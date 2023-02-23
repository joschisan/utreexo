#![allow(dead_code, unused_variables)]

use arrayvec;
use blake;

type Hash = [u8; 32];

#[derive(Clone, PartialEq, Eq, Debug)]
enum Direction {
    Left,
    Right,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct Leaf {
    hash: Hash,
    path: arrayvec::ArrayVec<Direction, 31>,
    proof: arrayvec::ArrayVec<Hash, 31>,
}

impl Leaf {
    fn new(hash: Hash) -> Self {
        Leaf {
            hash,
            path: Default::default(),
            proof: Default::default(),
        }
    }

    fn extension(&self) -> Node {
        let get_parent = |delete, (direction, sibling)| {
            let sibling = Node::sibling(sibling);

            match direction {
                Direction::Left => Node::branch(delete, sibling, false),
                Direction::Right => Node::branch(sibling, delete, false),
            }
        };

        let delete = Node::delete(self.hash);

        std::iter::zip(self.path.clone(), self.proof.clone()).fold(delete, get_parent)
    }
}

fn parent_hash(left: &Hash, right: &Hash) -> Hash {
    let mut hash = [0; 32];
    let mut state = blake::Blake::new(256).unwrap();

    state.update(left);
    state.update(right);

    state.finalise(&mut hash);

    hash
}

#[derive(Debug)]
struct Node {
    hash: Hash,
    children: Option<Box<(Node, Node)>>,
    cache: bool,
    delete: bool,
    proof: bool,
}

impl Node {
    fn branch(left: Node, right: Node, cache: bool) -> Self {
        Self {
            hash: parent_hash(&left.hash, &right.hash),
            cache,
            delete: left.delete || right.delete,
            proof: left.proof || right.proof,
            children: if cache || left.delete || right.delete || left.proof || right.proof {
                Some(Box::new((left, right)))
            } else {
                None
            },
        }
    }

    fn delete(hash: Hash) -> Node {
        Node {
            hash,
            children: None,
            cache: false,
            delete: true,
            proof: false,
        }
    }
    fn proof(hash: Hash) -> Node {
        Node {
            hash,
            children: None,
            cache: false,
            delete: false,
            proof: true,
        }
    }
    fn sibling(hash: Hash) -> Node {
        Node {
            hash,
            children: None,
            cache: false,
            delete: false,
            proof: false,
        }
    }

    fn verify(&self) {
        if let Some((left, right)) = self.children.as_deref() {
            assert!(self.hash == parent_hash(&left.hash, &right.hash));
            assert!(self.cache || self.proof || self.delete);
            assert!(left.cache == right.cache);
            assert!(self.delete == left.delete || right.delete);
            assert!(self.proof == left.proof || right.proof);

            left.verify();
            right.verify();
        } else {
            assert!(!self.cache);
        }
    }

    fn update(&mut self) {
        let (left, right) = self.children.as_deref().expect("called update on a leaf");
        self.hash = parent_hash(&left.hash, &right.hash);
        self.delete = left.delete || right.delete;
        self.proof = left.proof || right.proof;

        if !self.cache && !self.delete && !self.proof {
            self.children = None;
        }
    }

    fn extend(&mut self, mut leaf: Leaf) -> Option<Leaf> {
        if leaf.path.len() == 0 {
            if self.hash != leaf.hash {
                return None;
            }

            self.delete = true;

            leaf.proof.clear();

            return Some(leaf);
        }

        if self.children.is_none() {
            let extension = leaf.extension();

            if self.hash != extension.hash {
                return None;
            }

            *self = extension;

            leaf.proof.truncate(leaf.path.len());

            return Some(leaf);
        };

        let (left, right) = self.children.as_deref_mut().unwrap();

        match leaf.path.pop().unwrap() {
            Direction::Left => {
                let mut leaf = left.extend(leaf)?;
                leaf.path.push(Direction::Left);
                leaf.proof.push(right.hash);
                self.delete = true;
                Some(leaf)
            }
            Direction::Right => {
                let mut leaf = right.extend(leaf)?;
                leaf.path.push(Direction::Right);
                leaf.proof.push(left.hash);
                self.delete = true;
                Some(leaf)
            }
        }
    }

    fn replace(&mut self, depth: usize, src: Node) -> Node {
        assert!(self.delete);

        if depth == 0 {
            return std::mem::replace(self, src);
        }

        let (left, right) = self.children.as_deref_mut().unwrap();

        if left.delete {
            let replaced = left.replace(depth - 1, src);
            self.update();
            replaced
        } else {
            let replaced = right.replace(depth - 1, src);
            self.update();
            replaced
        }
    }

    fn split(self, roots: &mut [Option<Node>; 32]) -> usize {
        assert!(self.delete);

        if self.children.is_none() {
            return 0;
        }

        let (left, right) = *self.children.unwrap();

        if left.delete {
            let n_roots = left.split(roots);
            assert!(roots[n_roots].is_none());
            roots[n_roots] = Some(right);
            n_roots + 1
        } else {
            let n_roots = right.split(roots);
            roots[n_roots] = Some(left);
            n_roots + 1
        }
    }

    fn proove(&self, hash: Hash) -> Option<Leaf> {
        if !self.proof {
            return None;
        }

        if self.hash == hash && self.children.is_none() {
            return Some(Leaf::new(hash));
        }

        let (left, right) = self.children.as_deref()?;

        if let Some(mut leaf) = left.proove(hash) {
            leaf.path.push(Direction::Left);
            leaf.proof.push(right.hash);
            return Some(leaf);
        }

        if let Some(mut leaf) = right.proove(hash) {
            leaf.path.push(Direction::Right);
            leaf.proof.push(left.hash);
            return Some(leaf);
        }

        None
    }

    fn prune(&mut self) {
        if !self.delete {
            return;
        }

        self.delete = false;

        if !self.cache && !self.proof {
            self.children = None;
            return;
        }

        let (left, right) = self.children.as_deref_mut().unwrap();

        left.prune();
        right.prune();
    }

    fn increase_proof_limit(&mut self) {
        assert!(!self.delete);

        let (left, right) = self.children.as_deref_mut().unwrap();

        if left.cache && right.cache {
            left.increase_proof_limit();
            right.increase_proof_limit();
        } else {
            self.children = None;
        }
    }
}

struct Accumulator {
    roots: [Option<Node>; 32],
    proof_limit: usize,
}

impl Accumulator {
    fn empty(proof_limit: usize) -> Self {
        Self {
            roots: Default::default(),
            proof_limit,
        }
    }

    fn verify(&self) {
        self.roots
            .iter()
            .filter_map(|r| r.as_ref())
            .for_each(|r| r.verify())
    }

    fn update(&mut self, deletions: Vec<Leaf>, additions: Vec<(Hash, bool)>) -> Option<Vec<Leaf>> {
        let proofs: Option<Vec<Leaf>> = deletions
            .into_iter()
            .map(|leaf| self.roots[leaf.path.len()].as_mut()?.extend(leaf))
            .collect();

        if proofs.is_none() {
            self.roots
                .iter_mut()
                .filter_map(|r| r.as_mut())
                .for_each(|r| r.prune());

            return None;
        }

        loop {
            let height_replace = self
                .roots
                .iter()
                .position(|r| r.is_some() && r.as_ref().unwrap().delete);

            if height_replace.is_none() {
                break;
            }

            let height_replace = height_replace.unwrap();
            let height_min = self.roots.iter().position(|r| r.is_some()).unwrap();
            let root_min = self.roots[height_min].take().unwrap();

            let n_roots = if height_replace == height_min {
                root_min.split(&mut self.roots)
            } else {
                self.roots[height_replace]
                    .as_mut()
                    .unwrap()
                    .replace(height_replace - height_min, root_min)
                    .split(&mut self.roots)
            };

            assert!(n_roots == height_min);
        }

        for (hash, proof) in additions {
            let mut root = if proof {
                Node::proof(hash)
            } else {
                Node::sibling(hash)
            };

            let mut height = 0;

            for sibling in self.roots.iter_mut().map_while(|r| r.take()) {
                root = Node::branch(root, sibling, height >= self.proof_limit);
                height += 1;
            }

            self.roots[height] = Some(root);
        }

        proofs
    }

    fn proove(&self, hash: Hash) -> Option<Leaf> {
        self.roots
            .iter()
            .filter_map(|r| r.as_ref())
            .find_map(|r| r.proove(hash))
    }

    fn increase_proof_limit(&mut self) {
        self.roots
            .iter_mut()
            .filter_map(|r| r.as_mut())
            .for_each(|r| r.increase_proof_limit());
        self.proof_limit += 1;
    }
}

#[cfg(test)]
mod tests {
    use fastrand;
    fn random_hash() -> super::Hash {
        [0; 32].map(|x| fastrand::u8(..))
    }

    #[test]
    fn proof() {
        let mut accumulator_a = super::Accumulator::empty(5);
        let mut accumulator_b = super::Accumulator::empty(5);

        let utxos: Vec<super::Hash> = (0..128000).map(|_| random_hash()).collect();

        let utxos_a: Vec<(super::Hash, bool)> = utxos
            .clone()
            .into_iter()
            .map(|hash| (hash, hash[0] == 0))
            .collect();

        let utxos_b: Vec<(super::Hash, bool)> = utxos
            .clone()
            .into_iter()
            .map(|hash| (hash, hash[0] == 1))
            .collect();

        accumulator_a.update(vec![], utxos_a).unwrap();
        accumulator_b.update(vec![], utxos_b).unwrap();

        let mut utxo_set: Vec<super::Hash> = utxos
            .into_iter()
            .filter(|hash| hash[0] == 0 || hash[0] == 1)
            .collect();

        for _ in 0..10 {
            fastrand::shuffle(&mut utxo_set);

            let stxos: Vec<super::Leaf> = utxo_set
                .split_off(utxo_set.len() - 100)
                .into_iter()
                .map(|hash| {
                    if hash[0] == 0 {
                        accumulator_a.proove(hash).unwrap()
                    } else {
                        accumulator_b.proove(hash).unwrap()
                    }
                })
                .collect();

            let stxos_truncated: Vec<super::Leaf> = stxos
                .clone()
                .into_iter()
                .map(|mut leaf| {
                    leaf.proof.truncate(5);
                    leaf
                })
                .collect();

            let utxos: Vec<super::Hash> = (0..12800).map(|_| random_hash()).collect();

            let utxos_a: Vec<(super::Hash, bool)> = utxos
                .clone()
                .into_iter()
                .map(|hash| (hash, hash[0] == 0))
                .collect();

            let utxos_b: Vec<(super::Hash, bool)> = utxos
                .clone()
                .into_iter()
                .map(|hash| (hash, hash[0] == 1))
                .collect();

            let stxos_a = accumulator_a
                .update(stxos_truncated.clone(), utxos_a)
                .unwrap();
            let stxos_b = accumulator_b
                .update(stxos_truncated.clone(), utxos_b)
                .unwrap();

            assert!(stxos_a == stxos);
            assert!(stxos_b == stxos);

            accumulator_a.verify();
            accumulator_b.verify();

            for hash in utxos
                .into_iter()
                .filter(|hash| hash[0] == 0 || hash[0] == 1)
            {
                utxo_set.push(hash)
            }
        }
    }
}
