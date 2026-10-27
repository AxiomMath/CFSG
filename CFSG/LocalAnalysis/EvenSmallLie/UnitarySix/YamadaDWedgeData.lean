module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParF2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev WCol (n : ℕ) := Fin n × Fin n × Fin n

abbrev WRow (n m : ℕ) := (Fin m × Fin n × Fin n × Fin n) ⊕ (Fin n × Fin n × Fin n)

@[expose] def wedgeEqP {n m : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (WRow n m) (WCol n) (ZMod 2) := fun ρ c =>
  match ρ with
  | .inl (g, i, j, r) =>
    (if c.2.2 = r then M g c.1 i * M g c.2.1 j else 0) +
      (if c.1 = i ∧ c.2.1 = j then M g r c.2.2 else 0)
  | .inr (k, l, s) =>
    if c.2.2 = s ∧ ((c.1 = k ∧ c.2.1 = l) ∨ (c.1 = l ∧ c.2.1 = k)) then 1 else 0

@[expose] def eCol (n : ℕ) : WCol n ≃ Fin (n * (n * n)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

@[expose] def eRow (n m : ℕ) : WRow n m ≃ Fin (m * (n * (n * n)) + n * (n * n)) :=
  (Equiv.sumCongr ((Equiv.prodCongr (Equiv.refl (Fin m)) (eCol n)).trans finProdFinEquiv)
    (eCol n)).trans finSumFinEquiv

@[expose] def wedgeEq {n m : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Fin (m * (n * (n * n)) + n * (n * n))) (Fin (n * (n * n))) (ZMod 2) :=
  (wedgeEqP M).reindex (eRow n m) (eCol n)

@[expose] def wedgeR {n m : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)) : Array ℕ :=
  matBits _ _ (wedgeEq M)

@[expose] def leftInvF2 (w : ℕ) (R : Array ℕ) : Array ℕ := Id.run do
  let n := R.size
  let mut vals : Array ℕ := R
  let mut tags : Array ℕ := Array.ofFn (n := n) fun i => 2 ^ i.val
  let mut used : Array Bool := Array.replicate n false
  let mut piv : Array ℕ := Array.replicate w 0
  for u in [0:w] do
    let mut p := n
    for i in [0:n] do
      if p == n && !(used.getD i true) && (vals.getD i 0).testBit u then
        p := i
    if p < n then
      used := used.set! p true
      piv := piv.set! u p
      let vp := vals.getD p 0
      let tp := tags.getD p 0
      for i in [0:n] do
        if i != p && (vals.getD i 0).testBit u then
          vals := vals.set! i (vals.getD i 0 ^^^ vp)
          tags := tags.set! i (tags.getD i 0 ^^^ tp)
  return Array.ofFn (n := w) fun u => tags.getD (piv.getD u.val 0) 0

@[expose] def wedgeCheckGen (n m : ℕ) (M : Fin m → Matrix (Fin n) (Fin n) (ZMod 2)) : Bool :=
  bIsId (n * (n * n)) (bmul (n * (n * n)) (m * (n * (n * n)) + n * (n * n))
    (leftInvF2 (n * (n * n)) (wedgeR M)) (wedgeR M))

@[expose] def wedgeGensN : Array (Array ℕ) :=
  #[#[1, 2, 5, 10, 16, 32, 80, 160], #[1, 2, 6, 11, 16, 32, 112, 144],
    #[1, 2, 4, 8, 20, 40, 64, 128], #[4, 8, 1, 2, 64, 128, 16, 32],
    #[1, 2, 16, 32, 4, 8, 64, 128]]

@[expose] def wedgeMatN (g : Fin 5) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  toMat 8 8 (wedgeGensN.getD g #[])

@[expose] def wedgeCheckN : Bool := wedgeCheckGen 8 5 wedgeMatN

@[expose] def wedgeGensW : Array (Array ℕ) := #[#[1, 3, 4, 13], #[1, 2, 5, 11], #[8, 6, 4, 1]]

@[expose] def wedgeMatW (g : Fin 3) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  toMat 4 4 (wedgeGensW.getD g #[])

@[expose] def wedgeCheckW : Bool := wedgeCheckGen 4 3 wedgeMatW

end CFSG.EvenSmallLie.UnitarySix.YamadaD
