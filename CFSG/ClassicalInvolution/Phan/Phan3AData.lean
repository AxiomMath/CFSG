module

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

@[expose] def decodeLetter (n c : Nat) : Option (Fin n × Bool) :=
  if h : c / 2 < n then some (⟨c / 2, h⟩, decide (c % 2 = 0)) else none

@[expose] def decodeWord (n : Nat) (w : List Nat) : List (Fin n × Bool) :=
  w.filterMap (decodeLetter n)

@[expose] def su3Codes : List (List Nat) :=
  [[6, 6, 6], [0, 0, 0, 0], [0, 4, 1, 5], [0, 5, 3, 4, 3], [0, 6, 1, 6, 5], [2, 6, 3, 6, 2, 7]]

@[expose] def su3Rels : List (List (Fin 4 × Bool)) := su3Codes.map (decodeWord 4)

@[expose] def shiftLetter (s : Nat) (hs : 4 + s ≤ 6) (l : Fin 4 × Bool) : Fin 6 × Bool :=
  (⟨l.1.val + s, by have := l.1.isLt; omega⟩, l.2)

@[expose] def phanA3CommRels : List (List (Fin 6 × Bool)) :=
  [[(0, true), (4, true), (0, false), (4, false)], [(0, true), (5, true), (0, false), (5, false)],
   [(1, true), (4, true), (1, false), (4, false)], [(1, true), (5, true), (1, false), (5, false)]]

@[expose] def phanA3Rels : List (List (Fin 6 × Bool)) :=
  su3Rels.map (List.map (shiftLetter 0 (by decide))) ++
    su3Rels.map (List.map (shiftLetter 2 (by decide))) ++ phanA3CommRels

@[expose] def phanA3U1 : List (Fin 6 × Bool) :=
  decodeWord 6 [4, 2, 6, 1, 3, 10, 6, 10, 4, 2, 6, 1, 3, 10, 6, 10]

@[expose] def phanA3U2 : List (Fin 6 × Bool) :=
  decodeWord 6 [4, 7, 1, 2, 7, 5, 11, 6, 2, 6, 0, 0, 11, 6, 2, 6, 11]

@[expose] def invWord {n : Nat} (w : List (Fin n × Bool)) : List (Fin n × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def powWord {n : Nat} (u : List (Fin n × Bool)) : Int → List (Fin n × Bool)
  | (k : Nat) => (List.replicate k u).flatten
  | Int.negSucc k => (List.replicate (k + 1) (invWord u)).flatten

@[expose] def phanA3Exps : List (Int × Int) :=
  (List.range 5).flatMap fun (a : Nat) => (List.range 5).filterMap fun (b : Nat) =>
    if a = 2 ∧ b = 2 then none else some ((a : Int) - 2, (b : Int) - 2)

@[expose] def phanA3KernelWords : List (List (Fin 6 × Bool) × Nat) :=
  phanA3Exps.map fun ij => (powWord phanA3U1 ij.1 ++ powWord phanA3U2 ij.2, 3)

end CFSG.ClassicalInvolution.Phan.Q3G
