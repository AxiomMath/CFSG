module

public import CFSG.LieType.Chevalley.RootCommutatorData

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps

@[expose] def oddDerivVecEq {n : ℕ} (u v : Fin n → ℤ) : Bool :=
  (List.finRange n).all fun j => u j == v j

theorem eq_of_oddDerivVecEq {n : ℕ} {u v : Fin n → ℤ} (h : oddDerivVecEq u v = true) : u = v :=
  funext fun j => eq_of_beq (List.all_eq_true.1 h j (List.mem_finRange j))

theorem oddDerivVecEq_self {n : ℕ} (u : Fin n → ℤ) : oddDerivVecEq u u = true :=
  List.all_eq_true.2 fun j _ => beq_self_eq_true (u j)

@[expose] def oddDerivMemB {n : ℕ} (v : Fin n → ℤ) (L : List (Fin n → ℤ)) : Bool :=
  L.any fun w => oddDerivVecEq w v

theorem mem_of_oddDerivMemB {n : ℕ} {v : Fin n → ℤ} {L : List (Fin n → ℤ)}
    (h : oddDerivMemB v L = true) : v ∈ L := by
  obtain ⟨w, hw, he⟩ := List.any_eq_true.1 h
  rwa [← eq_of_oddDerivVecEq he]

@[expose] def oddDerivHeight {n : ℕ} (v : Fin n → ℤ) : ℤ :=
  (List.ofFn v).sum

theorem oddDerivHeight_eq {τ : Tag} (v : Fin τ.rank → ℤ) : oddDerivHeight v = height v := by
  rw [oddDerivHeight, List.sum_ofFn]
  rfl

@[expose] def oddDerivMixedB {n : ℕ} (v : Fin n → ℤ) : Bool :=
  (List.finRange n).any (fun j => decide (0 < v j)) &&
    (List.finRange n).any fun j => decide (v j < 0)

@[expose] def oddDerivQuadTerms : Tag → List (ℕ × ℕ × ℤ)
  | .G2 => [(0, 0, 6), (0, 1, -6), (1, 1, 2)]
  | .F4 => [(0, 0, 4), (0, 1, -4), (1, 1, 4), (1, 2, -4), (2, 2, 2), (2, 3, -2), (3, 3, 2)]
  | .D4 => [(0, 0, 2), (0, 2, -2), (1, 1, 2), (1, 2, -2), (2, 2, 2), (2, 3, -2), (3, 3, 2)]
  | .E6 => [(0, 0, 2), (0, 2, -2), (1, 1, 2), (1, 3, -2), (2, 2, 2), (2, 3, -2), (3, 3, 2),
      (3, 4, -2), (4, 4, 2), (4, 5, -2), (5, 5, 2)]
  | .E7 => [(0, 0, 2), (0, 2, -2), (1, 1, 2), (1, 3, -2), (2, 2, 2), (2, 3, -2), (3, 3, 2),
      (3, 4, -2), (4, 4, 2), (4, 5, -2), (5, 5, 2), (5, 6, -2), (6, 6, 2)]
  | .E8 => [(0, 0, 2), (0, 2, -2), (1, 1, 2), (1, 3, -2), (2, 2, 2), (2, 3, -2), (3, 3, 2),
      (3, 4, -2), (4, 4, 2), (4, 5, -2), (5, 5, 2), (5, 6, -2), (6, 6, 2), (6, 7, -2), (7, 7, 2)]

@[expose] def oddDerivQuadList (τ : Tag) (l : List ℤ) : ℤ :=
  ((oddDerivQuadTerms τ).map fun t => t.2.2 * l.getD t.1 0 * l.getD t.2.1 0).sum

@[expose] def oddDerivQuad (τ : Tag) (v : Fin τ.rank → ℤ) : ℤ :=
  oddDerivQuadList τ (List.ofFn v)

@[expose] def oddDerivQuadValues : Tag → List ℤ
  | .G2 => [2, 6]
  | .F4 => [2, 4]
  | .D4 => [2]
  | .E6 => [2]
  | .E7 => [2]
  | .E8 => [2]

@[expose] def oddDerivMaxHeight : Tag → ℤ
  | .G2 => 5
  | .F4 => 11
  | .D4 => 5
  | .E6 => 11
  | .E7 => 17
  | .E8 => 29

@[expose] def oddDerivNotRootB (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  decide (oddDerivMaxHeight τ < oddDerivHeight v) ||
    decide (oddDerivHeight v < -oddDerivMaxHeight τ) || oddDerivMixedB v ||
    !(oddDerivQuadValues τ).contains (oddDerivQuad τ v) || !isRootB τ v

@[expose] def oddDerivCode : List ℤ → ℕ
  | [] => 0
  | x :: l => (x + 8).toNat + 16 * oddDerivCode l

@[expose] def oddDerivMemNat (n : ℕ) : List ℕ → Bool
  | [] => false
  | c :: l => Nat.beq c n || oddDerivMemNat n l

@[expose] def oddDerivIsRootB (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  (List.ofFn v).all (fun x => decide (-8 ≤ x) && decide (x ≤ 7)) &&
    oddDerivMemNat (oddDerivCode (List.ofFn v)) τ.rootCertificate.roots

@[expose] def oddDerivTailB (τ : Tag) (h : ℤ) (SA : List (Fin τ.rank → ℤ)) : Bool :=
  τ.rootCertificate.roots.all fun c =>
    !(decide (0 < oddDerivHeight (decodeVec (τ := τ) c)) &&
        decide (h ≤ oddDerivHeight (decodeVec (τ := τ) c))) ||
      oddDerivMemB (decodeVec c) SA

end CFSG.SeitzReduction
