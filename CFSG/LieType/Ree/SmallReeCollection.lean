module

public import CFSG.LieType.Ree.SmallReeCollectionCheck

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

@[expose] def smallReeRoot (i : Fin 6) : Fin Tag.G2.rank → ℤ :=
  ![![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3]] i

@[expose] def smallReeX
    (R : Type*) [CommRing R] (i : Fin 6) (c : R) :
    (Module.End R (RootModule Tag.G2 R))ˣ :=
  pinnedX Tag.G2 R (smallReeRoot i) c

@[expose] def smallReePos (i : Fin 6) : ℕ :=
  ![1, 0, 4, 8, 3, 7] i

theorem root_smallReePos (i : Fin 6) :
    Tag.G2.rootCertificate.root (smallReePos i) = smallReeRoot i := by
  revert i
  decide

@[expose] def smallReeLeft (i j : Fin 6) : List Factor :=
  [(0, 1, smallReePos j, 1), (1, 0, smallReePos i, 1)]

@[expose] def smallReeRight (i j : Fin 6) (cs : List Factor) : List Factor :=
  (1, 0, smallReePos i, 1) :: (0, 1, smallReePos j, 1) :: cs

theorem smallReeCheck_0_1
    : wordCheck Tag.G2 3 (smallReeLeft 0 1)
    (smallReeRight 0 1 [(1, 1, smallReePos 2, 1), (2, 1, smallReePos 3, 1),
      (3, 1, smallReePos 4, -1), (3, 2, smallReePos 5, -1)]) = true := by
  decide +kernel

theorem smallReeCheck_0_2 :
    wordCheck Tag.G2 3 (smallReeLeft 0 2) (smallReeRight 0 2 [(1, 1, smallReePos 3, -1)]) =
      true := by
  decide +kernel

theorem smallReeCheck_1_4 :
    wordCheck Tag.G2 3 (smallReeLeft 1 4) (smallReeRight 1 4 [(1, 1, smallReePos 5, -1)]) =
      true := by
  decide +kernel

theorem smallReeCheck_0_3 :
    wordCheck Tag.G2 3 (smallReeLeft 0 3) (smallReeRight 0 3 []) = true := by
  decide +kernel

theorem smallReeCheck_0_4 :
    wordCheck Tag.G2 3 (smallReeLeft 0 4) (smallReeRight 0 4 []) = true := by
  decide +kernel

theorem smallReeCheck_0_5 :
    wordCheck Tag.G2 3 (smallReeLeft 0 5) (smallReeRight 0 5 []) = true := by
  decide +kernel

theorem smallReeCheck_1_2 :
    wordCheck Tag.G2 3 (smallReeLeft 1 2) (smallReeRight 1 2 []) = true := by
  decide +kernel

theorem smallReeCheck_1_3 :
    wordCheck Tag.G2 3 (smallReeLeft 1 3) (smallReeRight 1 3 []) = true := by
  decide +kernel

theorem smallReeCheck_1_5 :
    wordCheck Tag.G2 3 (smallReeLeft 1 5) (smallReeRight 1 5 []) = true := by
  decide +kernel

theorem smallReeCheck_2_3 :
    wordCheck Tag.G2 3 (smallReeLeft 2 3) (smallReeRight 2 3 []) = true := by
  decide +kernel

theorem smallReeCheck_2_4 :
    wordCheck Tag.G2 3 (smallReeLeft 2 4) (smallReeRight 2 4 []) = true := by
  decide +kernel

theorem smallReeCheck_2_5 :
    wordCheck Tag.G2 3 (smallReeLeft 2 5) (smallReeRight 2 5 []) = true := by
  decide +kernel

theorem smallReeCheck_3_4 :
    wordCheck Tag.G2 3 (smallReeLeft 3 4) (smallReeRight 3 4 []) = true := by
  decide +kernel

theorem smallReeCheck_3_5 :
    wordCheck Tag.G2 3 (smallReeLeft 3 5) (smallReeRight 3 5 []) = true := by
  decide +kernel

theorem smallReeCheck_4_5 :
    wordCheck Tag.G2 3 (smallReeLeft 4 5) (smallReeRight 4 5 []) = true := by
  decide +kernel

@[expose] def smallReeCommPairs : List (Fin 6 × Fin 6) :=
  [(0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

theorem mem_smallReeCommPairs : ∀ i j : Fin 6, i < j → (i, j) ≠ (0, 1) → (i, j) ≠ (0, 2) →
    (i, j) ≠ (1, 4) → (i, j) ∈ smallReeCommPairs := by
  decide

theorem smallReeCheck_comm
    : ∀ p ∈ smallReeCommPairs,
    wordCheck Tag.G2 3 (smallReeLeft p.1 p.2) (smallReeRight p.1 p.2 []) = true := by
  simp only [smallReeCommPairs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
    implies_true, and_true]
  exact ⟨smallReeCheck_0_3, smallReeCheck_0_4, smallReeCheck_0_5, smallReeCheck_1_2,
    smallReeCheck_1_3, smallReeCheck_1_5, smallReeCheck_2_3, smallReeCheck_2_4, smallReeCheck_2_5,
    smallReeCheck_3_4, smallReeCheck_3_5, smallReeCheck_4_5⟩

section Identities

variable {R : Type*} [CommRing R]

theorem factorPinned_smallReeLeft
    (i j : Fin 6) (x y : R) :
    factorPinned Tag.G2 R (smallReeLeft i j) x y = smallReeX R j y * smallReeX R i x := by
  simp only [smallReeLeft, factorPinned_cons, factorPinned_nil, mul_one, Int.cast_one, one_mul,
    pow_zero, pow_one, root_smallReePos, smallReeX]

theorem factorPinned_smallReeRight
    (i j : Fin 6) (cs : List Factor) (x y : R) :
    factorPinned Tag.G2 R (smallReeRight i j cs) x y =
      smallReeX R i x * smallReeX R j y * factorPinned Tag.G2 R cs x y := by
  simp only [smallReeRight, factorPinned_cons, Int.cast_one, one_mul, pow_zero, pow_one, mul_one,
    root_smallReePos, smallReeX, mul_assoc]

theorem small_Ree_collection_of_three_eq_zero
    (h3 : (3 : R) = 0) (x y : R) :
    smallReeX R 1 y * smallReeX R 0 x =
        smallReeX R 0 x * smallReeX R 1 y * smallReeX R 2 (x * y) * smallReeX R 3 (x ^ 2 * y) *
          smallReeX R 4 (-(x ^ 3 * y)) * smallReeX R 5 (-(x ^ 3 * y ^ 2)) ∧
      smallReeX R 2 y * smallReeX R 0 x =
        smallReeX R 0 x * smallReeX R 2 y * smallReeX R 3 (-(x * y)) ∧
      smallReeX R 4 y * smallReeX R 1 x =
        smallReeX R 1 x * smallReeX R 4 y * smallReeX R 5 (-(x * y)) ∧
      ∀ i j : Fin 6, i < j → (i, j) ≠ (0, 1) → (i, j) ≠ (0, 2) → (i, j) ≠ (1, 4) →
        smallReeX R j y * smallReeX R i x = smallReeX R i x * smallReeX R j y := by
  have hn : ((3 : ℕ) : R) = 0 := by exact_mod_cast h3
  have key : ∀ (i j : Fin 6) (cs : List Factor),
      wordCheck Tag.G2 3 (smallReeLeft i j) (smallReeRight i j cs) = true →
        smallReeX R j y * smallReeX R i x =
          smallReeX R i x * smallReeX R j y * factorPinned Tag.G2 R cs x y := by
    intro i j cs h
    rw [← factorPinned_smallReeLeft, ← factorPinned_smallReeRight]
    exact factorPinned_eq_of_wordCheck h R hn x y
  refine ⟨?_, ?_, ?_, fun i j hij h1 h2 h3' => ?_⟩
  · rw [key 0 1 _ smallReeCheck_0_1]
    simp only [factorPinned_cons, factorPinned_nil, root_smallReePos, Int.cast_one, Int.cast_neg,
      one_mul, neg_mul, pow_one, mul_one, mul_assoc, smallReeX]
  · rw [key 0 2 _ smallReeCheck_0_2]
    simp only [factorPinned_cons, factorPinned_nil, root_smallReePos, Int.cast_one, Int.cast_neg,
      one_mul, neg_mul, pow_one, mul_one, mul_assoc, smallReeX]
  · rw [key 1 4 _ smallReeCheck_1_4]
    simp only [factorPinned_cons, factorPinned_nil, root_smallReePos, Int.cast_one, Int.cast_neg,
      one_mul, neg_mul, pow_one, mul_one, mul_assoc, smallReeX]
  · rw [key i j [] (smallReeCheck_comm (i, j) (mem_smallReeCommPairs i j hij h1 h2 h3')),
      factorPinned_nil, mul_one]

end Identities

theorem small_Ree_positive_root_collection_identities
    (R : Type*) [CommRing R] [CharP R 3]
    (x y : R) :
    smallReeX R 1 y * smallReeX R 0 x =
        smallReeX R 0 x * smallReeX R 1 y * smallReeX R 2 (x * y) * smallReeX R 3 (x ^ 2 * y) *
          smallReeX R 4 (-(x ^ 3 * y)) * smallReeX R 5 (-(x ^ 3 * y ^ 2)) ∧
      smallReeX R 2 y * smallReeX R 0 x =
        smallReeX R 0 x * smallReeX R 2 y * smallReeX R 3 (-(x * y)) ∧
      smallReeX R 4 y * smallReeX R 1 x =
        smallReeX R 1 x * smallReeX R 4 y * smallReeX R 5 (-(x * y)) ∧
      ∀ i j : Fin 6, i < j → (i, j) ≠ (0, 1) → (i, j) ≠ (0, 2) → (i, j) ≠ (1, 4) →
        smallReeX R j y * smallReeX R i x = smallReeX R i x * smallReeX R j y :=
  small_Ree_collection_of_three_eq_zero (by exact_mod_cast CharP.cast_eq_zero R 3) x y

end CFSG.LieType.Ree
