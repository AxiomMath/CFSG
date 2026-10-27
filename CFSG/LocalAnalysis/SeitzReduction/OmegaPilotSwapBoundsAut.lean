module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapPair
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancingLocal.EvenOrthogonalComponents
  (conj_injective_matrixProjectiveDerived)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (exists_outer_two_part_le)

section Centreless

variable {P : Type*} [Group P] [Finite P]

omit [Finite P] in
theorem card_mulAut_eq_of_conj_injective
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) :
    Nat.card (MulAut P) = Nat.card P * Nat.card (Outer P) := by
  have h1 : Nat.card P = Nat.card (inner P) :=
    Nat.card_congr (MonoidHom.ofInjective hcj).toEquiv
  rw [h1, ← (inner P).card_mul_index]
  rfl

theorem factorization_two_card_mulAut_le
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) {f : ℕ}
    (hout : ordProj[2] (Nat.card (Outer P)) ≤ 2 * ordProj[2] f) :
    (Nat.card (MulAut P)).factorization 2 ≤
      (Nat.card P).factorization 2 + 1 + f.factorization 2 := by
  have : Finite (MulAut P) := MulEquiv.finite_left
  rw [card_mulAut_eq_of_conj_injective hcj,
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply]
  have h2 : 2 ^ (Nat.card (Outer P)).factorization 2 ≤ 2 ^ (1 + f.factorization 2) := by
    rw [pow_add, pow_one]
    exact hout
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

end Centreless

section Coordinate

variable {K : Type} [Field K] [Finite K]

theorem statedClassicalModel_coordinatePlus {n f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) :
    StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n 2 f :=
  ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK,
    ⟨(coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm⟩⟩

theorem statedClassicalModel_coordinateMinus {n f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) (h1 : 1 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n K h1 b c))
      .POmegaMinus n 2 f :=
  ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
    ⟨(coordinateMinusWitnessEquiv K h1 b c (MulEquiv.refl _)).symm⟩⟩

omit [Finite K] in
theorem conj_injective_coordinatePlus [CharP K 2] {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) :=
  conj_injective_matrixProjectiveDerived
    (regular_coordinateQuadPlus n K hn).1 (regular_coordinateQuadPlus n K hn).2
    (commutator_coordinateQuadPlus n K hn)

theorem conj_injective_coordinateMinus [CharP K 2] {n : ℕ} (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (MulAut.conj :
      matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c) →*
        MulAut (matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))) :=
  conj_injective_matrixProjectiveDerived
    (regular_coordinateQuadMinus n K b c hn hirr).1 (regular_coordinateQuadMinus n K b c hn hirr).2
    (commutator_coordinateQuadMinus n K b c hn hirr)

theorem factorization_two_card_mulAut_coordinatePlus {n f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n) :
    (Nat.card (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))).factorization 2 ≤
      f * (n * (n - 1)) + 1 + f.factorization 2 := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have h := statedClassicalModel_coordinatePlus hf hK (by omega : 4 ≤ n)
  obtain ⟨k, hk2, -, -, hk1⟩ := exists_outer_two_part_le _ .POmegaPlus (Or.inr (Or.inl rfl)) n 2 f h
  have hk : k = 1 := hk1 fun h' => by omega
  subst hk
  have hout := hk2 rfl
  rw [mul_one] at hout
  have := factorization_two_card_mulAut_le (conj_injective_coordinatePlus (K := K)
    (by omega : 3 ≤ n)) hout
  rwa [card_coordinatePlus hf hK (by omega), factorization_two_ordD hf (by omega)] at this

theorem factorization_two_card_mulAut_coordinateMinus {n f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card (MulAut (matrixProjectiveDerived
      (coordinateQuadMinus n K (by omega) b c)))).factorization 2 ≤
      f * (n * (n - 1)) + 1 + f.factorization 2 := by
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  have h := statedClassicalModel_coordinateMinus hf hK hn (by omega) hirr
  obtain ⟨k, hk2, -, -, hk1⟩ :=
    exists_outer_two_part_le _ .POmegaMinus (Or.inr (Or.inr rfl)) n 2 f h
  have hk : k = 1 := hk1 fun h' => by cases h'.1
  subst hk
  have hout := hk2 rfl
  rw [mul_one] at hout
  have := factorization_two_card_mulAut_le (conj_injective_coordinateMinus (K := K) hn hirr) hout
  rwa [card_coordinateMinus hf hK hn (by omega) hirr, factorization_two_ordTwistedD hf (by omega)]
    at this

end Coordinate

end CFSG.SeitzReduction.OmegaPilot
