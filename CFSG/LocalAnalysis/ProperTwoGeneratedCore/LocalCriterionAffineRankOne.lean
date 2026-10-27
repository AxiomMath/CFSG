module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneCoordinates
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionAffineRankOneSolvable
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne

open BenderSuzuki.PFchapter1section1

universe u v

theorem rank_one_primitive_odd_affine_core
    {F : Type u} [Group F] [Finite F]
    {Λ : Type v} [MulAction F Λ] [Finite Λ]
    [MulAction.IsPretransitive F Λ] [FaithfulSMul F Λ]
    (heven : Even (Nat.card F)) (hrank : ¬ TwoRankAtLeastTwo F)
    (hdegree : 3 ≤ Nat.card Λ) (a : Λ)
    (hmax : IsCoatom (MulAction.stabilizer F a)) :
    CFSG.oddCore F ≠ ⊥ ∧
      ∃ (ℓ : ℕ) (Q : Subgroup F) (hQnormal : Q.Normal),
        let : Q.Normal := hQnormal
        ℓ.Prime ∧ Odd ℓ ∧ Q ≠ ⊥ ∧ Q ≤ CFSG.oddCore F ∧
        IsElementaryAbelian ℓ Q ∧
        Q.IsComplement' (MulAction.stabilizer F a) ∧
        Q ⊔ MulAction.stabilizer F a = ⊤ ∧
        Q ⊓ MulAction.stabilizer F a = ⊥ ∧
        MulAction.stabilizer F a ⊓ Subgroup.centralizer (Q : Set F) = ⊥ ∧
        (∀ x y : Λ, ∃! q : Q, q • x = y) ∧
        Nonempty (Q ⋊[(Q.normalizerMonoidHom).comp
          (Subgroup.inclusion (Q.normalizer_eq_top ▸ le_top))]
          (MulAction.stabilizer F a) ≃* F) ∧
        ∃ n : ℕ, 0 < n ∧ Nat.card Λ = Nat.card Q ∧ Nat.card Λ = ℓ ^ n ∧
          Odd (Nat.card Λ) ∧ IsPrimePow (Nat.card Λ) := by
  have hRne := odd_core_nontrivial_of_rank_one_primitive heven hrank hdegree a hmax
  have hRodd := odd_core_card_odd F
  have hRsolvable : Group.IsSolvable (CFSG.oddCore F) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard (CFSG.oddCore F) hRodd
  obtain ⟨ℓ, Q, hℓ, hQne, hQnormal, hQR, hQelementary,
    hcompl, hprod, hinter, hcentralizer, hregular⟩ :=
    solvable_normal_primitive_regular_subgroup (by omega) a hmax
      (CFSG.oddCore F) inferInstance hRne hRsolvable
  let : Q.Normal := hQnormal
  let : IsElementaryAbelian ℓ Q := hQelementary
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hQodd : Odd (Nat.card Q) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hQR)
  have hℓdvd : ℓ ∣ Nat.card Q := by
    rcases (IsElementaryAbelian.isPGroup ℓ Q).card_eq_or_dvd with hcard | hdvd
    · exact (hQne ((Subgroup.eq_bot_iff_card Q).mpr hcard)).elim
    · exact hdvd
  have hℓodd : Odd ℓ := hQodd.of_dvd_nat hℓdvd
  obtain ⟨n, hn, hcard, hpower⟩ :=
    regular_elementary_degree ℓ hℓ Q hregular a (by omega)
  have hdegreeodd : Odd (Nat.card Λ) := by
    rw [hcard]
    exact hQodd
  have hprimepower : IsPrimePow (Nat.card Λ) :=
    (isPrimePow_nat_iff _).mpr ⟨ℓ, n, hℓ, hn, hpower.symm⟩
  exact ⟨hRne, ℓ, Q, hQnormal, hℓ, hℓodd, hQne, hQR, hQelementary,
    hcompl, hprod, hinter, hcentralizer, hregular,
    ⟨normal_complement_semidirect_equiv Q (MulAction.stabilizer F a) hcompl⟩,
    n, hn, hcard, hpower, hdegreeodd, hprimepower⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionAffineRankOne
