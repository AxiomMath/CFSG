module

public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.RegularCharacterDegreeSquareSum
import CFSG.FeitThompson.Representations.ConjugacyClassSumScalar
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInducedSupportBasis

variable {L : Type*} [Group L]

theorem leftRegular_character_mem_classFun :
    (Representation.leftRegular ℂ L).character ∈ classFun L :=
  mem_classFun.2 fun _ _ h => (char_eq_of_isConj _ h).symm

theorem leftRegular_character_mem_classFunSupportedOn [Finite L] (H : Subgroup L) :
    (Representation.leftRegular ℂ L).character ∈ classFunSupportedOn H :=
  mem_classFunSupportedOn.2 ⟨leftRegular_character_mem_classFun, fun _ hl =>
    leftRegular_character_of_ne_one fun h => hl (h ▸ H.one_mem)⟩

variable [Fintype L]

theorem cfInner_leftRegular_character_of_mem_indFam (H : Subgroup L) {ξ : L → ℂ}
    (hξ : ξ ∈ indFam H (Irr H)) :
    cfInner (Representation.leftRegular ℂ L).character ξ = ξ 1 := by
  obtain ⟨d, -, -, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_indFam H hξ
  rw [cfInner_leftRegular_character, hd, Complex.conj_natCast]

theorem leftRegular_character_eq_sum_indFam (H : Subgroup L) [H.Normal]
    [Fintype (indFam H (Irr H))] :
    (Representation.leftRegular ℂ L).character
      = ∑ ξ : indFam H (Irr H),
        ((ξ : L → ℂ) 1 / cfInner (ξ : L → ℂ) (ξ : L → ℂ)) • (ξ : L → ℂ) := by
  refine (coe_eq_sum_cfInner_div_smul H
    ⟨_, leftRegular_character_mem_classFunSupportedOn (L := L) H⟩).trans
    (Finset.sum_congr rfl fun ξ _ => ?_)
  rw [cfInner_leftRegular_character_of_mem_indFam H ξ.2]

theorem eq_sum_indFam_of_apply_one_of_apply_ne_one (H : Subgroup L) [H.Normal]
    [Fintype (indFam H (Irr H))] {r : L → ℂ} (h1 : r 1 = (Nat.card L : ℂ))
    (h0 : ∀ l : L, l ≠ 1 → r l = 0) :
    r = ∑ ξ : indFam H (Irr H),
      ((ξ : L → ℂ) 1 / cfInner (ξ : L → ℂ) (ξ : L → ℂ)) • (ξ : L → ℂ) := by
  have hr : r = (Representation.leftRegular ℂ L).character := by
    funext l
    by_cases hl : l = 1
    · rw [hl, h1, leftRegular_character_one]
    · rw [h0 l hl, leftRegular_character_of_ne_one hl]
  rw [hr, leftRegular_character_eq_sum_indFam H]

theorem exists_leftRegular_character_eq_sum_indFam (H : Subgroup L) [H.Normal]
    [Fintype (indFam H (Irr H))] :
    ∃ n : indFam H (Irr H) → ℕ, (∀ ξ, 0 < n ξ) ∧
      (∀ ξ : indFam H (Irr H), cfInner (ξ : L → ℂ) (ξ : L → ℂ) = (n ξ : ℂ)) ∧
      (Representation.leftRegular ℂ L).character
        = ∑ ξ : indFam H (Irr H), ((ξ : L → ℂ) 1 / (n ξ : ℂ)) • (ξ : L → ℂ) := by
  choose n hn hne using fun ξ : indFam H (Irr H) =>
    exists_cfInner_self_eq_of_mem_indFam H ξ.2
  refine ⟨n, hn, hne, (leftRegular_character_eq_sum_indFam H).trans
    (Finset.sum_congr rfl fun ξ _ => by rw [hne ξ])⟩

end CFSG.FeitThompson
