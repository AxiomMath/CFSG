module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPAlt
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPComp
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPSL2
import CFSG.GroupTheory.SylowIntersectionControl.GomiFact37CSPThree

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin (commV fixV ffJ IsFFStarOffender IrrPlus BinaryNaturalSL FFModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

variable {W : Type} [CommGroup W] [Finite W]

private theorem gomiCSP_le_normalizer_of_offender (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact37Hyp Y S L) (hq : CFSG.IsQuasisimple ↥L)
    (hirr : commV L ∈ IrrPlus L ⊤)
    (hoff : ffJ S ≤ Subgroup.normalizer (L : Set (MulAut W)) →
      ∀ A : Subgroup (MulAut W), IsFFStarOffender S A → ⁅L, A⁆ ≠ ⊥ →
        ¬ commV L ⊓ fixV (ffJ S) ≤ gomiWXKer L) :
    gomiCSP S L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  refine gomiCSP_le_normalizer_of_not_le hW h hq hirr ?_
  by_cases hJ : ⁅L, ffJ S⁆ = ⊥
  · exact not_inf_fixV_ffJ_le_of_commutator_eq_bot hW hirr hJ
  · obtain ⟨A, hA, hLA⟩ := exists_isFFStarOffender_commutator_ne_bot hJ
    exact hoff (ffJ_le_normalizer_of_gomiFact37Hyp hW h hq) A hA hLA

theorem gomiCSP_le_normalizer (hW : ∀ w : W, w ^ 2 = 1) {Y S L : Subgroup (MulAut W)}
    (h : GomiFact37Hyp Y S L)
    (hnat : (∃ m : ℕ, 2 ≤ m ∧ IsSLn ↥L 2 m ∧ BinaryNaturalSL L (commV L) (gomiWXKer L) 2 m) ∨
      ∃ m : ℕ, 2 ≤ m ∧ IsAlt ↥L (2 * m - 1) ∧
        (FFModel.altDn (2 * m - 1)).Realizes L (commV L) (gomiWXKer L)) :
    gomiCSP S L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  have hS : IsPGroup 2 ↥S := h.2.1.2.1
  rcases hnat with ⟨m, hm, -, hsl⟩ | ⟨m, hm, hL, halt⟩
  · exact gomiCSP_le_normalizer_of_offender hW h (isQuasisimple_of_binaryNaturalSL hm hsl)
      (commV_mem_irrPlus_of_binaryNaturalSL hm hsl) fun hN _ hA hLA =>
        not_inf_fixV_ffJ_le_of_binaryNaturalSL hW hS hm hsl hN hA hLA
  obtain rfl | hm3 : m = 2 ∨ 3 ≤ m := by omega
  · exact gomiCSP_le_normalizer_of_isAlt_three hW h hL
  have hodd : Odd (2 * m - 1) := ⟨m - 1, by omega⟩
  have h5 : 5 ≤ 2 * m - 1 := by omega
  exact gomiCSP_le_normalizer_of_offender hW h (isQuasisimple_of_isAlt h5 hL)
    (commV_mem_irrPlus_of_altDn hodd h5 hL halt) fun hN _ hA hLA =>
      not_inf_fixV_ffJ_le_of_altDn hW hS hodd h5 hL halt hN hA hLA

theorem gomiFact37OneCSP_holds : GomiFact37OneCSP :=
  fun _ _ _ hW _ _ _ h _ hnat => gomiCSP_le_normalizer hW h hnat

end CFSG.GroupTheory

end
