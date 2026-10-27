module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveExTwoPart

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace FiveEx

theorem eq_zero_of_lieModel_exc {X : Type} [Group X] {t : StatedLieTag} {m p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : LieModel X t m p f) : m = 0 := by
  rcases h with ⟨hc, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact absurd hc (by revert ht; cases t <;> decide)
  all_goals exact h0

theorem four_dvd_five_pow_sub_one (f : ℕ) : 2 ^ 2 ∣ 5 ^ f - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow 5 1 f

end FiveEx

theorem oddFiveSL2BoundFamilyInput_of_twoPart {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) (h : ∀ f, ExcTwoPartInput t 5 f 5) :
    OddFiveSL2BoundFamilyInput t := by
  intro J _ _ _ _ m f _ hJm τ hτ
  obtain rfl := FiveEx.eq_zero_of_lieModel_exc ht hJm
  exact absurd (h f J hJm τ hτ.1) (fiveA5Group_of_catSL2Hyp hτ).not_dvd

section Families

theorem oddFiveSL2BoundFamilyInput_G2_F4_E8 :
    OddFiveSL2BoundFamilyInput .G2 ∧ OddFiveSL2BoundFamilyInput .F4 ∧
      OddFiveSL2BoundFamilyInput .E8 :=
  ⟨oddFiveSL2BoundFamilyInput_of_twoPart (by decide) fun _ =>
      excTwoPartInput_G2 (by norm_num) (by norm_num) (by norm_num) le_rfl,
    oddFiveSL2BoundFamilyInput_of_twoPart (by decide) fun f =>
      excTwoPartInput_F4 (s := 2) (by norm_num) (by norm_num)
        (FiveEx.four_dvd_five_pow_sub_one f) (by norm_num) (by norm_num),
    oddFiveSL2BoundFamilyInput_of_twoPart (by decide) fun _ =>
      excTwoPartInput_E8 (by norm_num) (by norm_num) (by norm_num)⟩

end Families

end CFSG.SeitzReduction.RankOne
