module

public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.P55

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem i336UsedAt : I336UsedAt := by
  intro G _ _ p hp hp2 T D hT hD hDT hTD hrk
  have hDne : D ≠ ⊥ := by
    rintro rfl
    exact hTD (Subgroup.commutator_bot_right T)
  obtain ⟨D₀, hD₀D, hD₀c, hD₀ne⟩ :=
    I336.exists_hyperplane_comm_ne_bot hp hp2 hT hD hDne hDT hTD
  obtain ⟨hp3, ⟨e₀⟩⟩ := I336.quat_of_action hp hp2 (hT.to_le inf_le_left)
    (hrk D₀ hD₀D hD₀c hD₀ne) hD (I336.normalizer_inf_centralizer hD hDT hD₀D) hD₀ne
  refine ⟨hp3, ?_⟩
  by_cases hTc : T ≤ Subgroup.centralizer (D₀ : Set G)
  ·
    left
    have h : T ⊓ Subgroup.centralizer (D₀ : Set G) = T := inf_eq_left.mpr hTc
    exact ⟨(MulEquiv.subgroupCongr h.symm).trans e₀⟩
  · right
    obtain ⟨D₁, hD₁D, hD₁c, hD₁not⟩ := I336.exists_second_hyperplane hp hp2 hT hD hDne hDT hTc
    have hD₁ne : (⁅T ⊓ Subgroup.centralizer (D₁ : Set G), D⁆ : Subgroup G) ≠ ⊥ := by
      intro h
      apply hD₁not
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
        (Subgroup.centralizer_le (show (D₀ : Set G) ⊆ D from hD₀D))
    obtain ⟨-, ⟨e₁⟩⟩ := I336.quat_of_action hp hp2 (hT.to_le inf_le_left)
      (hrk D₁ hD₁D hD₁c hD₁ne) hD (I336.normalizer_inf_centralizer hD hDT hD₁D) hD₁ne
    have hne : D₀ ≠ D₁ := by
      rintro rfl
      exact hD₁not inf_le_right
    obtain ⟨hsup, hcard⟩ := I336.card_inf_hyperplanes hp hD hD₀D hD₁D hD₀c hD₁c hne
    obtain ⟨U, hU, hUe, hUc⟩ := I336.exists_U hp hp2 hT hD hDne hDT hrk hTD hD₀D hD₁D hsup
      hD₀ne hD₁ne e₀ e₁
    refine ⟨D₀ ⊓ D₁, inf_le_left.trans hD₀D, ?_, ?_, U, hU, hUe, hUc⟩
    · subst hp3
      simpa using hcard
    · intro h
      apply hD₀ne
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h ⊢
      exact (inf_le_inf_left _ (Subgroup.centralizer_le
        (show ((D₀ ⊓ D₁ : Subgroup G) : Set G) ⊆ D₀ from inf_le_left))).trans h

end CFSG.LocalAnalysis.GLTheoremA.P55
