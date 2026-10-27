module

public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LieType.SpecialLinear

open scoped MatrixGroups
open CFSG.LinearGroups CFSG.LocalAnalysis.EvenBN.Common

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z]

omit [Field F] [CharP F 2] in
theorem exists_finset_card_four_of_card (hq : 4 ≤ Fintype.card F) :
    ∃ s : Finset F, s.card = 4 := by
  have h4 : 4 ≤ (Finset.univ : Finset F).card := by simpa using hq
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h4
  exact ⟨t, ht⟩

theorem ker_eq_bot_of_factor_nontrivial (hq : 4 ≤ Fintype.card F)
    (ρ : Representation (ZMod 2) (SL(2, F) × SL(2, F)) Z)
    (h₁ : ∃ g, ρ (g, 1) ≠ 1) (h₂ : ∃ g, ρ (1, g) ≠ 1) :
    ρ.ker = ⊥ := by
  have h4 : 4 ≤ Nat.card F := by simpa [Nat.card_eq_fintype_card] using hq
  have hnorm : ρ.ker.Normal := MonoidHom.normal_ker ρ
  rcases normal_sl2_prod_eq (k := F) h4 hnorm with h | h | h | h
  · exact h
  · obtain ⟨g, hg⟩ := h₁
    exfalso
    apply hg
    have hmem : (g, 1) ∈ ρ.ker := by
      rw [h]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top g, Subgroup.mem_bot.mpr rfl⟩
    simpa [MonoidHom.mem_ker] using hmem
  · obtain ⟨g, hg⟩ := h₂
    exfalso
    apply hg
    have hmem : (1, g) ∈ ρ.ker := by
      rw [h]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top g⟩
    simpa [MonoidHom.mem_ker] using hmem
  · obtain ⟨g, hg⟩ := h₁
    exfalso
    apply hg
    have hmem : (g, 1) ∈ ρ.ker := by
      rw [h]
      exact Subgroup.mem_top (g, 1)
    simpa [MonoidHom.mem_ker] using hmem

end CFSG.LieType.SpecialLinear
