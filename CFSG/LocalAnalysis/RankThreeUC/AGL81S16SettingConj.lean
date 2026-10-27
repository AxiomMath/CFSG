module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Facts

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem setting_conj_inf_cj (g h : G) (M : Subgroup G) :
    cj g M ⊓ cj h (cj g M) = cj g (M ⊓ cj (g⁻¹ * h * g) M) := by
  have hgh : g * (g⁻¹ * h * g) = h * g := by group
  rw [cj_inf, cj_cj, cj_cj, hgh]

theorem LocalSetting.conj {p : ℕ} {M V : Subgroup G} (h : LocalSetting p M V) (g : G) :
    LocalSetting p (cj g M) (cj g V) := by
  refine ⟨isElemAbelian_cj h.elemAbelian, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact h.ne_bot (cj_eq_bot_iff.mp hbot)
  · rw [cj_normalizer, h.normalizer_eq]
  · rw [cj_normalizer, h.self_normalizing]
  · intro k hk
    have hk' : g⁻¹ * k * g ∉ M := fun hmem => hk (mem_cj_iff.mpr hmem)
    rw [setting_conj_inf_cj, card_cj]
    exact h.spe _ hk'
  · intro X hX hXp hrank
    have hY : cj g⁻¹ X ≠ ⊥ := fun hb => hX (cj_eq_bot_iff.mp hb)
    have hYp : IsPGroup 2 ↥(cj g⁻¹ X) := isPGroup_cj hXp
    have hM : cj g⁻¹ (cj g M ⊓ normalizer (X : Set G)) =
        M ⊓ normalizer ((cj g⁻¹ X : Subgroup G) : Set G) := by
      rw [cj_inf, cj_normalizer, cj_cj, inv_mul_cancel, cj_one]
    have hrank' : 2 ≤ CFSG.Open.pRank p (M ⊓ normalizer ((cj g⁻¹ X : Subgroup G) : Set G)) := by
      rw [← hM, pRank_cj]
      exact hrank
    have hle := h.u2 (cj g⁻¹ X) hY hYp hrank'
    rw [cj_normalizer] at hle
    have hle' := (cj_le_cj_iff (g := g)).mpr hle
    rw [cj_cj, mul_inv_cancel, cj_one] at hle'
    exact hle'

end CFSG.LocalAnalysis.RankThreeUC
