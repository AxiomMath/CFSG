module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB6

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T T₁ S : Subgroup G} {a : G}

namespace SecB6

variable (h : SecB6 T T₁ S a)

include h

theorem exists_t_normalizes [Finite G] (h214 : Lemma214) (hInv : InvolutionClassInput) {u : G}
    (hu : u ∈ normIn T T₁) (hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u)
    (hL8 : 8 ≤ Nat.card (normIn T T₁))
    [hNorm : ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁)).Normal]
    (hpair : SylowInner (↥(T₁ ⊔ conjSubgroup a T₁) ⧸
      (cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁))
      ((T₁.subgroupOf (T₁ ⊔ conjSubgroup a T₁)).map
        (QuotientGroup.mk' ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf
          (T₁ ⊔ conjSubgroup a T₁))))) :
    ∃ t ∈ T, conjSubgroup (t⁻¹ * a) T₁ = T₁ := by
  have hS2 := h.sec₂ h214 hInv
  have haX := h.mem_normalizer_sup
  have haN := h.mem_normalizer_cfgM
  have hT₁X : T₁ ≤ T₁ ⊔ conjSubgroup a T₁ := le_sup_left
  obtain ⟨g, hg, hgfix⟩ := hpair.exists_fixed_conj_of_involution hT₁X h.haa haX haN
  have hgT : conjSubgroup g T₁ = T := h.conj_eq_of_fixed h214 hInv hu hvals hL8 hg hgfix
  have hTX : T ≤ T₁ ⊔ conjSubgroup a T₁ := hgT ▸ conjSubgroup_le_of_le_of_mem hT₁X hg
  have hpairT : SylowInner (↥(T₁ ⊔ conjSubgroup a T₁) ⧸
      (cfgM T₁ (conjSubgroup a T₁)).subgroupOf (T₁ ⊔ conjSubgroup a T₁))
      ((T.subgroupOf (T₁ ⊔ conjSubgroup a T₁)).map
        (QuotientGroup.mk' ((cfgM T₁ (conjSubgroup a T₁)).subgroupOf
          (T₁ ⊔ conjSubgroup a T₁)))) := by
    have := hpair.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥(T₁ ⊔ conjSubgroup a T₁)))
    rw [conjSubgroup_map_subgroupOf] at this
    rwa [← hgT]
  obtain ⟨t, htT, htN, hb⟩ := hpairT.exists_inner_of_unique_fixed (cfgM_le_sup _ _) hTX h.haa haX
    haN h.haN fun g' hg' hfix' => by
      have hgg : g' * g ∈ T₁ ⊔ conjSubgroup a T₁ := (T₁ ⊔ conjSubgroup a T₁).mul_mem hg' hg
      have e : conjSubgroup g' T = conjSubgroup (g' * g) T₁ := by
        rw [← hgT, conjSubgroup_conjSubgroup]
      rw [e] at hfix' ⊢
      exact h.conj_eq_of_fixed h214 hInv hu hvals hL8 hgg hfix'
  refine ⟨t, htT, ?_⟩
  have hV₀ : IsPGroup 2 ↥(T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)) :=
    (isPGroup_two_of_isElemAbelian h.sec.cfg.wc₁.1).to_sup_of_normal_right'
      (isPGroup_two_of_isElemAbelian hS2.cfg.isElemAbelian_cfgM)
      (le_sup_left.trans hS2.cfg.le_normalizer_cfgM)
  refine eq_of_conj_le_pGroup h.sec.cfg.wc₁ hV₀ le_sup_left ?_
  refine conjSubgroup_le_of_forall_mem fun v hv => ?_
  have h1 := hb v (hT₁X hv)
  have e : (t⁻¹ * a) * v * (t⁻¹ * a)⁻¹ =
      ((t⁻¹ * a) * v * (t⁻¹ * a)⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact (T₁ ⊔ cfgM T₁ (conjSubgroup a T₁)).mul_mem (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left hv)

end SecB6

end CFSG.CGT.Timmesfeld75
