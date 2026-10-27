module

public import CFSG.CGT.T75JM.L2GTheta

public section

namespace CFSG.CGT.T75JM

open CFSG.Open CFSG.CGT.Timmesfeld75

variable {G H : Type*} [Group G] [Group H]

namespace TCtx

variable {T T₁ : Subgroup G} (h : TCtx T T₁)
include h

theorem exists_config [Finite H] {n m : ℕ} (M : T1Model H n m)
    (E : OntoEmb H (Subgroup.normalizer (T : Set G))) (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ (E' : OntoEmb H (Subgroup.normalizer (T : Set G))) (g : G) (k : Fin m),
      (∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T) ∧ conjSubgroup g T = T₁ ∧ g * g = E'.Φ (M.d0 k) ∧
        ∀ i, g * E'.Φ (M.d i) * g⁻¹ = E'.Φ (M.theta k i) := by
  obtain ⟨E', hT, hB⟩ := h.exists_adjust M hE
  have hcl : ∀ x ∈ Subgroup.normalizer (T : Set G), ∀ y ∈ Subgroup.normalizer (T : Set G),
      x * x = 1 → y * y = 1 → x ∉ T → y ∉ T →
        ∃ n ∈ Subgroup.normalizer (T : Set G), n * x * n⁻¹ = y := by
    intro x hx y hy hx2 hy2 hxT hyT
    obtain ⟨x', rfl⟩ := E.surj x hx
    obtain ⟨y', rfl⟩ := E.surj y hy
    have hx'2 : x' * x' = 1 := E.inj (by rw [map_mul, hx2, map_one])
    have hy'2 : y' * y' = 1 := E.inj (by rw [map_mul, hy2, map_one])
    obtain ⟨n₁, hn₁⟩ := M.inv_class x' hx'2 (fun hm => hxT ((hE x').1 hm))
    obtain ⟨n₂, hn₂⟩ := M.inv_class y' hy'2 (fun hm => hyT ((hE y').1 hm))
    refine ⟨E.Φ (n₂ * n₁⁻¹), E.mem _, ?_⟩
    rw [← hn₁, ← hn₂]
    simp only [map_mul, map_inv]
    group
  obtain ⟨g₀, hg1, hg2⟩ := h.exists_swapper hcl
  obtain ⟨g, k, hgT, hg, hrel⟩ := h.exists_theta M E' hT hB hg1 hg2
  exact ⟨E', g, k, hT, hgT, hg, hrel⟩

theorem exists_config_one [Finite H] {n : ℕ} (M : T1Model H n 1) (hd0 : M.d0 0 = 1)
    (E : OntoEmb H (Subgroup.normalizer (T : Set G))) (hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) :
    ∃ (E' : OntoEmb H (Subgroup.normalizer (T : Set G))) (g : G),
      (∀ x, x ∈ M.T0 ↔ E'.Φ x ∈ T) ∧ conjSubgroup g T = T₁ ∧ g * g = 1 ∧
        ∀ i, g * E'.Φ (M.d i) * g⁻¹ = E'.Φ (M.theta 0 i) := by
  obtain ⟨E', g, k, hT, hgT, hg, hrel⟩ := h.exists_config M E hE
  have hk : k = 0 := Subsingleton.elim _ _
  subst hk
  exact ⟨E', g, hT, hgT, by rw [hg, hd0, map_one], hrel⟩

end TCtx

end CFSG.CGT.T75JM
