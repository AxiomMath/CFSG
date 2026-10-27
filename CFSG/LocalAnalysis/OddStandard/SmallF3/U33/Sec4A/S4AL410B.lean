module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL46

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma tau_conj_x1x2_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have hcomm_inv : x₁⁻¹ * x₂⁻¹ = (x₁ * x₂)⁻¹ := by
    have := congrArg Inv.inv h.wreath.comm.symm
    simpa [mul_inv_rev] using this
  calc tau * (x₁ * x₂) * tau⁻¹
      = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
    _ = (x₁ * x₂)⁻¹ := hcomm_inv

private lemma x1x2_tau_sq (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    (tau * (x₁ * x₂)) * (tau * (x₁ * x₂)) = 1 := by
  have hconj := tau_conj_x1x2_of h
  have hτ2 : tau * tau = 1 := by rw [← pow_two]; exact h44
  calc (tau * (x₁ * x₂)) * (tau * (x₁ * x₂))
      = (tau * (x₁ * x₂) * tau⁻¹) * (tau * tau) * (x₁ * x₂) := by group
    _ = (x₁ * x₂)⁻¹ * 1 * (x₁ * x₂) := by rw [hconj, hτ2]
    _ = 1 := by group

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private theorem exists_conj_of_invol_outer (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (htau : ∃ g : G, g * t * g⁻¹ = tau)
    (httau : ∃ g : G, g * t * g⁻¹ = t * tau) {γ : G} (hγ : γ ∈ invCent t)
    (hγout : γ ∉ twoCore t ⊔ L) (hγ2 : γ ^ 2 = 1) :
    ∃ g : G, g * t * g⁻¹ = γ := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  obtain ⟨k, _hk, p, hp, hkp⟩ :=
    h.invol_outer γ hγ hγout (by rw [hγ2]; exact Subgroup.one_mem _)
  have hpt : p ∈ zpowers t := by rw [← h43]; exact hp
  rcases mem_zpowers_eq_one_or_eq ht2 hpt with hp1 | hpt'
  · rw [hp1, one_mul] at hkp
    obtain ⟨g₀, hg₀⟩ := htau
    refine ⟨k⁻¹ * g₀, ?_⟩
    rw [show k⁻¹ * g₀ * t * (k⁻¹ * g₀)⁻¹ = k⁻¹ * (g₀ * t * g₀⁻¹) * k by group, hg₀,
      ← hkp]
    group
  · rw [hpt'] at hkp
    obtain ⟨g₀, hg₀⟩ := httau
    refine ⟨k⁻¹ * g₀, ?_⟩
    rw [show k⁻¹ * g₀ * t * (k⁻¹ * g₀)⁻¹ = k⁻¹ * (g₀ * t * g₀⁻¹) * k by group, hg₀,
      ← hkp]
    group

theorem exists_mem_tG_of_normal_E8 (h : Ctx t L S x₁ x₂ lam rho tau)
    (h43 : twoCore t = zpowers t) (h44 : tau ^ 2 = 1) (htau : ∃ g : G, g * t * g⁻¹ = tau)
    (httau : ∃ g : G, g * t * g⁻¹ = t * tau) {E : Subgroup G} (hEn : NormalIn E S)
    (hEe : CFSG.Open.IsElemAbelian 2 E) (hEc : Nat.card E = 8) :
    ∃ g : G, ∃ c ∈ E, g * t * g⁻¹ = c := by
  have hx1L : x₁ ∈ L := (generators_mem_L h.toCtx0).1
  have hx2L : x₂ ∈ L := (generators_mem_L h.toCtx0).2.1
  have hxL : x₁ * x₂ ∈ L := Subgroup.mul_mem L hx1L hx2L
  have hx_inv : x₁ * x₂ ∈ invCent t := L_le_invCent h.hyp hxL
  have htau_inv : tau ∈ invCent t := h.le_invCent h.tau_mem
  have ht_inv : t ∈ invCent t := mem_invCent_iff.mpr rfl
  rcases lemma4_6_of h h43 h44 E hEn hEe hEc with hE | hE | hE | hE | hE
  · exact ⟨1, t, by rw [hE]; exact Subgroup.subset_closure (by simp), by simp⟩
  · obtain ⟨g, hg⟩ := htau
    exact ⟨g, tau, by rw [hE]; exact Subgroup.subset_closure (by simp), hg⟩
  · obtain ⟨g, hg⟩ := httau
    exact ⟨g, t * tau, by rw [hE]; exact Subgroup.subset_closure (by simp), hg⟩
  ·
    let γ : G := tau * (x₁ * x₂)
    have hγinv : γ ∈ invCent t := by
      dsimp only [γ]
      exact Subgroup.mul_mem _ htau_inv hx_inv
    have hγout : γ ∉ twoCore t ⊔ L := by
      intro hmem
      have hxsub : (x₁ * x₂)⁻¹ ∈ twoCore t ⊔ L :=
        Subgroup.mem_sup_right (Subgroup.inv_mem L hxL)
      have htau_mem : tau ∈ twoCore t ⊔ L := by
        have hm := Subgroup.mul_mem _ hmem hxsub
        rwa [show γ * (x₁ * x₂)⁻¹ = tau by dsimp only [γ]; group] at hm
      exact h.tau_not_mem htau_mem
    have hγ2 : γ ^ 2 = 1 := by
      have hsq := x1x2_tau_sq h h44
      dsimp only [γ]
      rw [pow_two, hsq]
    obtain ⟨g, hg⟩ := exists_conj_of_invol_outer h h43 htau httau hγinv hγout hγ2
    exact ⟨g, γ, by rw [hE]; exact Subgroup.subset_closure (by simp [γ]), hg⟩
  ·
    let γ : G := t * tau * (x₁ * x₂)
    have hγinv : γ ∈ invCent t := by
      dsimp only [γ]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht_inv htau_inv) hx_inv
    have hγout : γ ∉ twoCore t ⊔ L := by
      intro hmem
      have htmem : t⁻¹ ∈ twoCore t ⊔ L :=
        Subgroup.mem_sup_left (Subgroup.inv_mem _ h.hyp.mem_twoCore)
      have hxsub : (x₁ * x₂)⁻¹ ∈ twoCore t ⊔ L :=
        Subgroup.mem_sup_right (Subgroup.inv_mem L hxL)
      have htau_mem : tau ∈ twoCore t ⊔ L := by
        have hm := Subgroup.mul_mem _ (Subgroup.mul_mem _ htmem hmem) hxsub
        rwa [show t⁻¹ * γ * (x₁ * x₂)⁻¹ = tau by dsimp only [γ]; group] at hm
      exact h.tau_not_mem htau_mem
    have hγ2 : γ ^ 2 = 1 := by
      have hww : (tau * (x₁ * x₂)) * (tau * (x₁ * x₂)) = 1 := x1x2_tau_sq h h44
      have ht_tau : Commute t tau := (mem_invCent_iff.mp htau_inv).symm
      have ht_x : Commute t (x₁ * x₂) := (mem_invCent_iff.mp hx_inv).symm
      have htw : Commute t (tau * (x₁ * x₂)) := ht_tau.mul_right ht_x
      dsimp only [γ]
      rw [show t * tau * (x₁ * x₂) = t * (tau * (x₁ * x₂)) by group, htw.mul_pow 2,
        show t ^ 2 = 1 by rw [pow_two]; exact t_mul_self h.hyp,
        show (tau * (x₁ * x₂)) ^ 2 = 1 by rw [pow_two]; exact hww, mul_one]
    obtain ⟨g, hg⟩ := exists_conj_of_invol_outer h h43 htau httau hγinv hγout hγ2
    exact ⟨g, γ, by rw [hE]; exact Subgroup.subset_closure (by simp [γ]), hg⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
