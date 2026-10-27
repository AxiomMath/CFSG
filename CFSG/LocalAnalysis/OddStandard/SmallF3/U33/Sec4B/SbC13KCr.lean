module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13KOrd

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma c13K_four_le_base (x₁ x₂ : G) : fourGrp x₁ x₂ ≤ baseGrp x₁ x₂ := by
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  refine (Subgroup.closure_le (K := baseGrp x₁ x₂)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · rw [hg]; exact Subgroup.pow_mem _ hx₁ 2
  · rw [hg]; exact Subgroup.pow_mem _ (Subgroup.mul_mem _ hx₁ hx₂) 2

theorem c13K_CM_t_rho (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {g : G}
    (hg : g ∈ ctxM t tau x₁ x₂) (hgt : g * t = t * g) (hgρ : g * rho = rho * g) :
    g ∈ closure ({t, tau, rho} : Set G) := by
  have hgτ_mem : g * tau * g⁻¹ ∈ conjIn (ctxM t tau x₁ x₂) tau := ⟨g, hg, rfl⟩
  rw [hc.tauM] at hgτ_mem
  obtain ⟨v, hvV, hv_eq⟩ := hgτ_mem
  simp only [smul_eq_mul] at hv_eq
  have hρτ : rho * tau * rho⁻¹ = tau := by
    rw [(c13K_rho_comm hc).2.1]; group
  have hgρ' : g⁻¹ * rho⁻¹ = rho⁻¹ * g⁻¹ := by
    rw [← mul_inv_rev, hgρ.symm, mul_inv_rev]
  have hconj : rho * (g * tau * g⁻¹) * rho⁻¹ = g * tau * g⁻¹ := by
    calc rho * (g * tau * g⁻¹) * rho⁻¹
        = (rho * g) * tau * (g⁻¹ * rho⁻¹) := by group
      _ = (g * rho) * tau * (rho⁻¹ * g⁻¹) := by rw [hgρ.symm, hgρ']
      _ = g * (rho * tau * rho⁻¹) * g⁻¹ := by group
      _ = g * tau * g⁻¹ := by rw [hρτ]
  have hfix : rho * v * rho⁻¹ = v := by
    have h2 : rho * (tau * v) * rho⁻¹ = tau * v := by
      rw [hv_eq]; exact hconj
    have h3 : rho * (tau * v) * rho⁻¹ = tau * (rho * v * rho⁻¹) := by
      calc rho * (tau * v) * rho⁻¹
          = (rho * tau * rho⁻¹) * (rho * v * rho⁻¹) := by group
        _ = tau * (rho * v * rho⁻¹) := by rw [hρτ]
    rw [h3] at h2
    exact mul_left_cancel h2
  have hvQ : v ∈ ctxQ t tau x₁ x₂ rho := hc.base_le_Q (c13K_four_le_base x₁ x₂ hvV)
  have hv1 : v = 1 := hc.fpf_QY.fix v hvQ hfix
  have hgtau : g * tau * g⁻¹ = tau := by
    rw [← hv_eq, hv1, mul_one]
  have hgtau_comm : g * tau = tau * g := by
    calc g * tau = (g * tau * g⁻¹) * g := by group
      _ = tau * g := by rw [hgtau]
  have hmem_cent : g ∈ centralizer ((closure ({t, tau, rho} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact hgt.symm
    · exact hgtau_comm.symm
    · exact hgρ.symm
  have hg_in : g ∈ ctxM t tau x₁ x₂ ⊓
      centralizer ((closure ({t, tau, rho} : Set G) : Subgroup G) : Set G) := ⟨hg, hmem_cent⟩
  rw [hc.cent_trho] at hg_in
  exact hg_in

theorem c13K_fix_Tp (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {s : G}
    (hs : s ∈ c13KTp t tau x₁ x₂ rho) (hρs : rho * s * rho⁻¹ = s) : s = t ∨ s = t * tau := by
  rw [c13K_mem_Tp_iff hc s] at hs
  rcases hs with ⟨c, hcC, rfl⟩ | ⟨d, hd, rfl⟩
  · left
    have hρt : rho * t = t * rho := (c13K_rho_comm hc).1
    have h1 : rho * (t * c) * rho⁻¹ = t * (rho * c * rho⁻¹) := by
      calc rho * (t * c) * rho⁻¹
          = (rho * t) * c * rho⁻¹ := by group
        _ = (t * rho) * c * rho⁻¹ := by rw [hρt]
        _ = t * (rho * c * rho⁻¹) := by group
    rw [h1] at hρs
    have hfix : rho * c * rho⁻¹ = c := mul_left_cancel hρs
    rw [hc.fpf_QY.fix c hcC.1 hfix, mul_one]
  · right
    have hρt : rho * t = t * rho := (c13K_rho_comm hc).1
    have hρtau : rho * tau = tau * rho := (c13K_rho_comm hc).2.1
    have h1 : rho * (t * tau * d) * rho⁻¹ = t * tau * (rho * d * rho⁻¹) := by
      calc rho * (t * tau * d) * rho⁻¹
          = (rho * t) * tau * d * rho⁻¹ := by group
        _ = (t * rho) * tau * d * rho⁻¹ := by rw [hρt]
        _ = t * (rho * tau) * d * rho⁻¹ := by group
        _ = t * (tau * rho) * d * rho⁻¹ := by rw [hρtau]
        _ = t * tau * (rho * d * rho⁻¹) := by group
    rw [h1] at hρs
    have hfix : rho * d * rho⁻¹ = d := mul_left_cancel hρs
    rw [hc.fpf_QY.fix d (hc.base_le_Q hd) hfix, mul_one]

private lemma c13K_CK_t_rho_aux
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om) {k : G}
    (hk : k ∈ ctxK t tau x₁ x₂ rho) (hkt : k * t = t * k) (hkρ : k * rho = rho * k) :
    k ∈ closure ({t, om} : Set G) ⊔ zpowers rho := by
  have hkM : k ∈ ctxM t tau x₁ x₂ := by
    have h : k ∈ ctxK t tau x₁ x₂ rho ⊓ centralizer ({t} : Set G) :=
      ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkt⟩
    rw [c13K_CK_t_eq hc] at h
    exact h.1
  have hk_cl : k ∈ closure ({t, tau, rho} : Set G) := c13K_CM_t_rho hc hkM hkt hkρ
  have hsub : closure ({t, tau, rho} : Set G) ≤ closure ({t, om} : Set G) ⊔ zpowers rho := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · rw [hx]
      refine Subgroup.mem_sup_left ?_
      have ht : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
      have hom : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
      have hom_inv : om⁻¹ = om := by
        have h := (c13K_rel hc).2.2.1
        exact inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h)
      have homt : om * t * om⁻¹ = t * tau := (c13K_rel hc).2.2.2.2.2.2.2
      have ht2 : t * t = 1 := by
        have h := (c13K_rel hc).1
        rwa [pow_two] at h
      have h1 : t * om * t * om = tau := by
        calc t * om * t * om = t * (om * t * om) := by group
          _ = t * (om * t * om⁻¹) := by rw [hom_inv]
          _ = t * (t * tau) := by rw [homt]
          _ = tau := by rw [← mul_assoc, ht2, one_mul]
      rw [← h1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hom) ht) hom
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers rho)
  exact hsub hk_cl

theorem c13K_CK_rho
    (hc : Ctx13M t L S x₁ x₂ lam rho tau om)
    (hne : ∃ k ∈ ctxK t tau x₁ x₂ rho, k ∉ ctxM t tau x₁ x₂) :
    ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) =
      closure ({t, om} : Set G) ⊔ zpowers rho := by
  apply le_antisymm
  · intro k hk
    have hkK : k ∈ ctxK t tau x₁ x₂ rho := hk.1
    have hkρ : k * rho = rho * k := Subgroup.mem_centralizer_singleton_iff.mp hk.2
    have hsTp : k * t * k⁻¹ ∈ c13KTp t tau x₁ x₂ rho := by
      have h : k * t * k⁻¹ ∈ conjIn (ctxK t tau x₁ x₂ rho) t := ⟨k, hkK, rfl⟩
      rwa [c13K_tK_eq hc hne] at h
    have hρs : rho * (k * t * k⁻¹) * rho⁻¹ = k * t * k⁻¹ := by
      have hρk : rho * k * rho⁻¹ = k := by rw [hkρ.symm]; group
      have hρt : rho * t * rho⁻¹ = t := by rw [(c13K_rho_comm hc).1]; group
      have hρki : rho * k⁻¹ * rho⁻¹ = k⁻¹ := by
        calc rho * k⁻¹ * rho⁻¹ = (rho * k * rho⁻¹)⁻¹ := by group
          _ = k⁻¹ := by rw [hρk]
      calc rho * (k * t * k⁻¹) * rho⁻¹
          = (rho * k * rho⁻¹) * (rho * t * rho⁻¹) * (rho * k⁻¹ * rho⁻¹) := by group
        _ = k * t * k⁻¹ := by rw [hρk, hρt, hρki]
    rcases c13K_fix_Tp hc hsTp hρs with h | h
    · have hkt : k * t = t * k := by
        calc k * t = (k * t * k⁻¹) * k := by group
          _ = t * k := by rw [h]
      exact c13K_CK_t_rho_aux hc hkK hkt hkρ
    · have homt : om * t * om⁻¹ = t * tau := (c13K_rel hc).2.2.2.2.2.2.2
      have homK : om ∈ ctxK t tau x₁ x₂ rho := hc.M_le_K (c13K_mem_M hc).2.2.1
      have hk'K : om⁻¹ * k ∈ ctxK t tau x₁ x₂ rho :=
        (ctxK t tau x₁ x₂ rho).mul_mem ((ctxK t tau x₁ x₂ rho).inv_mem homK) hkK
      have hk't_conj : (om⁻¹ * k) * t * (om⁻¹ * k)⁻¹ = t := by
        have h' : k * t * k⁻¹ = om * t * om⁻¹ := by rw [h, homt]
        calc (om⁻¹ * k) * t * (om⁻¹ * k)⁻¹
            = om⁻¹ * (k * t * k⁻¹) * om := by group
          _ = om⁻¹ * (om * t * om⁻¹) * om := by rw [h']
          _ = t := by group
      have hk't : (om⁻¹ * k) * t = t * (om⁻¹ * k) := by
        calc (om⁻¹ * k) * t
            = ((om⁻¹ * k) * t * (om⁻¹ * k)⁻¹) * (om⁻¹ * k) := by group
          _ = t * (om⁻¹ * k) := by rw [hk't_conj]
      have homρ : om * rho = rho * om := (c13K_rho_comm hc).2.2.symm
      have hom_inv : om⁻¹ = om := by
        have h := (c13K_rel hc).2.2.1
        exact inv_eq_of_mul_eq_one_right (by rwa [pow_two] at h)
      have hk'ρ : (om⁻¹ * k) * rho = rho * (om⁻¹ * k) := by
        have hom_inv_ρ : om⁻¹ * rho = rho * om⁻¹ := by rw [hom_inv, homρ]
        calc (om⁻¹ * k) * rho = om⁻¹ * (k * rho) := by group
          _ = om⁻¹ * (rho * k) := by rw [hkρ]
          _ = (om⁻¹ * rho) * k := by group
          _ = (rho * om⁻¹) * k := by rw [hom_inv_ρ]
          _ = rho * (om⁻¹ * k) := by group
      have hk'_mem : om⁻¹ * k ∈ closure ({t, om} : Set G) ⊔ zpowers rho :=
        c13K_CK_t_rho_aux hc hk'K hk't hk'ρ
      have hk_eq : k = om * (om⁻¹ * k) := by group
      rw [hk_eq]
      exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))) hk'_mem
  · apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact ⟨hc.M_le_K (c13K_mem_M hc).1,
          Subgroup.mem_centralizer_singleton_iff.mpr (c13K_rho_comm hc).1.symm⟩
      · rw [hx]
        exact ⟨hc.M_le_K (c13K_mem_M hc).2.2.1,
          Subgroup.mem_centralizer_singleton_iff.mpr (c13K_rho_comm hc).2.2.symm⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨hc.M_le_K (c13K_mem_M hc).2.2.2.1,
        Subgroup.mem_centralizer_singleton_iff.mpr (by group)⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
