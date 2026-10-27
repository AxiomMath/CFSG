module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AConcl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mul_swap_centralizer_iff {G : Type*} [Group G] {t tau x : G} (htx : t * x = x * t) :
    (x * (t * tau) = (t * tau) * x) ↔ (x * tau = tau * x) := by
  constructor
  · intro h
    have h1 : t * (x * tau) = t * (tau * x) := by
      calc t * (x * tau) = (t * x) * tau := (mul_assoc t x tau).symm
        _ = (x * t) * tau := by rw [htx]
        _ = x * (t * tau) := mul_assoc x t tau
        _ = (t * tau) * x := h
        _ = t * (tau * x) := mul_assoc t tau x
    exact mul_left_cancel h1
  · intro h
    calc x * (t * tau) = (x * t) * tau := (mul_assoc x t tau).symm
      _ = (t * x) * tau := by rw [← htx]
      _ = t * (x * tau) := mul_assoc t x tau
      _ = t * (tau * x) := by rw [h]
      _ = (t * tau) * x := (mul_assoc t tau x).symm

private lemma mul_t_t_swap {G : Type*} [Group G] {p t tau : G} (ht2 : t * t = 1) :
    (p * t) * (t * tau) = p * tau := by
  rw [← mul_assoc, mul_assoc p t t, ht2, mul_one]

theorem ctx4_swap (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Ctx4 t L S x₁ x₂ lam rho (t * tau) := by
  have ht2 : t * t = 1 := t_mul_self hc.hyp
  have htP : t ∈ twoCore t := hc.hyp.mem_twoCore
  have h0 : Ctx0 t L S x₁ x₂ lam rho := hc.toCtx0
  have hcommS : ∀ s ∈ S, s * t = t * s :=
    fun s hs => mem_invCent_iff.mp (h0.le_invCent hs)
  have htau_t : tau * t = t * tau := hcommS tau hc.tau_mem
  have hL_comm : ∀ x ∈ L, t * x = x * t :=
    fun x hx => (mem_invCent_iff.mp (L_le_invCent hc.hyp hx)).symm
  have htau_eq : t * (t * tau) = tau := by rw [← mul_assoc, ht2, one_mul]
  have hWleS : wreathGrp x₁ x₂ lam ≤ S := by rw [← h0.inf_eq]; exact inf_le_left
  have hWleL : wreathGrp x₁ x₂ lam ≤ L := by rw [← h0.inf_eq]; exact inf_le_right
  have hx1W : x₁ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx2W : x₂ ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hlamW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hx1S : x₁ ∈ S := hWleS hx1W
  have hx2S : x₂ ∈ S := hWleS hx2W
  have hlamS : lam ∈ S := hWleS hlamW
  have hx1L : x₁ ∈ L := hWleL hx1W
  have hx2L : x₂ ∈ L := hWleL hx2W
  have hlamL : lam ∈ L := hWleL hlamW
  have hlePS : twoCore t ≤ S := by rw [hc.S_eq]; exact le_sup_left
  have htS : t ∈ S := hlePS htP
  have htW : t ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_left htP
  have hf : (t * tau) ^ 2 = tau ^ 2 := by
    rw [pow_two, pow_two]
    calc t * tau * (t * tau) = t * (tau * t) * tau := by group
      _ = t * (t * tau) * tau := by rw [htau_t]
      _ = t * t * (tau * tau) := by group
      _ = tau * tau := by rw [ht2, one_mul]
  have htau_mem : t * tau ∈ S := Subgroup.mul_mem _ htS hc.tau_mem
  have htau_not_mem : t * tau ∉ twoCore t ⊔ L := by
    intro h
    apply hc.tau_not_mem
    have htPL : t ∈ twoCore t ⊔ L := Subgroup.mem_sup_left htP
    have h' : t * (t * tau) ∈ twoCore t ⊔ L := Subgroup.mul_mem _ htPL h
    rwa [htau_eq] at h'
  have htau_sq_mem : (t * tau) ^ 2 ∈ twoCore t := by rw [hf]; exact hc.tau_sq_mem
  have htx1inv : t * x₁⁻¹ = x₁⁻¹ * t := hL_comm x₁⁻¹ (L.inv_mem hx1L)
  have htx2inv : t * x₂⁻¹ = x₂⁻¹ * t := hL_comm x₂⁻¹ (L.inv_mem hx2L)
  have htau_x₁ : (t * tau) * x₁ * (t * tau)⁻¹ = x₁⁻¹ := by
    have h1 : (t * tau) * x₁ * (t * tau)⁻¹ = t * (tau * x₁ * tau⁻¹) * t⁻¹ := by group
    rw [h1, hc.tau_x₁, htx1inv]
    group
  have htau_x₂ : (t * tau) * x₂ * (t * tau)⁻¹ = x₂⁻¹ := by
    have h1 : (t * tau) * x₂ * (t * tau)⁻¹ = t * (tau * x₂ * tau⁻¹) * t⁻¹ := by group
    rw [h1, hc.tau_x₂, htx2inv]
    group
  have htau_lam : (t * tau) * lam = lam * (t * tau) := by
    have htlam : t * lam = lam * t := hL_comm lam hlamL
    calc (t * tau) * lam = t * (tau * lam) := by group
      _ = t * (lam * tau) := by rw [hc.tau_lam]
      _ = t * lam * tau := by group
      _ = lam * t * tau := by rw [htlam]
      _ = lam * (t * tau) := by group
  have htau_rho : (t * tau) * rho = rho * (t * tau) := by
    have htrho : t * rho = rho * t := hL_comm rho h0.rho_mem
    calc (t * tau) * rho = t * (tau * rho) := by group
      _ = t * (rho * tau) := by rw [hc.tau_rho]
      _ = t * rho * tau := by group
      _ = rho * t * tau := by rw [htrho]
      _ = rho * (t * tau) := by group
  have hcentL : L ⊓ centralizer ({(t * tau)} : Set G) = L ⊓ centralizer ({tau} : Set G) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      obtain ⟨hxL, hxcent⟩ := hx
      refine ⟨hxL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxcent ⊢
      exact (mul_swap_centralizer_iff (t := t) (tau := tau) (x := x)
        (hL_comm x hxL)).mp hxcent
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      obtain ⟨hxL, hxcent⟩ := hx
      refine ⟨hxL, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxcent ⊢
      exact (mul_swap_centralizer_iff (t := t) (tau := tau) (x := x)
        (hL_comm x hxL)).mpr hxcent
  have hcentT : wreathGrp x₁ x₂ lam ⊓ centralizer ({(t * tau)} : Set G) =
      wreathGrp x₁ x₂ lam ⊓ centralizer ({tau} : Set G) := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      obtain ⟨hxW, hxcent⟩ := hx
      refine ⟨hxW, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxcent ⊢
      exact (mul_swap_centralizer_iff (t := t) (tau := tau) (x := x)
        (hL_comm x (hWleL hxW))).mp hxcent
    · intro x hx
      rw [Subgroup.mem_inf] at hx ⊢
      obtain ⟨hxW, hxcent⟩ := hx
      refine ⟨hxW, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hxcent ⊢
      exact (mul_swap_centralizer_iff (t := t) (tau := tau) (x := x)
        (hL_comm x (hWleL hxW))).mpr hxcent
  have hperm_four :
      Nonempty (↥(L ⊓ centralizer ({(t * tau)} : Set G)) ≃* Equiv.Perm (Fin 4)) := by
    obtain ⟨e⟩ := hc.perm_four
    exact ⟨(MulEquiv.subgroupCongr hcentL).trans e⟩
  have hinvol_outer : ∀ γ ∈ invCent t, γ ∉ twoCore t ⊔ L → γ ^ 2 ∈ twoCore t →
      ∃ h ∈ invCent t, ∃ p ∈ twoCore t, h * γ * h⁻¹ = p * (t * tau) := by
    intro γ hγ hγPL hγ2
    obtain ⟨h, hh, p, hp, e⟩ := hc.invol_outer γ hγ hγPL hγ2
    refine ⟨h, hh, p * t, Subgroup.mul_mem _ hp htP, ?_⟩
    rw [e]
    exact (mul_t_t_swap (t := t) (tau := tau) (p := p) ht2).symm
  have hnorm_baseGrp : ctxW t x₁ x₂ ⊔ closure {rho, lam, t * tau} =
      ctxW t x₁ x₂ ⊔ closure {rho, lam, tau} := by
    apply le_antisymm
    · apply sup_le le_sup_left
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h1 | h2 | h3
      · rw [h1]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [h2]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [h3]
        exact Subgroup.mul_mem ((ctxW t x₁ x₂ : Subgroup G) ⊔ closure {rho, lam, tau})
          (Subgroup.mem_sup_left htW)
          (Subgroup.mem_sup_right
            (Subgroup.subset_closure (show tau ∈ ({rho, lam, tau} : Set G) by simp)))
    · apply sup_le le_sup_left
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h1 | h2 | h3
      · rw [h1]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [h2]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · rw [h3]
        have hmem := Subgroup.mul_mem ((ctxW t x₁ x₂ : Subgroup G) ⊔ closure {rho, lam, t * tau})
            (Subgroup.mem_sup_left htW)
            (Subgroup.mem_sup_right
              (Subgroup.subset_closure
                (show t * tau ∈ ({rho, lam, t * tau} : Set G) by simp)))
        rw [SetLike.mem_coe]
        simpa only [htau_eq] using hmem
  have hzp : ctxW t x₁ x₂ ⊔ zpowers (t * tau) = ctxW t x₁ x₂ ⊔ zpowers tau := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      exact Subgroup.mul_mem ((ctxW t x₁ x₂ : Subgroup G) ⊔ zpowers tau)
        (Subgroup.mem_sup_left htW)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers tau))
    · apply sup_le le_sup_left
      apply Subgroup.zpowers_le.mpr
      have hmem := Subgroup.mul_mem ((ctxW t x₁ x₂ : Subgroup G) ⊔ zpowers (t * tau))
          (Subgroup.mem_sup_left htW)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers (t * tau)))
      simpa only [htau_eq] using hmem
  have hS : S = twoCore t ⊔ m12Grp x₁ x₂ lam (t * tau) := by
    apply le_antisymm
    · rw [hc.S_eq]
      apply sup_le
      · exact le_sup_left
      · unfold m12Grp
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with h1 | h2 | h3 | h4
        · rw [h1]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
        · rw [h2]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
        · rw [h3]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
        · rw [h4]
          have hmem := Subgroup.mul_mem ((twoCore t : Subgroup G) ⊔ closure {x₁, x₂, lam, t * tau})
              (Subgroup.mem_sup_left htP)
              (Subgroup.mem_sup_right
                (Subgroup.subset_closure
                  (show t * tau ∈ ({x₁, x₂, lam, t * tau} : Set G) by simp)))
          rw [SetLike.mem_coe]
          simpa only [htau_eq] using hmem
    · apply sup_le
      · rw [hc.S_eq]; exact le_sup_left
      · unfold m12Grp
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with h1 | h2 | h3 | h4
        · rw [h1]; exact hx1S
        · rw [h2]; exact hx2S
        · rw [h3]; exact hlamS
        · rw [h4]; exact Subgroup.mul_mem S htS hc.tau_mem
  have hl44 : Lemma4_4Concl t (t * tau) :=
    ⟨by rw [hf]; exact hc.l44.1, hc.l44.2⟩
  exact
    { toCtx :=
        { toCtx0 := hc.toCtx0
          ne_fstar := hc.ne_fstar
          relIndex_two := hc.relIndex_two
          index_PT := hc.index_PT
          card_S := hc.card_S
          S_eq := hS
          tau_mem := htau_mem
          tau_not_mem := htau_not_mem
          tau_sq_mem := htau_sq_mem
          tau_x₁ := htau_x₁
          tau_x₂ := htau_x₂
          tau_lam := htau_lam
          tau_rho := htau_rho
          cent_L_tau := by rw [hcentL]; exact hc.cent_L_tau
          perm_four := hperm_four
          cent_T_tau := by rw [hcentT]; exact hc.cent_T_tau
          dihedral := hc.dihedral
          normal_W := hc.normal_W
          cent_W := hc.cent_W
          invol_outer := hinvol_outer
          center_ge := hc.center_ge
          center_le := hc.center_le
          center_omega := hc.center_omega
          m2_PT := hc.m2_PT
          m2_PT_attained := hc.m2_PT_attained
          E16_cases := hc.E16_cases
          cent_baseGrp := hc.cent_baseGrp
          norm_baseGrp := by rw [hnorm_baseGrp]; exact hc.norm_baseGrp
          normal_norm := by rw [hzp]; exact hc.normal_norm }
      l42 := hc.l42
      l43 := hc.l43
      l44 := hl44 }

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
