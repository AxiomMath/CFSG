module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private theorem l18_conj_eq_of_mem_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {g y : G}
    (hg : g ∈ ctxCY t tau x₁ x₂ rho) (hy : y ∈ ctxYq t tau x₁ x₂ rho) :
    g * y * g⁻¹ = y := by
  have hc' : y * g = g * y :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hg).2 y hy
  rw [hc'.symm, mul_assoc, mul_inv_cancel, mul_one]

private theorem l18_t_not_mem_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∉ ctxCY t tau x₁ x₂ rho := by
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  obtain ⟨-, -, -, -, -, -, hYV, -, hv1mem, -, ht1, -, -, -, -, -, -, -, -⟩ := hV
  have hv1Y : v₁ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hYV]; exact Subgroup.mem_sup_right hv1mem
  intro htC
  have hconj : t * v₁ * t⁻¹ = v₁ := l18_conj_eq_of_mem_C hc htC hv1Y
  rw [hconj] at ht1
  have hz1 : (x₁ * x₂) ^ 2 = 1 := by
    have h' : v₁ * 1 = v₁ * (x₁ * x₂) ^ 2 := by rw [mul_one]; exact ht1
    exact (mul_left_cancel h').symm
  exact (l17_yz_ne hc).2.1 hz1

theorem l18_not_mem_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∉ ctxCY t tau x₁ x₂ rho ∧ lam ∉ ctxCY t tau x₁ x₂ rho ∧
      t * lam ∉ ctxCY t tau x₁ x₂ rho := by
  obtain ⟨V', v₁, v₂, hV⟩ := hc.data_V
  obtain ⟨-, -, -, -, -, -, hYV, -, -, hv1ne, -, hv2mem, -, -, -, hlt2, -, -, -⟩ := hV
  have hv2Y : v₂ ∈ ctxYq t tau x₁ x₂ rho := by
    rw [hYV]; exact Subgroup.mem_sup_right hv2mem
  have hx1sqY : x₁ ^ 2 ∈ ctxYq t tau x₁ x₂ rho :=
    l17_V_le_Y hc (Subgroup.subset_closure (by simp))
  refine ⟨l18_t_not_mem_C hc, ?_, ?_⟩
  · intro hlamC
    have hconj : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 :=
      l18_conj_eq_of_mem_C hc hlamC hx1sqY
    have h := l17_lam_y hc
    rw [hconj] at h
    have hz1 : (x₁ * x₂) ^ 2 = 1 := by
      have h' : x₁ ^ 2 * 1 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by rw [mul_one]; exact h
      exact (mul_left_cancel h').symm
    exact (l17_yz_ne hc).2.1 hz1
  · intro htlamC
    have hconj : (t * lam) * v₂ * (t * lam)⁻¹ = v₂ :=
      l18_conj_eq_of_mem_C hc htlamC hv2Y
    have hlamt : lam * t = t * lam := (l17_lam_comm hc).1
    have hlt := hlt2
    rw [hlamt] at hlt
    rw [hconj] at hlt
    have hv1_1 : v₁ = 1 := by
      have h' : v₂ * 1 = v₂ * v₁ := by rw [mul_one]; exact hlt
      exact (mul_left_cancel h').symm
    exact hv1ne hv1_1

private theorem l18_t_mem_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∈ ctxOK t tau x₁ x₂ rho :=
  l18_R_le_OK hc (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))

private theorem l18_om_mem_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    om ∈ ctxOK t tau x₁ x₂ rho :=
  l18_C_le_OK hc
    (l18_QA_le_C hc (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))))

private theorem l18_tom_le_OK (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) ≤ ctxOK t tau x₁ x₂ rho := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact l18_t_mem_OK hc
  · exact l18_om_mem_OK hc

private theorem l18_tom_le_cent (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) ≤ centralizer ({rho} : Set G) :=
  (ctx13_T_facts hc).1

private theorem l18_rho_mem_cent_tom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    rho ∈ centralizer (((closure ({t, om} : Set G)) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (l18_tom_le_cent hc ha) rho rfl).symm

theorem l18_OK_cap_cent_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxOK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = closure {t, om} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxOK, hxCent⟩ := Subgroup.mem_inf.mp hx
    have hOKleK : ctxOK t tau x₁ x₂ rho ≤ ctxK t tau x₁ x₂ rho :=
      (l18_OK_normal (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho)).1
    have hxsup : x ∈ closure ({t, om} : Set G) ⊔ zpowers rho := by
      have hmem : x ∈ ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hOKleK hxOK, hxCent⟩
      rwa [hc.CK_rho] at hmem
    have hnorm : ∀ k ∈ zpowers rho, ∀ h ∈ closure ({t, om} : Set G),
        k * h * k⁻¹ ∈ closure ({t, om} : Set G) := by
      intro k hk h hh
      have hkC : k ∈ centralizer (((closure ({t, om} : Set G)) : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr (l18_rho_mem_cent_tom hc) hk
      have hcomm : k * h = h * k :=
        (Subgroup.mem_centralizer_iff.mp hkC h hh).symm
      have heq : k * h * k⁻¹ = h := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact hh
    obtain ⟨h, hh, k, hk, hxeq⟩ := (mem_sup_iff_of_normalizes hnorm).mp hxsup
    have hkOK : k ∈ ctxOK t tau x₁ x₂ rho := by
      have hk_eq : k = h⁻¹ * x := by rw [hxeq]; group
      rw [hk_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (l18_tom_le_OK hc hh)) hxOK
    have hk1 : k = 1 := by
      have hN3 : Nat.card (zpowers rho : Subgroup G) = 3 := by
        rw [Nat.card_zpowers, hc.ord_rho]
      have hIntBot : (zpowers rho : Subgroup G) ⊓ ctxOK t tau x₁ x₂ rho = ⊥ := by
        have hdvd : Nat.card (↑((zpowers rho : Subgroup G) ⊓ ctxOK t tau x₁ x₂ rho)) ∣ 3 := by
          rw [← hN3]
          exact Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact Subgroup.eq_bot_of_card_eq _ h1
        · exfalso
          have hle : (zpowers rho : Subgroup G) ≤ ctxOK t tau x₁ x₂ rho := by
            have heq : ((zpowers rho : Subgroup G) ⊓ ctxOK t tau x₁ x₂ rho) =
                (zpowers rho : Subgroup G) := by
              refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
              rw [h3, hN3]
            intro y hy
            have hy' : y ∈ (zpowers rho : Subgroup G) ⊓ ctxOK t tau x₁ x₂ rho := by
              rw [heq]; exact hy
            exact (Subgroup.mem_inf.mp hy').2
          exact l18_rho_not_mem_OK hc (hle (Subgroup.mem_zpowers rho))
      have hkbot : k ∈ (zpowers rho : Subgroup G) ⊓ ctxOK t tau x₁ x₂ rho :=
        Subgroup.mem_inf.mpr ⟨hk, hkOK⟩
      rw [hIntBot] at hkbot
      exact Subgroup.mem_bot.mp hkbot
    rw [hxeq, hk1, mul_one]
    exact hh
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨l18_tom_le_OK hc hx, l18_tom_le_cent hc hx⟩

private theorem l18_tau_mem_cent_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau ∈ centralizer ({rho} : Set G) := by
  have hle : closure ({t, tau} : Set G) ≤ ctxR t tau x₁ x₂ ⊓ centralizer ({rho} : Set G) := by
    rw [hc.CR_rho]
  exact (Subgroup.mem_inf.mp (hle (Subgroup.subset_closure (by simp)))).2

private theorem l18_tauom_le_cent (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({tau, om} : Set G) ≤ centralizer ({rho} : Set G) := by
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact l18_tau_mem_cent_rho hc
  · exact (ctx13_T_facts hc).1 (Subgroup.subset_closure (by simp))

private theorem l18_tauom_le_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({tau, om} : Set G) ≤ ctxCY t tau x₁ x₂ rho :=
  le_trans le_sup_right (l18_QA_le_C hc)

private theorem l18_tau_mem_tom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    tau ∈ closure ({t, om} : Set G) := by
  obtain ⟨ht2, -, -, -, -, -, -⟩ := ctx13_relations hc
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  have hom : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have htt : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have hconj : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hom htt) (Subgroup.inv_mem _ hom)
  have hkey : tau = t * (om * t * om⁻¹) := by
    rw [hc.t_om, ← mul_assoc, ht2', one_mul]
  rw [hkey]
  exact Subgroup.mul_mem _ htt hconj

private theorem l18_t_mem_normalizer_tauom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    t ∈ Subgroup.normalizer (((closure ({tau, om} : Set G)) : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  refine Subgroup.closure_induction
    (p := fun n _ => t * n * t⁻¹ ∈ closure ({tau, om} : Set G)) ?_ ?_ ?_ ?_ hn
  · intro x hx
    rcases hx with hx | hx
    · subst x
      have hcomm : t * tau = tau * t := (ctx13_relations hc).2.2.2.2.2.1
      have heq : t * tau * t⁻¹ = tau := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [heq]
      exact Subgroup.subset_closure (by simp)
    · subst x
      have hom2 : om * om = 1 := by simpa [pow_two] using hc.om_sq
      have homi : om⁻¹ = om := inv_eq_of_mul_eq_one_right hom2
      have hcomm : t * tau = tau * t := (ctx13_relations hc).2.2.2.2.2.1
      have htτ : t * tau * t⁻¹ = tau := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      have h1 : t * om = om * (t * tau) := by
        have h := hc.t_om
        rw [homi] at h
        calc t * om = (om * om) * t * om := by rw [hom2, one_mul]
          _ = om * (om * t * om) := by group
          _ = om * (t * tau) := by rw [h]
      have heq : t * om * t⁻¹ = om * tau := by
        rw [h1, mul_assoc, htτ]
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · simpa using Subgroup.one_mem (closure ({tau, om} : Set G))
  · intro x y hx hy ihx ihy
    have heq : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x hx ih
    have heq : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [heq]
    exact Subgroup.inv_mem _ ih

private theorem l18_tom_eq_tauom_sup (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    closure ({t, om} : Set G) = closure ({tau, om} : Set G) ⊔ zpowers t := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · subst x
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    · subst x
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  · apply sup_le
    · rw [Subgroup.closure_le]
      intro x hx
      rcases hx with hx | hx
      · subst x
        exact l18_tau_mem_tom hc
      · subst x
        exact Subgroup.subset_closure (by simp)
    · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

theorem l18_C_cap_cent_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxCY t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) = closure {tau, om} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxC, hxCent⟩ := Subgroup.mem_inf.mp hx
    have hxOK : x ∈ ctxOK t tau x₁ x₂ rho := l18_C_le_OK hc hxC
    have hxCl : x ∈ closure ({t, om} : Set G) := by
      have hmem : x ∈ ctxOK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) :=
        Subgroup.mem_inf.mpr ⟨hxOK, hxCent⟩
      rwa [l18_OK_cap_cent_rho hc] at hmem
    have hxsup : x ∈ closure ({tau, om} : Set G) ⊔ zpowers t := by
      rw [l18_tom_eq_tauom_sup hc] at hxCl
      exact hxCl
    have hnorm : ∀ k ∈ zpowers t, ∀ h ∈ closure ({tau, om} : Set G),
        k * h * k⁻¹ ∈ closure ({tau, om} : Set G) := by
      intro k hk h hh
      have hkN : k ∈ Subgroup.normalizer
          (((closure ({tau, om} : Set G)) : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr (l18_t_mem_normalizer_tauom hc) hk
      exact (Subgroup.mem_normalizer_iff.mp hkN h).mp hh
    obtain ⟨h, hh, k, hk, hxeq⟩ := (mem_sup_iff_of_normalizes hnorm).mp hxsup
    have hhC : h ∈ ctxCY t tau x₁ x₂ rho := l18_tauom_le_C hc hh
    have hkC : k ∈ ctxCY t tau x₁ x₂ rho := by
      have hk_eq : k = h⁻¹ * x := by rw [hxeq]; group
      rw [hk_eq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) hxC
    have hkt : k = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
      have hper : t ^ (m % (2 : ℤ)) = k := by
        have h : t ^ (m % (orderOf t : ℤ)) = t ^ m := zpow_mod_orderOf t m
        have hcast : ((orderOf t : ℕ) : ℤ) = (2 : ℤ) := by
          rw [hc.hyp.ord_t]; norm_num
        rw [hcast] at h
        rw [h, hm]
      rcases Int.emod_two_eq_zero_or_one m with h0 | h1
      · rw [h0, zpow_zero] at hper
        exact hper.symm
      · rw [h1, zpow_one] at hper
        rw [← hper] at hkC
        exact absurd hkC (l18_t_not_mem_C hc)
    rw [hxeq, hkt, mul_one]
    exact hh
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨l18_tauom_le_C hc hx, l18_tauom_le_cent hc hx⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
