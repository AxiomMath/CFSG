module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzB0B

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}
  {q s : G}

theorem fzb_qs_conj_qsy (h : Ctx t L S x₁ x₂ lam rho tau) (hK : Nat.card (twoCore t) = 4)
    (hq : zpowers q = twoCore t) (hs : s = tau ∨ s = q * tau) (hsq : s * q * s⁻¹ = q⁻¹) :
    ∃ d ∈ invCent t, d * (q * s) * d⁻¹ = q * s * lam := by
  have hqK : q ∈ twoCore t := by rw [← hq]; exact Subgroup.mem_zpowers q
  have hqH : q ∈ invCent t := S4A.twoCore_le_invCent t hqK
  have htH : tau ∈ invCent t := h.le_invCent h.tau_mem
  have hq2 : q ^ 2 = t := (fzbs_q_facts h hK hq).2
  have hsH : s ∈ invCent t := by
    rcases hs with rfl | rfl
    · exact htH
    · exact (invCent t).mul_mem hqH htH
  have hlamS : lam ∈ S := by
    have h1 : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at h1
    exact h1.1
  have hlamL : lam ∈ L := by
    have h1 : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
    rw [← h.inf_eq] at h1
    exact h1.2
  have hlamH : lam ∈ invCent t := h.le_invCent hlamS
  have hlam2 : lam ^ 2 = 1 := by
    rw [← h.wreath.ord_lam]; exact pow_orderOf_eq_one lam
  have hqlam : q * lam = lam * q := fzb_K_comm_L h hqK hlamL
  have hslam : s * lam = lam * s := by
    rcases hs with rfl | rfl
    · exact h.tau_lam
    · calc (q * tau) * lam = q * (tau * lam) := by group
        _ = q * (lam * tau) := by rw [h.tau_lam]
        _ = (q * lam) * tau := by group
        _ = (lam * q) * tau := by rw [hqlam]
        _ = lam * (q * tau) := by group
  have hqslams : (q * s) * lam = lam * (q * s) := by
    calc (q * s) * lam = q * (s * lam) := by group
      _ = q * (lam * s) := by rw [hslam]
      _ = (q * lam) * s := by group
      _ = (lam * q) * s := by rw [hqlam]
      _ = lam * (q * s) := by group
  have htauq : tau * q * tau⁻¹ = q⁻¹ := by
    rcases hs with rfl | rfl
    · exact hsq
    · have h1 : q * (tau * q * tau⁻¹) * q⁻¹ = q⁻¹ := by
        calc q * (tau * q * tau⁻¹) * q⁻¹
            = (q * tau) * q * (q * tau)⁻¹ := by group
          _ = q⁻¹ := hsq
      calc tau * q * tau⁻¹ = q⁻¹ * (q * (tau * q * tau⁻¹) * q⁻¹) * q := by group
        _ = q⁻¹ * q⁻¹ * q := by rw [h1]
        _ = q⁻¹ := by group
  have hcommK : ∀ a ∈ twoCore t, ∀ b ∈ twoCore t, a * b = b * a := by
    haveI : IsCyclic (twoCore t) := h.hyp.isCyclic
    haveI : IsMulCommutative (twoCore t) := IsCyclic.isMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : twoCore t) ⟨b, hb⟩)
  have hqN : q ∈ twoCore t ⊔ L := Subgroup.mem_sup_left hqK
  have hlamN : lam ∈ twoCore t ⊔ L := Subgroup.mem_sup_right hlamL
  have hlamN' : lam ∈ zpowers t ⊔ L := Subgroup.mem_sup_right hlamL
  have hγ₁out : q * s ∉ twoCore t ⊔ L := by
    intro hmem
    have hsN : s ∈ twoCore t ⊔ L := by
      have h1 : q⁻¹ * (q * s) ∈ twoCore t ⊔ L :=
        (twoCore t ⊔ L).mul_mem ((twoCore t ⊔ L).inv_mem hqN) hmem
      simpa using h1
    rcases hs with rfl | rfl
    · exact h.tau_not_mem hsN
    · have h2 : tau ∈ twoCore t ⊔ L := by
        have h1 : q⁻¹ * (q * tau) ∈ twoCore t ⊔ L :=
          (twoCore t ⊔ L).mul_mem ((twoCore t ⊔ L).inv_mem hqN) hsN
        simpa using h1
      exact h.tau_not_mem h2
  have hγ₂out : q * s * lam ∉ twoCore t ⊔ L := by
    intro hmem
    have hqsmem : q * s ∈ twoCore t ⊔ L := by
      have h1 : (q * s * lam) * lam⁻¹ ∈ twoCore t ⊔ L :=
        (twoCore t ⊔ L).mul_mem hmem ((twoCore t ⊔ L).inv_mem hlamN)
      simpa using h1
    exact hγ₁out hqsmem
  have hssq : s ^ 2 ∈ twoCore t := by
    rcases hs with rfl | rfl
    · exact h.tau_sq_mem
    · have h2 : (q * tau) ^ 2 = tau ^ 2 := by
        calc (q * tau) ^ 2 = (q * tau) * (q * tau) := by rw [pow_two]
          _ = q * (tau * q * tau⁻¹) * (tau * tau) := by group
          _ = q * q⁻¹ * (tau * tau) := by rw [htauq]
          _ = tau * tau := by group
          _ = tau ^ 2 := by rw [pow_two]
      rw [h2]
      exact h.tau_sq_mem
  have hγ₁sq : (q * s) ^ 2 ∈ twoCore t := by
    have h2 : (q * s) ^ 2 = s ^ 2 := by
      calc (q * s) ^ 2 = q * s * (q * s) := by rw [pow_two]
        _ = q * (s * q * s⁻¹) * (s * s) := by group
        _ = q * q⁻¹ * (s * s) := by rw [hsq]
        _ = s * s := by group
        _ = s ^ 2 := by rw [pow_two]
    rw [h2]; exact hssq
  have hγ₂sq : (q * s * lam) ^ 2 ∈ twoCore t := by
    have h2 : (q * s * lam) ^ 2 = (q * s) ^ 2 := by
      calc (q * s * lam) ^ 2 = (q * s) ^ 2 * lam ^ 2 := Commute.mul_pow hqslams 2
        _ = (q * s) ^ 2 * 1 := by rw [hlam2]
        _ = (q * s) ^ 2 := by rw [mul_one]
    rw [h2]; exact hγ₁sq
  have hγ₁H : q * s ∈ invCent t := (invCent t).mul_mem hqH hsH
  have hγ₂H : q * s * lam ∈ invCent t := (invCent t).mul_mem hγ₁H hlamH
  obtain ⟨h₁, hh₁, p₁, hp₁, hconj₁⟩ := h.invol_outer (q * s) hγ₁H hγ₁out hγ₁sq
  obtain ⟨h₂, hh₂, p₂, hp₂, hconj₂⟩ := h.invol_outer (q * s * lam) hγ₂H hγ₂out hγ₂sq
  have hc₂mem : h₂ * (q * s * lam) * h₂⁻¹ * (q * s * lam)⁻¹ ∈ zpowers t ⊔ L :=
    fzb_comm_qs_mem h hK hq hs hsq hh₂ hlamL
  have hc₁mem : h₁ * (q * s) * h₁⁻¹ * (q * s)⁻¹ ∈ zpowers t ⊔ L := by
    have h1 := fzb_comm_qs_mem h hK hq hs hsq hh₁ (ℓ := 1) (Subgroup.one_mem L)
    simpa using h1
  have hγ₂γ₁ : (q * s * lam) * (q * s)⁻¹ = lam := by
    rw [mul_inv_rev]
    calc q * s * lam * (s⁻¹ * q⁻¹) = q * (s * lam * s⁻¹) * q⁻¹ := by group
      _ = q * lam * q⁻¹ := by rw [hslam]; group
      _ = lam := by rw [hqlam]; group
  have hmid : (q * s * lam)⁻¹ * lam * (q * s) = 1 := by
    rw [hqslams]; group
  have hp₂p₁_eq : p₂ * p₁⁻¹ =
      (h₂ * (q * s * lam) * h₂⁻¹ * (q * s * lam)⁻¹) * lam *
        (h₁ * (q * s) * h₁⁻¹ * (q * s)⁻¹)⁻¹ := by
    have hc₂ : h₂ * (q * s * lam) * h₂⁻¹ * (q * s * lam)⁻¹ =
        (p₂ * tau) * (q * s * lam)⁻¹ := by rw [hconj₂]
    have hc₁ : (h₁ * (q * s) * h₁⁻¹ * (q * s)⁻¹)⁻¹ =
        (q * s) * (p₁ * tau)⁻¹ := by rw [hconj₁, mul_inv_rev, inv_inv]
    rw [hc₂, hc₁]
    rw [show (p₂ * tau) * (q * s * lam)⁻¹ * lam * ((q * s) * (p₁ * tau)⁻¹)
        = (p₂ * tau) * ((q * s * lam)⁻¹ * lam * (q * s)) * (p₁ * tau)⁻¹ by group]
    rw [hmid, mul_one]
    group
  have hp₂p₁N : p₂ * p₁⁻¹ ∈ zpowers t ⊔ L := by
    rw [hp₂p₁_eq]
    exact (zpowers t ⊔ L).mul_mem ((zpowers t ⊔ L).mul_mem hc₂mem hlamN')
      ((zpowers t ⊔ L).inv_mem hc₁mem)
  have hp₂p₁K : p₂ * p₁⁻¹ ∈ twoCore t := (twoCore t).mul_mem hp₂ ((twoCore t).inv_mem hp₁)
  have hp : p₂ * p₁⁻¹ ∈ zpowers t := fzb_K_inf_N h hp₂p₁K hp₂p₁N
  have hcases : p₂ * p₁⁻¹ = 1 ∨ p₂ * p₁⁻¹ = t := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hmod : t ^ (k % (2 : ℤ)) = p₂ * p₁⁻¹ := by
      have hz := zpow_mod_orderOf t k
      rw [h.hyp.ord_t] at hz
      exact hz.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [← hmod, h0]; simp
    · right; rw [← hmod, h1]; simp
  rcases hcases with hcase | hcase
  · have hp₂p₁ : p₂ = p₁ := by
      calc p₂ = (p₂ * p₁⁻¹) * p₁ := by group
        _ = 1 * p₁ := by rw [hcase]
        _ = p₁ := by group
    refine ⟨h₂⁻¹ * h₁, (invCent t).mul_mem ((invCent t).inv_mem hh₂) hh₁, ?_⟩
    calc (h₂⁻¹ * h₁) * (q * s) * (h₂⁻¹ * h₁)⁻¹
        = h₂⁻¹ * (h₁ * (q * s) * h₁⁻¹) * h₂ := by group
      _ = h₂⁻¹ * (p₁ * tau) * h₂ := by rw [hconj₁]
      _ = h₂⁻¹ * (p₂ * tau) * h₂ := by rw [← hp₂p₁]
      _ = h₂⁻¹ * (h₂ * (q * s * lam) * h₂⁻¹) * h₂ := by rw [← hconj₂]
      _ = q * s * lam := by group
  · have hp₂p₁ : p₂ = t * p₁ := by
      calc p₂ = (p₂ * p₁⁻¹) * p₁ := by group
        _ = t * p₁ := by rw [hcase]
    have hp₁q : p₁ * q = q * p₁ := hcommK p₁ hp₁ q hqK
    have hp₁t : p₁ * t = t * p₁ := hcommK p₁ hp₁ t h.hyp.mem_twoCore
    have ht2 : t * t = 1 := by
      rw [← pow_two, ← h.hyp.ord_t]; exact pow_orderOf_eq_one t
    have htinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have htauq' : tau * q = q⁻¹ * tau := by
      calc tau * q = (tau * q * tau⁻¹) * tau := by group
        _ = q⁻¹ * tau := by rw [htauq]
    have h1 : q * tau = tau * q⁻¹ := by
      calc q * tau = (q * (tau * q)) * q⁻¹ := by group
        _ = (q * (q⁻¹ * tau)) * q⁻¹ := by rw [htauq']
        _ = tau * q⁻¹ := by group
    have hqq : q⁻¹ * q⁻¹ = t := by
      rw [show q⁻¹ * q⁻¹ = (q * q)⁻¹ by group, ← pow_two, hq2, htinvt]
    have hτt : tau * t = t * tau := by
      have hτt' : tau * t * tau⁻¹ = t := (fzbs_tau_facts h).2.1
      calc tau * t = (tau * t * tau⁻¹) * tau := by group
        _ = t * tau := by rw [hτt']
    have hqt : q * tau * q⁻¹ = t * tau := by
      rw [h1, mul_assoc, hqq]
      exact hτt
    have hqconj : q * (p₁ * tau) * q⁻¹ = p₂ * tau := by
      calc q * (p₁ * tau) * q⁻¹
          = (q * p₁ * q⁻¹) * (q * tau * q⁻¹) := by group
        _ = p₁ * (t * tau) := by rw [← hp₁q, hqt]; group
        _ = (p₁ * t) * tau := by group
        _ = (t * p₁) * tau := by rw [hp₁t]
        _ = t * p₁ * tau := by group
        _ = p₂ * tau := by rw [← hp₂p₁]
    refine ⟨h₂⁻¹ * q * h₁,
      (invCent t).mul_mem ((invCent t).mul_mem ((invCent t).inv_mem hh₂) hqH) hh₁, ?_⟩
    calc (h₂⁻¹ * q * h₁) * (q * s) * (h₂⁻¹ * q * h₁)⁻¹
        = h₂⁻¹ * (q * (h₁ * (q * s) * h₁⁻¹) * q⁻¹) * h₂ := by group
      _ = h₂⁻¹ * (q * (p₁ * tau) * q⁻¹) * h₂ := by rw [hconj₁]
      _ = h₂⁻¹ * (p₂ * tau) * h₂ := by rw [hqconj]
      _ = h₂⁻¹ * (h₂ * (q * s * lam) * h₂⁻¹) * h₂ := by rw [← hconj₂]
      _ = q * s * lam := by group

end CFSG.OddStandard.SmallF3.FritzII
