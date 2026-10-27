module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BT

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho q : G}

private theorem fzc_sy3_cocycle (q x y : G) :
    q * (x * y) * q⁻¹ * (x * y)⁻¹ =
      (q * x * q⁻¹ * x⁻¹) * (x * (q * y * q⁻¹ * y⁻¹) * x⁻¹) := by
  group

theorem fzc_sy3_Wp_le_P (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (ht : t ∈ fzP t x₁ x₂ rho) : baseGrp x₁ x₂ ⊔ zpowers t ≤ fzP t x₁ x₂ rho :=
  sup_le (fzc_sy3_E_le_P h hq) (zpowers_le.2 ht)

theorem fzc_sy3_P_W (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ p ∈ fzP t x₁ x₂ rho, p ∈ ctxW t x₁ x₂ → p ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro p hp hpW
  rcases fzc_sy3_W_cos h hK hq4 hqt p hpW with h1 | h1
  · exact h1
  · exfalso
    apply fzc_sy3_q_notin_P h hq hK hq4 hqt
    have e : q = p * (q⁻¹ * p)⁻¹ := by group
    rw [e]
    exact mul_mem hp (inv_mem (fzc_sy3_Wp_le_P h hq ht h1))

theorem fzc_sy3_R_cos (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ r ∈ fzR t x₁ x₂, r ∈ fzP t x₁ x₂ rho ∨ r * q⁻¹ ∈ fzP t x₁ x₂ rho := by
  intro r hr
  have hqR : q ∈ fzR t x₁ x₂ := hq.W_le_R (fzc_sy3_q_mem_W hK)
  have hR : fzR t x₁ x₂ = fzP t x₁ x₂ rho ⊔ zpowers q := by rw [hq.R_eq_PK, hK]
  rw [hR] at hr
  have hqq : q * q ∈ fzP t x₁ x₂ rho := by rw [← pow_two, hqt]; exact ht
  obtain ⟨p, hp, rfl | rfl⟩ :=
    (mem_sup_zpowers_sq hqq (fun x hx => hq.P_normal_R q hqR x hx)).1 hr
  · exact Or.inl hp
  · right
    rw [mul_inv_cancel_right]
    exact hp

theorem fzc_sy3_card_P (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    Nat.card (fzP t x₁ x₂ rho) = 4 * Nat.card ↥(baseGrp x₁ x₂ ⊔ zpowers t) := by
  have hqR : q ∈ fzR t x₁ x₂ := hq.W_le_R (fzc_sy3_q_mem_W hK)
  have hqq : q * q ∈ fzP t x₁ x₂ rho := by rw [← pow_two, hqt]; exact ht
  have h1 := card_sup_zpowers_sq hqq (fun x hx => hq.P_normal_R q hqR x hx)
    (fzc_sy3_q_notin_P h hq hK hq4 hqt)
  rw [← hK, ← hq.R_eq_PK, hq.card_R, hq.card_W, hK, Nat.card_zpowers, hq4] at h1
  rw [fzc_sy3_card_Wp h]
  omega

theorem fzc_sy3_P_rho_eq (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ⁅fzP t x₁ x₂ rho, zpowers rho⁆ = fzP t x₁ x₂ rho := by
  have hc : Commute q rho := Commute.symm (fzc_sy3_q_rho h hK)
  apply le_antisymm
  · calc ⁅fzP t x₁ x₂ rho, zpowers rho⁆ ≤ ⁅fzR t x₁ x₂, zpowers rho⁆ :=
          Subgroup.commutator_mono_left (fzc_sy3_P_le_R hq)
      _ = fzP t x₁ x₂ rho := (fzc_sy3_P_eq hq).symm
  · calc fzP t x₁ x₂ rho = ⁅fzR t x₁ x₂, zpowers rho⁆ := fzc_sy3_P_eq hq
      _ ≤ ⁅fzP t x₁ x₂ rho, zpowers rho⁆ := by
        rw [Subgroup.commutator_le]
        intro r hr g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have hqg : q * rho ^ k = rho ^ k * q := (hc.zpow_right k).eq
        rcases fzc_sy3_R_cos hq hK hqt ht r hr with hp | hp
        · exact Subgroup.commutator_mem_commutator hp hg
        · have e : ⁅r, rho ^ k⁆ = ⁅r * q⁻¹, rho ^ k⁆ := by
            simp only [commutatorElement_def]
            calc r * rho ^ k * r⁻¹ * (rho ^ k)⁻¹
                = r * q⁻¹ * (q * rho ^ k) * r⁻¹ * (rho ^ k)⁻¹ := by group
              _ = r * q⁻¹ * (rho ^ k * q) * r⁻¹ * (rho ^ k)⁻¹ := by rw [hqg]
              _ = r * q⁻¹ * rho ^ k * (r * q⁻¹)⁻¹ * (rho ^ k)⁻¹ := by group
          rw [e]
          exact Subgroup.commutator_mem_commutator hp hg

theorem fzc_sy3_rho_PWp (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ p ∈ fzP t x₁ x₂ rho, rho * p * rho⁻¹ * p⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t →
      p ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
  intro p hp h1
  exact fzc_sy3_P_W h hq hK hq4 hqt ht p hp
    (fzc_sy3_rho_RW h hq p (fzc_sy3_P_le_R hq hp) (fzc_sy3_Wp_le_W h h1))

theorem fzc_sy3_P_sq (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ p ∈ fzP t x₁ x₂ rho, p ∉ baseGrp x₁ x₂ ⊔ zpowers t → p ^ 2 * t ∈ baseGrp x₁ x₂ := by
  intro p hp hpW
  by_contra hne
  have hpR := fzc_sy3_P_le_R hq hp
  have hnE := fzc_sy3_R_nrm_E h hq hK hq4 hqt
  have hp2 : p ^ 2 ∈ baseGrp x₁ x₂ := by
    have h1 : p ^ 2 ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
      rw [pow_two]
      exact fzc_sy3_R_sq h hq hK hq4 hqt p hpR
    rcases (fzc_sy3_Wp_mem h).1 h1 with h2 | h2
    · exact h2
    · exact absurd (show p ^ 2 * t ∈ baseGrp x₁ x₂ by rw [fzc_sy3_t_comm_tE h h2]; exact h2) hne
  have key : ∀ s ∈ fzR t x₁ x₂, s ^ 2 ∈ baseGrp x₁ x₂ → ∀ g : G,
      g * s⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t → g ^ 2 ∈ baseGrp x₁ x₂ := by
    intro s hs hs2 g hg
    have h1 := fzc_sy3_sq_coset h hq hK hq4 hqt s hs _ hg
    rw [inv_mul_cancel_right] at h1
    have e : g ^ 2 = g ^ 2 * (s ^ 2)⁻¹ * s ^ 2 := by group
    rw [e]
    exact mul_mem (S4A.pt_four_le_base x₁ x₂ h1) hs2
  have hsq : ∀ g ∈ fzP t x₁ x₂ rho, g ^ 2 ∈ baseGrp x₁ x₂ := by
    intro g hg
    rcases fzc_sy3_rho_cosets (fzc_sy3_Wp_le_P h hq ht) (fzc_sy3_card_P h hq hK hq4 hqt ht)
      (fun r hr w hw => fzc_sy3_R_Wp h hq hK hq4 hqt r (fzc_sy3_P_le_R hq hr) w hw)
      (fun r hr => by rw [pow_two]; exact fzc_sy3_R_sq h hq hK hq4 hqt r (fzc_sy3_P_le_R hq hr))
      (fun a ha b hb => by
        rw [commutatorElement_def]
        exact fzc_sy3_R_comm h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) b (fzc_sy3_P_le_R hq hb))
      hq.rho_norm_P (fzc_sy3_rho_Wp h) (fzc_sy3_rho3 h) (fzc_sy3_rho_PWp h hq hK hq4 hqt ht)
      hp hpW g hg with hg1 | hg1 | hg1 | hg1
    · exact key 1 (one_mem _) (by rw [one_pow]; exact one_mem _) g (by rwa [inv_one, mul_one])
    · exact key p hpR hp2 g hg1
    · refine key _ (hq.rho_norm_R p hpR) ?_ g hg1
      rw [show (rho * p * rho⁻¹) ^ 2 = rho * p ^ 2 * rho⁻¹ by simp only [pow_two]; group]
      exact fzc_sy2_rho_nrm_E h _ hp2
    · refine key _ ?_ ?_ g hg1
      · rw [fzc_sy3_rho_inv_conj h]
        exact hq.rho_norm_R _ (hq.rho_norm_R p hpR)
      · rw [show (rho⁻¹ * p * rho) ^ 2 = rho⁻¹ * p ^ 2 * rho by simp only [pow_two]; group,
          fzc_sy3_rho_inv_conj h]
        exact fzc_sy2_rho_nrm_E h _ (fzc_sy2_rho_nrm_E h _ hp2)
  have hab : ∀ a ∈ fzP t x₁ x₂ rho, ∀ b ∈ fzP t x₁ x₂ rho,
      a * b * a⁻¹ * b⁻¹ ∈ baseGrp x₁ x₂ := by
    intro a ha b hb
    have e : a * b * a⁻¹ * b⁻¹ = (a * b) ^ 2 * (b⁻¹ * (a ^ 2)⁻¹ * b⁻¹⁻¹) * (b ^ 2)⁻¹ := by
      simp only [pow_two]; group
    rw [e]
    refine mul_mem (mul_mem (hsq _ (mul_mem ha hb)) ?_) (inv_mem (hsq b hb))
    exact hnE _ (fzc_sy3_P_le_R hq (inv_mem hb)) _ (inv_mem (hsq a ha))
  have h3 := fzc_sy3_norm_fix (R := fzP t x₁ x₂ rho) (N := baseGrp x₁ x₂)
    (fzc_sy3_E_le_P h hq) (fun r hr e he => hnE r (fzc_sy3_P_le_R hq hr) e he) hq.rho_norm_P
    (fzc_sy2_rho_nrm_E h) hab (fzc_sy3_rho3 h)
    (by rw [fzc_sy3_P_rho_eq h hq hK hqt ht]; exact ht) (fzc_sy3_rho_comm_t h)
  rw [pow_succ, fzc_sy2_t_sq h, one_mul] at h3
  exact fzc_sy2_t_notin_E h h3

theorem fzc_sy3_P_comm_tE (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ x ∈ fzP t x₁ x₂ rho, ∀ y ∈ fzP t x₁ x₂ rho, x ∉ baseGrp x₁ x₂ ⊔ zpowers t →
      y ∉ baseGrp x₁ x₂ ⊔ zpowers t → x * y⁻¹ ∉ baseGrp x₁ x₂ ⊔ zpowers t →
        x * y * x⁻¹ * y⁻¹ ∉ baseGrp x₁ x₂ := by
  intro x hx y hy hxW hyW hxy hc
  have hyR := fzc_sy3_P_le_R hq hy
  have hxyW : x * y ∉ baseGrp x₁ x₂ ⊔ zpowers t := by
    intro h'
    apply hxy
    have e : x * y⁻¹ = (x * y) * (y * y)⁻¹ := by group
    rw [e]
    exact mul_mem h' (inv_mem (fzc_sy3_R_sq h hq hK hq4 hqt y hyR))
  have hsq := fzc_sy3_P_sq h hq hK hq4 hqt ht
  have h1 : t * (x * y) ^ 2 ∈ baseGrp x₁ x₂ := by
    have h0 := hsq _ (mul_mem hx hy) hxyW
    rw [← fzc_sy3_t_comm_Et h h0]
    exact h0
  have h2 : t * x ^ 2 ∈ baseGrp x₁ x₂ := by
    have h0 := hsq x hx hxW
    rw [← fzc_sy3_t_comm_Et h h0]
    exact h0
  have h3 : t * y ^ 2 ∈ baseGrp x₁ x₂ := by
    have h0 := hsq y hy hyW
    rw [← fzc_sy3_t_comm_Et h h0]
    exact h0
  have h4 : (y * x ^ 2 * y⁻¹) * y ^ 2 ∈ baseGrp x₁ x₂ :=
    fzc_sy3_tE_mul h (fzc_sy3_R_tE h hq hK hq4 hqt y hyR _ h2) h3
  have h5 : (x * y) ^ 2 ∈ baseGrp x₁ x₂ := by
    have e : (x * y) ^ 2 = (x * y * x⁻¹ * y⁻¹) * ((y * x ^ 2 * y⁻¹) * y ^ 2) := by
      simp only [pow_two]; group
    rw [e]
    exact mul_mem hc h4
  have h6 := mul_mem h1 (inv_mem h5)
  rw [mul_inv_cancel_right] at h6
  exact fzc_sy2_t_notin_E h h6

private theorem fzc_sy3_K_P_q (h : Ctx0 t L S x₁ x₂ lam rho)
    (hq : FzCQFacts t S x₁ x₂ lam rho) (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4)
    (hqt : q ^ 2 = t) (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ p ∈ fzP t x₁ x₂ rho, q * p * q⁻¹ * p⁻¹ ∈ baseGrp x₁ x₂ := by
  have hqR : q ∈ fzR t x₁ x₂ := hq.W_le_R (fzc_sy3_q_mem_W hK)
  have hrq : rho * q = q * rho := fzc_sy3_q_rho h hK
  have hR := fzc_sy3_R_tE h hq hK hq4 hqt
  have hcW : ∀ x ∈ fzP t x₁ x₂ rho, q * x * q⁻¹ * x⁻¹ ∈ baseGrp x₁ x₂ ⊔ zpowers t := by
    intro x hx
    refine fzc_sy3_P_W h hq hK hq4 hqt ht _
      (mul_mem (hq.P_normal_R q hqR x hx) (inv_mem hx)) ?_
    have e : q * x * q⁻¹ * x⁻¹ = q * (x * q⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (fzc_sy3_q_mem_W hK)
      (fzc_sy3_R_W x (fzc_sy3_P_le_R hq hx) _ (inv_mem (fzc_sy3_q_mem_W hK)))
  intro p hp
  by_contra hne
  have hpR := fzc_sy3_P_le_R hq hp
  have hp₂ : rho * p * rho⁻¹ ∈ fzR t x₁ x₂ := hq.rho_norm_R p hpR
  have hc₁ : t * (q * p * q⁻¹ * p⁻¹) ∈ baseGrp x₁ x₂ :=
    ((fzc_sy3_Wp_mem h).1 (hcW p hp)).resolve_left hne
  have hc₂ : t * (q * (rho * p * rho⁻¹) * q⁻¹ * (rho * p * rho⁻¹)⁻¹) ∈ baseGrp x₁ x₂ := by
    have e : q * (rho * p * rho⁻¹) * q⁻¹ * (rho * p * rho⁻¹)⁻¹ =
        rho * (q * p * q⁻¹ * p⁻¹) * rho⁻¹ := by
      calc q * (rho * p * rho⁻¹) * q⁻¹ * (rho * p * rho⁻¹)⁻¹
          = (q * rho) * p * (q * rho)⁻¹ * (rho * p⁻¹ * rho⁻¹) := by group
        _ = (rho * q) * p * (rho * q)⁻¹ * (rho * p⁻¹ * rho⁻¹) := by rw [← hrq]
        _ = rho * (q * p * q⁻¹ * p⁻¹) * rho⁻¹ := by group
    rw [e]
    exact fzc_sy3_rho_tE h hc₁
  have hqri : q * rho⁻¹ = rho⁻¹ * q := by
    calc q * rho⁻¹ = rho⁻¹ * (rho * q) * rho⁻¹ := by group
      _ = rho⁻¹ * (q * rho) * rho⁻¹ := by rw [hrq]
      _ = rho⁻¹ * q := by group
  have hc₃ : t * (q * (rho⁻¹ * p * rho) * q⁻¹ * (rho⁻¹ * p * rho)⁻¹) ∈ baseGrp x₁ x₂ := by
    have e : q * (rho⁻¹ * p * rho) * q⁻¹ * (rho⁻¹ * p * rho)⁻¹ =
        rho⁻¹ * (q * p * q⁻¹ * p⁻¹) * rho := by
      calc q * (rho⁻¹ * p * rho) * q⁻¹ * (rho⁻¹ * p * rho)⁻¹
          = (q * rho⁻¹) * p * (q * rho⁻¹)⁻¹ * (rho⁻¹ * p⁻¹ * rho) := by group
        _ = (rho⁻¹ * q) * p * (rho⁻¹ * q)⁻¹ * (rho⁻¹ * p⁻¹ * rho) := by rw [hqri]
        _ = rho⁻¹ * (q * p * q⁻¹ * p⁻¹) * rho := by group
    rw [e, fzc_sy3_rho_inv_conj h]
    exact fzc_sy3_rho_tE h (fzc_sy3_rho_tE h hc₁)
  have hc₁₂ : q * (p * (rho * p * rho⁻¹)) * q⁻¹ * (p * (rho * p * rho⁻¹))⁻¹ ∈
      baseGrp x₁ x₂ := by
    rw [fzc_sy3_cocycle q p (rho * p * rho⁻¹)]
    exact fzc_sy3_tE_mul h hc₁ (hR p hpR _ hc₂)
  have hn : t * (q * (p * (rho * p * rho⁻¹) * (rho⁻¹ * p * rho)) * q⁻¹ *
      (p * (rho * p * rho⁻¹) * (rho⁻¹ * p * rho))⁻¹) ∈ baseGrp x₁ x₂ := by
    rw [fzc_sy3_cocycle q (p * (rho * p * rho⁻¹)) (rho⁻¹ * p * rho)]
    exact fzc_sy3_E_tE h hc₁₂ (hR _ (mul_mem hpR hp₂) _ hc₃)
  have hnorm := fzc_sy3_norm (R := fzP t x₁ x₂ rho) (N := baseGrp x₁ x₂ ⊔ zpowers t)
    (fzc_sy3_Wp_le_P h hq ht)
    (fun r hr n hn => fzc_sy3_R_Wp h hq hK hq4 hqt r (fzc_sy3_P_le_R hq hr) n hn)
    hq.rho_norm_P (fzc_sy3_rho_Wp h)
    (fun a ha b hb =>
      fzc_sy3_R_comm h hq hK hq4 hqt a (fzc_sy3_P_le_R hq ha) b (fzc_sy3_P_le_R hq hb))
    (fzc_sy3_rho3 h) p (by rw [fzc_sy3_P_rho_eq h hq hK hqt ht]; exact hp)
  rw [fzc_sy3_q_comm_W h hK _ (fzc_sy3_Wp_le_W h hnorm), mul_inv_cancel_right,
    mul_inv_cancel, mul_one] at hn
  exact fzc_sy2_t_notin_E h hn

theorem fzc_sy3_K_P (h : Ctx0 t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hK : twoCore t = zpowers q) (hq4 : orderOf q = 4) (hqt : q ^ 2 = t)
    (ht : t ∈ fzP t x₁ x₂ rho) :
    ∀ k ∈ zpowers q, ∀ p ∈ fzP t x₁ x₂ rho, k * p * k⁻¹ * p⁻¹ ∈ baseGrp x₁ x₂ := by
  classical
  have hq1 := fzc_sy3_K_P_q h hq hK hq4 hqt ht
  have hpow : ∀ m : ℕ, ∀ p ∈ fzP t x₁ x₂ rho, q ^ m * p * (q ^ m)⁻¹ * p⁻¹ ∈ baseGrp x₁ x₂ := by
    intro m
    induction m with
    | zero => intro p _; simp
    | succ m ih =>
      intro p hp
      have e : q ^ (m + 1) * p * (q ^ (m + 1))⁻¹ * p⁻¹ =
          q * (q ^ m * p * (q ^ m)⁻¹ * p⁻¹) * q⁻¹ * (q * p * q⁻¹ * p⁻¹) := by group
      rw [e]
      refine mul_mem ?_ (hq1 p hp)
      rw [fzc_sy3_q_comm_W h hK _ (mem_sup_right (ih p hp)), mul_inv_cancel_right]
      exact ih p hp
  intro k hk p hp
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hk
  obtain ⟨m, -, rfl⟩ := hk
  exact hpow m p hp

end CFSG.OddStandard.SmallF3.FritzII
