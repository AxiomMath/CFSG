module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511B

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

theorem conjugate_R_le_of_involutions {s : G} {J : Subgroup G}
    (hJ : ∀ b ∈ conjugate (S ⊓ L) s, b * b = 1 → b ∈ J) : conjugate (S ⊓ L) s ≤ J := by
  obtain ⟨m, -, ⟨e⟩⟩ := h.exists_dihedral_R
  intro b hb
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁2, ha₂2, hab⟩ := exists_mul_of_dihedral e (mem_conjugate_iff.mp hb)
  have hconj : ∀ a ∈ S ⊓ L, s⁻¹ * a * s ∈ conjugate (S ⊓ L) s := fun a ha => by
    rw [mem_conjugate_iff, show s * (s⁻¹ * a * s) * s⁻¹ = a by group]
    exact ha
  have hsq : ∀ a : G, a * a = 1 → s⁻¹ * a * s * (s⁻¹ * a * s) = 1 := fun a ha => by
    rw [show s⁻¹ * a * s * (s⁻¹ * a * s) = s⁻¹ * (a * a) * s by group, ha]
    group
  have h1 : b = (s⁻¹ * a₁ * s) * (s⁻¹ * a₂ * s) := by
    calc b = s⁻¹ * (s * b * s⁻¹) * s := by group
      _ = s⁻¹ * (a₁ * a₂) * s := by rw [hab]
      _ = (s⁻¹ * a₁ * s) * (s⁻¹ * a₂ * s) := by group
  rw [h1]
  exact mul_mem (hJ _ (hconj a₁ ha₁) (hsq a₁ ha₁2)) (hJ _ (hconj a₂ ha₂) (hsq a₂ ha₂2))

include ε in
theorem cases_of_not_le_Q (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    (∃ r ∈ conjugate (S ⊓ L) s, r * r = 1 ∧ actG L ε r ∉ Lin) ∨
      ∀ b ∈ conjugate (S ⊓ L) s, b ∈ Q ∨ b * t ∈ Q := by
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hst : s * t * s⁻¹ ≠ t := fun h1 => hsS (hCt s hsT (by
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h1]))
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hRsS : conjugate (S ⊓ L) s ≤ S := conjugate_le_of_mem_normalizer hsN inf_le_left
  have hnaR : ∃ a ∈ (h.Rbar ε : Subgroup 𝕊), ∃ b ∈ (h.Rbar ε : Subgroup 𝕊), a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hna
    exact ⟨_, h.psi_mem_Rbar ε ha, _, h.psi_mem_Rbar ε hb,
      fun h1 => hab ((h.psi_comm_iff ε ha hb).mp h1)⟩
  have hht := h.tS
  have hlin : ∀ b ∈ conjugate (S ⊓ L) s, actG L ε b ∈ Lin → b ∈ Q ∨ b * t ∈ Q := by
    intro b hb hbl
    have hbS := hRsS hb
    have hbN := h.S_le hbS
    have hfix : ∀ ρ ∈ (h.Rbar ε : Subgroup 𝕊), actG L ε b ρ = ρ :=
      (h.actG_fix_iff ε hbS).mpr fun r hr =>
        h.commute_of_inf_conjugate_eq_bot hsN hRs hr hb
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.isPGroup_S) ⟨b, hbS⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨c, hcR, hcZ, hc⟩ := hD.centralizer_sylow_lin (h.Rbar ε) hnaR _ hbl
      ⟨k, by rw [← actG_pow ε hbN, ← hk, pow_orderOf_eq_one, actG_one]⟩ hfix
    obtain ⟨r, hr, rfl⟩ := (h.mem_Rbar_iff ε).mp hcR
    have hrZ : ∀ r' ∈ S ⊓ L, (r : G) * r' = r' * r := fun r' hr' =>
      (h.psi_comm_iff ε hr hr').mp (hcZ _ (h.psi_mem_Rbar ε hr'))
    rcases h.center_R hna hr hrZ with h1 | h1
    · left
      have hr1 : r = 1 := Subtype.ext h1
      rw [hr1, map_one, map_one] at hc
      exact (h.actG_eq_one_iff_mem_Q ε hbS).mp hc
    · right
      have hrt : r = ⟨t, h.tL⟩ := Subtype.ext h1
      rw [hrt, ← actG_of_mem_self ε h.tL] at hc
      have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
      rw [← h.actG_eq_one_iff_mem_Q ε (mul_mem hbS hht), actG_mul ε hbN (h.S_le hht), hc,
        ← actG_mul ε (h.S_le hht) (h.S_le hht), ht22, actG_one]
  by_cases hall : ∀ r ∈ conjugate (S ⊓ L) s, r * r = 1 → actG L ε r ∈ Lin
  · right
    have hsub : conjugate (S ⊓ L) s ≤ Q ⊔ zpowers t := h.conjugate_R_le_of_involutions
      fun b hb hb2 => by
        rcases hlin b hb (hall b hb hb2) with h1 | h1
        · exact mem_sup_left h1
        · rw [show b = b * t * t⁻¹ by group]
          exact mul_mem (mem_sup_left h1) (inv_mem (mem_sup_right (mem_zpowers t)))
    intro b hb
    have hcomm : ∀ q ∈ Q, ∀ y ∈ zpowers t, q * y = y * q := by
      intro q hq y hy
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (h.commute_Q_R hq h.tR) i).eq
    obtain ⟨q, hq, y, hy, rfl⟩ := exists_mul_of_mem_sup_commute hcomm (hsub hb)
    have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
    rcases eq_one_or_eq_of_mem_zpowers_sq ht22 hy with rfl | rfl
    · left
      rw [mul_one]
      exact hq
    · right
      rw [mul_assoc, ht22, mul_one]
      exact hq
  · left
    push Not at hall
    obtain ⟨r, hr, hr2, hrl⟩ := hall
    exact ⟨r, hr, hr2, hrl⟩

end Sec5

end CFSG.ComponentClassification.Foote5
