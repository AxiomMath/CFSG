module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511P

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

theorem E_le_H (hD : Foote5AutData 𝕊 Lin) (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    {s : G} (hsN : s ∈ normalizer (S : Set G)) (hss : s * s ∈ S)
    (hRs : S ⊓ L ⊓ conjugate (S ⊓ L) s = ⊥) (hz : z = s⁻¹ * t * s) {r : G}
    (hr : r ∈ conjugate (S ⊓ L) s) (hr2 : r * r = 1) (hrlin : actG L ε r ∉ Lin)
    {E : Subgroup G} (hES : E ≤ S) (hTE : T ≤ normalizer (E : Set G))
    (hEsq : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card E = 8) (htE : t ∈ E) (hzE : z ∈ E) :
    E ≤ (Q ⊔ zpowers r) ⊔ (conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹)) := by
  intro e he
  have heS := hES he
  by_cases hinn : actG L ε e ∈ innAut5 𝕊
  · obtain ⟨q, hq, ρ, hρ, rfl⟩ := h.exists_mul_of_inner ε heS hinn
    exact mul_mem (mem_sup_left (mem_sup_left hq)) (h.R_le_H ε hD hsN hss hRs hz hr hr2 hrlin hρ)
  · by_cases hlin : actG L ε e ∈ Lin
    · exact (h.false_of_pgl_mem_E ε hD hna hES hTE hEsq hE8 htE hzE he hlin hinn).elim
    · exact h.mem_H_of_not_lin ε hD hsN hss hRs hz hr hr2 hrlin heS (hEsq e he) hlin

theorem false_of_field_involution (hKF : Foote5FieldCentralizerC) (h𝕊 : FooteSimpleType 𝕊)
    (hD : Foote5AutData 𝕊 Lin) (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a)
    (hQ : 4 < Nat.card Q) (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T)
    (hsS : s ∉ S) (hz : z = s⁻¹ * t * s) {r : G} (hr : r ∈ conjugate (S ⊓ L) s)
    (hr2 : r * r = 1) (hrlin : actG L ε r ∉ Lin) {E : Subgroup G} (hES : E ≤ S)
    (hTE : T ≤ normalizer (E : Set G)) (hEsq : ∀ e ∈ E, e * e = 1) (hE8 : Nat.card E = 8)
    (htE : t ∈ E) (hzE : z ∈ E) : False := by
  classical
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have hzt := h.conj_t_eq_z hss hz
  have hst : s * t * s⁻¹ ≠ t := by rw [hzt]; exact h.z_ne_t
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hrinn : actG L ε r ∉ innAut5 𝕊 := fun h1 => hrlin (hD.inn_le h1)
  have hcard := h.card_centralizer_Q_le_two_of_field ε hKF h𝕊 hna hsN hRs hz hr hr2 hrinn
  have hrS : r ∈ S := conjugate_le_of_mem_normalizer hsN inf_le_left hr
  have hrQ : r ∉ Q := fun h1 => hrinn (by
    rw [(h.actG_eq_one_iff_mem_Q ε hrS).mpr h1]
    exact one_mem _)
  have hrz : r * z = z * r := h.zS r hrS
  obtain ⟨v₁, hv₁, htest₁⟩ := h.exists_test_Q_sup hQ hrS hr2 hrQ hrz hcard
  set D₁ := Q ⊔ zpowers r with hD₁
  set D₂ := conjugate Q s⁻¹ ⊔ zpowers (s * r * s⁻¹) with hD₂
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := fun x hx y hy =>
    h.commute_D₁_D₂ hQ hsT hsS hsN hss hRs hr hx hy
  have hD₂iff : ∀ x, x ∈ D₂ ↔ s⁻¹ * x * s ∈ D₁ := fun x => mem_D₂_iff
  have hstz : s * z * s⁻¹ = t := by rw [hz]; group
  have hv₂ : s * v₁ * s⁻¹ ∈ D₂ := by
    rw [hD₂iff, show s⁻¹ * (s * v₁ * s⁻¹) * s = v₁ by group]
    exact hv₁
  have htest₂ : ∀ b ∈ D₂, b * b = 1 →
      ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) *
        ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) = 1 → b = 1 ∨ b = t := by
    intro b hb hb2 hc2
    have hb' := (hD₂iff b).mp hb
    have hb'2 : (s⁻¹ * b * s) * (s⁻¹ * b * s) = 1 := by
      rw [show s⁻¹ * b * s * (s⁻¹ * b * s) = s⁻¹ * (b * b) * s by group, hb2]
      group
    have hc'2 : (v₁ * (s⁻¹ * b * s) * v₁⁻¹ * (s⁻¹ * b * s)⁻¹) *
        (v₁ * (s⁻¹ * b * s) * v₁⁻¹ * (s⁻¹ * b * s)⁻¹) = 1 := by
      have h1 : v₁ * (s⁻¹ * b * s) * v₁⁻¹ * (s⁻¹ * b * s)⁻¹ =
          s⁻¹ * ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) * s := by group
      rw [h1, show s⁻¹ * ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) * s *
          (s⁻¹ * ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) * s) =
          s⁻¹ * (((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹) *
            ((s * v₁ * s⁻¹) * b * (s * v₁ * s⁻¹)⁻¹ * b⁻¹)) * s by group, hc2]
      group
    rcases htest₁ _ hb' hb'2 hc'2 with h1 | h1
    · left
      calc b = s * (s⁻¹ * b * s) * s⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · right
      calc b = s * (s⁻¹ * b * s) * s⁻¹ := by group
        _ = t := by rw [h1, hstz]
  have hcenter : ∀ x ∈ D₁, x ∈ D₂ → x = 1 := by
    intro x hx1 hx2
    have hZ1 := h.mem_center_D₁ hQ hrS hr2 hrz hcard hx1 fun y hy => (hcomm y hy x hx2).symm
    have hx2' := (hD₂iff x).mp hx2
    have hZ2 := h.mem_center_D₁ hQ hrS hr2 hrz hcard hx2' fun y hy => by
      have h1 := hcomm x hx1 (s * y * s⁻¹)
        ((hD₂iff _).mpr (by rw [show s⁻¹ * (s * y * s⁻¹) * s = y by group]; exact hy))
      calc s⁻¹ * x * s * y = s⁻¹ * (x * (s * y * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * y * s⁻¹) * x) * s := by rw [h1]
        _ = y * (s⁻¹ * x * s) := by group
    rcases hZ1 with h1 | h1
    · exact h1
    · exfalso
      rcases hZ2 with h2 | h2
      · rw [h1] at h2
        have hz1 : z ≠ 1 := fun h3 => by
          have := h.z2
          rw [h3, orderOf_one] at this
          omega
        apply hz1
        calc z = s * (s⁻¹ * z * s) * s⁻¹ := by group
          _ = 1 := by rw [h2]; group
      · rw [h1] at h2
        apply h.z_ne_t
        calc z = s * (s⁻¹ * z * s) * s⁻¹ := by group
          _ = s * z * s⁻¹ := by rw [h2]
          _ = t := hstz
  have hEH := h.E_le_H ε hD hna hsN hss hRs hz hr hr2 hrlin hES hTE hEsq hE8 htE hzE
  have hEzt : ∀ e ∈ E, e ∈ ({z * t, z, t, 1} : Finset G) := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_commute hcomm (hEH he)
    have hab := hcomm a ha b hb
    have haa : a * a = 1 := by
      have h1 : (a * a) * (b * b) = 1 := by
        rw [← hEsq _ he, show a * b * (a * b) = a * (b * a) * b by group, ← hab]
        group
      have h2 : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hcenter _ (mul_mem ha ha) (h2 ▸ inv_mem (mul_mem hb hb))
    have hbb : b * b = 1 := by
      have h1 : (a * a) * (b * b) = 1 := by
        rw [← hEsq _ he, show a * b * (a * b) = a * (b * a) * b by group, ← hab]
        group
      rwa [haa, one_mul] at h1
    have hv₁S : v₁ ∈ S := (sup_le h.QS (zpowers_le.mpr hrS)) hv₁
    have hv₂S : s * v₁ * s⁻¹ ∈ S := (mem_normalizer_iff.mp hsN v₁).mp hv₁S
    have hcE : ∀ v ∈ S, v * (a * b) * v⁻¹ * (a * b)⁻¹ ∈ E := fun v hv =>
      mul_mem ((mem_normalizer_iff.mp (hTE (h.ST hv)) _).mp he) (inv_mem he)
    have hc₁ : v₁ * (a * b) * v₁⁻¹ * (a * b)⁻¹ = v₁ * a * v₁⁻¹ * a⁻¹ := by
      have h1 := hcomm v₁ hv₁ b hb
      calc v₁ * (a * b) * v₁⁻¹ * (a * b)⁻¹ = v₁ * a * (b * v₁⁻¹) * b⁻¹ * a⁻¹ := by group
        _ = v₁ * a * (v₁⁻¹ * b) * b⁻¹ * a⁻¹ := by
            rw [show b * v₁⁻¹ = v₁⁻¹ * b by
              calc b * v₁⁻¹ = v₁⁻¹ * (v₁ * b) * v₁⁻¹ := by group
                _ = v₁⁻¹ * (b * v₁) * v₁⁻¹ := by rw [h1]
                _ = v₁⁻¹ * b := by group]
        _ = v₁ * a * v₁⁻¹ * a⁻¹ := by group
    set v₂ := s * v₁ * s⁻¹ with hv₂def
    have hcb : v₂ * b * v₂⁻¹ * b⁻¹ ∈ D₂ :=
      mul_mem (mul_mem (mul_mem hv₂ hb) (inv_mem hv₂)) (inv_mem hb)
    have hc₂ : v₂ * (a * b) * v₂⁻¹ * (a * b)⁻¹ = v₂ * b * v₂⁻¹ * b⁻¹ := by
      have h1 := hcomm a ha v₂ hv₂
      have h2 := hcomm a ha _ hcb
      calc v₂ * (a * b) * v₂⁻¹ * (a * b)⁻¹ = (v₂ * a) * b * v₂⁻¹ * b⁻¹ * a⁻¹ := by group
        _ = a * v₂ * b * v₂⁻¹ * b⁻¹ * a⁻¹ := by rw [← h1]
        _ = (a * (v₂ * b * v₂⁻¹ * b⁻¹)) * a⁻¹ := by group
        _ = ((v₂ * b * v₂⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [h2]
        _ = v₂ * b * v₂⁻¹ * b⁻¹ := by group
    have ha' := htest₁ a ha haa (by rw [← hc₁]; exact hEsq _ (hcE v₁ hv₁S))
    have hb' := htest₂ b hb hbb (by rw [← hc₂]; exact hEsq _ (hcE v₂ hv₂S))
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl <;> simp
  have h4 := (SmallLocal.card_le_of_forall_mem_finset ({z * t, z, t, 1} : Finset G) hEzt).trans
    Finset.card_le_four
  omega

end Sec5

end CFSG.ComponentClassification.Foote5
