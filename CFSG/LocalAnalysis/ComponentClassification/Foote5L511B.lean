module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511A

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_card_eq_two_mul {S T : Subgroup G} (hST : S ≤ T)
    (hcard : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) :
    s ∈ normalizer (S : Set G) := by
  have key : ∀ y ∈ T, ∀ x ∈ S, y * x * y⁻¹ ∈ S := by
    intro y hy x hx
    by_cases hyS : y ∈ S
    · exact mul_mem (mul_mem hyS hx) (inv_mem hyS)
    · refine mul_mem_of_card_eq_two_mul hST hcard (mul_mem hy (hST hx)) (inv_mem hy) ?_ ?_
      · intro h1
        exact hyS (by simpa using mul_mem h1 (inv_mem hx))
      · intro h1
        exact hyS (by simpa using inv_mem h1)
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key s hsT x hx, fun hx => ?_⟩
  have h1 := key s⁻¹ (inv_mem hsT) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at h1

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

include ε in
theorem conj_t_mem_Q (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    s⁻¹ * t * s ∈ Q := by
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hst : s * t * s⁻¹ ≠ t := fun h1 => hsS (hCt s hsT (by
    calc s * t = s * t * s⁻¹ * s := by group
      _ = t * s := by rw [h1]))
  have hRs := h.inf_conjugate_R_eq_bot hna hsN hst
  have hRsS : conjugate (S ⊓ L) s ≤ S := conjugate_le_of_mem_normalizer hsN inf_le_left
  have hle : ⁅conjugate (S ⊓ L) s, conjugate (S ⊓ L) s⁆ ≤ Q := by
    rw [commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.commutator_mem_Q_of_centralizes ε hD hRsS
      (fun b hb r hr => h.commute_of_inf_conjugate_eq_bot hsN hRs hr hb) hx hy
  have h1 := conj_mem_commutator_conjugate (a := s⁻¹) (h.t_mem_commutator_R ε hD hna)
  rw [inv_inv] at h1
  exact hle h1

include ε in
theorem exists_normal_e8_zt (hMW : MacWilliamsStatement) (hGH : GH74.GH74Statement)
    (hKG : Foote5KnownGroups) (hD : Foote5AutData 𝕊 Lin)
    (hna : ∃ a ∈ S ⊓ L, ∃ b ∈ S ⊓ L, a * b ≠ b * a) (hCt : ∀ y ∈ T, y * t = t * y → y ∈ S)
    (hT2 : Nat.card T = 2 * Nat.card S) {s : G} (hsT : s ∈ T) (hsS : s ∉ S) :
    ∃ E : Subgroup G, E ≤ S ∧ T ≤ normalizer (E : Set G) ∧ (∀ e ∈ E, e * e = 1) ∧
      Nat.card E = 8 ∧ t ∈ E ∧ s⁻¹ * t * s ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsN := mem_normalizer_of_card_eq_two_mul h.ST hT2 hsT
  have hss : s * s ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 hsT hsT hsS hsS
  have ht22 : t * t = 1 := by rw [← sq, ← h.t2, pow_orderOf_eq_one]
  set z' := s⁻¹ * t * s with hz'
  have hz'Q := h.conj_t_mem_Q ε hD hna hCt hT2 hsT hsS
  have hz'Z : ∀ g ∈ S, g * z' = z' * g := by
    intro g hg
    have h1 := h.tZ _ (conj_mem_of_mem_normalizer (inv_mem hsN) hg)
    rw [inv_inv] at h1
    calc g * z' = s⁻¹ * ((s * g * s⁻¹) * t) * s := by rw [hz']; group
      _ = s⁻¹ * (t * (s * g * s⁻¹)) * s := by rw [h1]
      _ = z' * g := by rw [hz']; group
  have hz'2 : z' * z' = 1 := by
    rw [hz', show s⁻¹ * t * s * (s⁻¹ * t * s) = s⁻¹ * (t * t) * s by group, ht22]
    group
  have hz't : z' * t = t * z' := (hz'Z t h.tS).symm
  have hz'1 : z' ≠ 1 := fun h1 => h.t_ne_one (by
    calc t = s * z' * s⁻¹ := by rw [hz']; group
      _ = 1 := by rw [h1]; group)
  have hz'nt : z' ≠ t := fun h1 => h.t_not_mem_Q (h1 ▸ hz'Q)
  set V := kleinFourOfCommutingInvolutions z' t hz'2 ht22 hz't with hV
  have hV4 : Nat.card V = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions z' t hz'2 ht22 hz'1 h.t_ne_one hz'nt
      hz't).card_four
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    rcases (mem_kleinFour_iff hz'2 ht22 hz't).mp hv with rfl | rfl | rfl | rfl
    · rw [show z' * t * (z' * t) = z' * (t * z') * t by group, ← hz't,
        show z' * (z' * t) * t = (z' * z') * (t * t) by group, hz'2, ht22, one_mul]
    · exact hz'2
    · exact ht22
    · exact one_mul 1
  have hVT : V ≤ T := fun v hv => by
    rcases (mem_kleinFour_iff hz'2 ht22 hz't).mp hv with rfl | rfl | rfl | rfl
    · exact mul_mem (h.ST (h.QS hz'Q)) (h.ST h.tS)
    · exact h.ST (h.QS hz'Q)
    · exact h.ST h.tS
    · exact one_mem _
  have hst' : s * t * s⁻¹ = z' := by
    have h1 := hz'Z _ hss
    calc s * t * s⁻¹ = (s * s) * z' * (s * s)⁻¹ := by rw [hz']; group
      _ = z' := by rw [h1, mul_inv_cancel_right]
  have hconjV : ∀ g ∈ T, g * z' * g⁻¹ ∈ V ∧ g * t * g⁻¹ ∈ V := by
    intro g hg
    by_cases hgS : g ∈ S
    · rw [hz'Z g hgS, h.tZ g hgS, mul_inv_cancel_right, mul_inv_cancel_right]
      exact ⟨(mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inl rfl)),
        (mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    · have hσ : s⁻¹ * g ∈ S := mul_mem_of_card_eq_two_mul h.ST hT2 (inv_mem hsT) hg
        (fun h1 => hsS (by simpa using inv_mem h1)) hgS
      have hg' : g = s * (s⁻¹ * g) := by group
      constructor
      · rw [hg', show s * (s⁻¹ * g) * z' * (s * (s⁻¹ * g))⁻¹ =
          s * ((s⁻¹ * g) * z' * (s⁻¹ * g)⁻¹) * s⁻¹ by group, hz'Z _ hσ, mul_inv_cancel_right,
          hz', show s * (s⁻¹ * t * s) * s⁻¹ = t by group]
        exact (mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inr (Or.inl rfl)))
      · rw [hg', show s * (s⁻¹ * g) * t * (s * (s⁻¹ * g))⁻¹ =
          s * ((s⁻¹ * g) * t * (s⁻¹ * g)⁻¹) * s⁻¹ by group, h.tZ _ hσ, mul_inv_cancel_right,
          hst']
        exact (mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inl rfl))
  have hTV : T ≤ normalizer (V : Set G) := le_normalizer_of_conj_mem fun g hg v hv => by
    rcases (mem_kleinFour_iff hz'2 ht22 hz't).mp hv with rfl | rfl | rfl | rfl
    · rw [show g * (z' * t) * g⁻¹ = (g * z' * g⁻¹) * (g * t * g⁻¹) by group]
      exact mul_mem (hconjV g hg).1 (hconjV g hg).2
    · exact (hconjV g hg).1
    · exact (hconjV g hg).2
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
  obtain ⟨A, hAT, hTA, hA, hA8⟩ := h.exists_normal_e8 hMW hGH hKG h.sylT
  obtain ⟨E, hVE, hET, hTE, hEsq, hE8⟩ := exists_normal_e8_ge h.sylT.isPGroup hAT hTA
    (fun a ha => by rw [← sq]; exact hA.2 a ha) hA8 hVT hTV hVsq hV4
  have hz'E : z' ∈ E := hVE ((mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inl rfl)))
  have htE : t ∈ E := hVE ((mem_kleinFour_iff hz'2 ht22 hz't).mpr (Or.inr (Or.inr (Or.inl rfl))))
  refine ⟨E, fun e he => ?_, hTE, hEsq, hE8, htE, hz'E⟩
  by_contra heS
  have heT := hET he
  have heN := mem_normalizer_of_card_eq_two_mul h.ST hT2 (inv_mem heT)
  have het : e⁻¹ * t * e⁻¹⁻¹ ≠ t := fun h1 => heS (by
    have h2 := hCt e⁻¹ (inv_mem heT) (by
      calc e⁻¹ * t = e⁻¹ * t * e⁻¹⁻¹ * e⁻¹ := by group
        _ = t * e⁻¹ := by rw [h1])
    simpa using inv_mem h2)
  have hRe := h.inf_conjugate_R_eq_bot hna heN het
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb => commute_of_sq_eq_one hEsq ha hb
  have hcE : ∀ r ∈ S ⊓ L, r * e * r⁻¹ * e⁻¹ ∈ E := fun r hr =>
    mul_mem ((mem_normalizer_iff.mp (hTE (h.ST (mem_inf.mp hr).1)) e).mp he) (inv_mem he)
  have hr' : ∀ r ∈ S ⊓ L, e * r⁻¹ * e⁻¹ ∈ conjugate (S ⊓ L) e⁻¹ := fun r hr => by
    rw [mem_conjugate_iff, show e⁻¹ * (e * r⁻¹ * e⁻¹) * e⁻¹⁻¹ = r⁻¹ by group]
    exact inv_mem hr
  have hcomm : ∀ r ∈ S ⊓ L, ∀ b ∈ conjugate (S ⊓ L) e⁻¹, r * b = b * r := fun r hr b hb =>
    (h.commute_of_inf_conjugate_eq_bot heN hRe hr hb).symm
  have hRsq : ∀ r₁ ∈ S ⊓ L, ∀ r₂ ∈ S ⊓ L, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ hr₁ r₂ hr₂
    have h1 := hEc _ (hcE r₁ hr₁) _ (hcE r₂ hr₂)
    have h2 : (r₁ * r₂) * ((e * r₁⁻¹ * e⁻¹) * (e * r₂⁻¹ * e⁻¹)) =
        (r₂ * r₁) * ((e * r₂⁻¹ * e⁻¹) * (e * r₁⁻¹ * e⁻¹)) := by
      calc (r₁ * r₂) * ((e * r₁⁻¹ * e⁻¹) * (e * r₂⁻¹ * e⁻¹)) =
          r₁ * (r₂ * (e * r₁⁻¹ * e⁻¹)) * (e * r₂⁻¹ * e⁻¹) := by group
        _ = r₁ * ((e * r₁⁻¹ * e⁻¹) * r₂) * (e * r₂⁻¹ * e⁻¹) := by
            rw [hcomm r₂ hr₂ _ (hr' r₁ hr₁)]
        _ = (r₁ * e * r₁⁻¹ * e⁻¹) * (r₂ * e * r₂⁻¹ * e⁻¹) := by group
        _ = (r₂ * e * r₂⁻¹ * e⁻¹) * (r₁ * e * r₁⁻¹ * e⁻¹) := h1
        _ = r₂ * ((e * r₂⁻¹ * e⁻¹) * r₁) * (e * r₁⁻¹ * e⁻¹) := by group
        _ = r₂ * (r₁ * (e * r₂⁻¹ * e⁻¹)) * (e * r₁⁻¹ * e⁻¹) := by
            rw [hcomm r₁ hr₁ _ (hr' r₂ hr₂)]
        _ = (r₂ * r₁) * ((e * r₂⁻¹ * e⁻¹) * (e * r₁⁻¹ * e⁻¹)) := by group
    exact (eq_of_mul_eq_mul_of_disjoint hRe (mul_mem hr₁ hr₂) (mul_mem hr₂ hr₁)
      (mul_mem (hr' r₁ hr₁) (hr' r₂ hr₂)) (mul_mem (hr' r₂ hr₂) (hr' r₁ hr₁)) h2).1
  obtain ⟨a, ha, b, hb, hab⟩ := hna
  exact hab (hRsq a ha b hb)

end Sec5

end CFSG.ComponentClassification.Foote5
