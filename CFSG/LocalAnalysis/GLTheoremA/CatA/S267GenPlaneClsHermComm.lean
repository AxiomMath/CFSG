module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherHermitian

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.LocalAnalysis.ComponentInitial

variable {ℓ f : ℕ} {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

section Herm

variable (hE : UnitaryFieldData ℓ f E) {H : W →ₛₗ[hE.bar] W →ₗ[E] E}

theorem hermComm_bar_self (hH : H.IsSymm) (v : W) : hE.bar (H v v) = H v v := hH.eq v v

theorem hermComm_swap (hH : H.IsSymm) (u v : W) : H v u = hE.bar (H u v) := (hH.eq u v).symm

theorem hermComm_exists_traceZero : ∃ c : E, c ≠ 0 ∧ c + hE.bar c = 0 := by
  obtain ⟨e, he⟩ := hE.exists_bar_ne
  refine ⟨e - hE.bar e, sub_ne_zero.mpr he.symm, ?_⟩
  rw [map_sub, hE.bar_bar]
  ring

theorem herm_add_smul_expand (x y : W) (α : E) :
    H (x + α • y) (x + α • y) =
      H x x + α * H x y + hE.bar α * H y x + hE.bar α * (α * H y y) := by
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul]
  ring

theorem herm_add_smul_self (hH : H.IsSymm) {u u' : W} (hu : H u u = 0) (hu' : H u' u' = 0)
    (μ : E) : H (u + μ • u') (u + μ • u') = μ * H u u' + hE.bar (μ * H u u') := by
  rw [LinearMap.map_add₂, map_add, map_add, LinearMap.map_smulₛₗ₂, map_smul, map_smul,
    LinearMap.map_smulₛₗ₂, hu, hu', hermComm_swap hE hH u u', smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, map_mul]
  ring

variable (hℓ : ℓ ≠ 2)
include hℓ

include hE in
theorem hermComm_two_ne_zero : (2 : E) ≠ 0 := by
  haveI := hE.charP
  intro h2
  have := (CharP.cast_eq_zero_iff E ℓ 2).mp (by exact_mod_cast h2)
  exact hℓ ((Nat.prime_dvd_prime_iff_eq hE.prime Nat.prime_two).mp this)

theorem exists_isotropic_partner_herm (hH : H.IsSymm) (hHl : H.SeparatingLeft) {u : W}
    (hu0 : u ≠ 0) (hu : H u u = 0) : ∃ u' : W, H u' u' = 0 ∧ H u u' = 1 := by
  have h2 := hermComm_two_ne_zero hE hℓ
  obtain ⟨v, hv⟩ : ∃ v, H u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hHl u hcon)
  obtain ⟨v₀, huv₀⟩ : ∃ v₀, H u v₀ = 1 :=
    ⟨(H u v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  set α : E := -(H v₀ v₀) / 2 with hα
  have hαbar : hE.bar α = α := by
    rw [hα, map_div₀, map_neg, hermComm_bar_self hE hH, map_ofNat]
  have e1 : H v₀ u = 1 := by rw [hermComm_swap hE hH u v₀, huv₀, map_one]
  refine ⟨v₀ + α • u, ?_, ?_⟩
  · rw [herm_add_smul_expand hE]
    simp only [hu, e1, huv₀, hαbar, mul_zero, add_zero, mul_one]
    rw [hα]
    field_simp
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hu, mul_zero, add_zero, huv₀]

theorem exists_isotropic_common (hH : H.IsSymm) (hHl : H.SeparatingLeft) {u₁ u₂ : W}
    (hu₁0 : u₁ ≠ 0) (hu₁ : H u₁ u₁ = 0) (hu₂0 : u₂ ≠ 0) (hu₂ : H u₂ u₂ = 0) :
    ∃ u₃ : W, H u₃ u₃ = 0 ∧ H u₁ u₃ ≠ 0 ∧ H u₂ u₃ ≠ 0 := by
  obtain ⟨u₁', hu₁'i, hu₁u₁'⟩ := exists_isotropic_partner_herm hE hℓ hH hHl hu₁0 hu₁
  obtain ⟨u₂', hu₂'i, hu₂u₂'⟩ := exists_isotropic_partner_herm hE hℓ hH hHl hu₂0 hu₂
  by_cases h1 : H u₂ u₁' = 0
  · by_cases h2 : H u₁ u₂' = 0
    · obtain ⟨c₀, hc₀, hc₀t⟩ := hermComm_exists_traceZero hE
      by_cases hd : H u₁' u₂' = 0
      · refine ⟨u₁' + (1 : E) • u₂', ?_, ?_, ?_⟩
        · rw [herm_add_smul_self hE hH hu₁'i hu₂'i, hd, mul_zero, map_zero, add_zero]
        · rw [map_add, map_smul, h2, smul_zero, add_zero, hu₁u₁']
          exact one_ne_zero
        · rw [map_add, map_smul, h1, hu₂u₂', zero_add, smul_eq_mul, mul_one]
          exact one_ne_zero
      · refine ⟨u₁' + (c₀ / H u₁' u₂') • u₂', ?_, ?_, ?_⟩
        · rw [herm_add_smul_self hE hH hu₁'i hu₂'i, div_mul_cancel₀ _ hd]
          exact hc₀t
        · rw [map_add, map_smul, h2, smul_zero, add_zero, hu₁u₁']
          exact one_ne_zero
        · rw [map_add, map_smul, h1, hu₂u₂', zero_add, smul_eq_mul, mul_one]
          exact div_ne_zero hc₀ hd
    · exact ⟨u₂', hu₂'i, h2, by rw [hu₂u₂']; exact one_ne_zero⟩
  · exact ⟨u₁', hu₁'i, by rw [hu₁u₁']; exact one_ne_zero, h1⟩

end Herm

variable (hE : UnitaryFieldData ℓ f E) (hℓ : ℓ ≠ 2) {H : W →ₛₗ[hE.bar] W →ₗ[E] E}
  (hH : H.IsSymm) (hHl : H.SeparatingLeft) (θ : E →+* E) (s : W →+ W)
  (hs : ∀ (e : E) (w : W), s (e • w) = θ e • s w)
  (hcomm : ∀ u : W, H u u = 0 → ∀ c : E, c + hE.bar c = 0 → ∀ v : W,
    s (v + (c * H u v) • u) = s v + (c * H u (s v)) • u)
include hE hℓ hH hHl hs hcomm

theorem hermComm_line {u : W} (hu : H u u = 0) : ∃ a : E, s u = a • u := by
  by_cases hu0 : u = 0
  · exact ⟨0, by rw [hu0, map_zero, smul_zero]⟩
  obtain ⟨c₀, hc₀, hc₀t⟩ := hermComm_exists_traceZero hE
  obtain ⟨v, hv⟩ : ∃ v, H u v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hHl u hcon)
  obtain ⟨v₀, huv₀⟩ : ∃ v₀, H u v₀ = 1 :=
    ⟨(H u v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩
  have h1 := hcomm u hu c₀ hc₀t v₀
  rw [huv₀, mul_one, map_add] at h1
  have h2 : s (c₀ • u) = (c₀ * H u (s v₀)) • u := add_left_cancel h1
  rw [hs] at h2
  have hθ : θ c₀ ≠ 0 := (map_ne_zero θ).mpr hc₀
  refine ⟨(θ c₀)⁻¹ * (c₀ * H u (s v₀)), ?_⟩
  rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hθ, one_smul]

theorem hermComm_rel {u u' : W} (hu : H u u = 0) (hu' : H u' u' = 0) (hd : H u u' ≠ 0)
    {a a' : E} (ha : s u = a • u) (ha' : s u' = a' • u') {μ : E}
    (hμ : μ * H u u' + hE.bar (μ * H u u') = 0) : a * μ = θ μ * a' := by
  have hw : H (u + μ • u') (u + μ • u') = 0 := by rw [herm_add_smul_self hE hH hu hu']; exact hμ
  obtain ⟨b, hb⟩ := hermComm_line hE hℓ hH hHl θ s hs hcomm hw
  rw [map_add, hs, ha, ha', smul_add, smul_smul, smul_smul] at hb
  have hind : ∀ x y : E, x • u + y • u' = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have h1 := congrArg (H u) hxy
    rw [map_add, map_smul, map_smul, hu, smul_zero, zero_add, map_zero, smul_eq_mul] at h1
    have hy : y = 0 := (mul_eq_zero.mp h1).resolve_right hd
    rw [hy, zero_smul, add_zero] at hxy
    have h2 := congrArg (fun w => H w u') hxy
    simp only [LinearMap.map_smulₛₗ₂, LinearMap.zero_apply, map_zero, smul_eq_mul] at h2
    have hx : hE.bar x = 0 := (mul_eq_zero.mp h2).resolve_right hd
    exact ⟨(map_eq_zero hE.bar).mp hx, hy⟩
  have h3 : (a - b) • u + (θ μ * a' - b * μ) • u' = 0 := by
    rw [sub_smul, sub_smul, show a • u - b • u + ((θ μ * a') • u' - (b * μ) • u') =
      (a • u + (θ μ * a') • u') - (b • u + (b * μ) • u') by abel, hb, sub_self]
  obtain ⟨h4, h5⟩ := hind _ _ h3
  rw [sub_eq_zero] at h4 h5
  rw [h4, h5]

include s in
theorem hermComm [FiniteDimensional E W] (hW : 2 ≤ Module.finrank E W)
    (hsinj : Function.Injective s) :
    (∀ e : E, hE.bar e = e → θ e = e) ∧ (θ = RingHom.id E → ∃ c : E, ∀ w, s w = c • w) := by
  classical
  obtain ⟨u, hu0, hu⟩ : ∃ u : W, u ≠ 0 ∧ H u u = 0 := by
    by_contra hcon
    push Not at hcon
    have hspan := UnitaryHigher.span_isotropic_eq_top hE hH hHl hW
    have hbot : Submodule.span E {v : W | v ≠ 0 ∧ H v v = 0} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro v ⟨hv0, hv⟩
      exact absurd hv (hcon v hv0)
    rw [hbot] at hspan
    have : Module.finrank E W = 0 := by
      rw [← finrank_top E W, ← hspan, finrank_bot]
    omega
  obtain ⟨u', hu'i, huu'⟩ := exists_isotropic_partner_herm hE hℓ hH hHl hu0 hu
  obtain ⟨a, ha⟩ := hermComm_line hE hℓ hH hHl θ s hs hcomm hu
  obtain ⟨a', ha'⟩ := hermComm_line hE hℓ hH hHl θ s hs hcomm hu'i
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hu0 (hsinj (by rw [ha, map_zero]))
  obtain ⟨c₀, hc₀, hc₀t⟩ := hermComm_exists_traceZero hE
  have hd : H u u' ≠ 0 := by rw [huu']; exact one_ne_zero
  have hrel : ∀ μ : E, μ + hE.bar μ = 0 → a * μ = θ μ * a' := fun μ hμ =>
    hermComm_rel hE hℓ hH hHl θ s hs hcomm hu hu'i hd ha ha' (by rw [huu', mul_one]; exact hμ)
  refine ⟨fun e he => ?_, fun hθ => ?_⟩
  ·
    have h1 := hrel c₀ hc₀t
    have h2 := hrel (c₀ * e) (by rw [map_mul, he, ← add_mul, hc₀t, zero_mul])
    rw [map_mul] at h2
    have h3 : a * c₀ * e = a * c₀ * θ e := by
      calc a * c₀ * e = a * (c₀ * e) := by ring
        _ = θ c₀ * θ e * a' := h2
        _ = (θ c₀ * a') * θ e := by ring
        _ = a * c₀ * θ e := by rw [← h1]
    exact (mul_left_cancel₀ (mul_ne_zero ha0 hc₀) h3).symm
  · subst hθ
    have hconst : ∀ w : W, w ≠ 0 → H w w = 0 → s w = a • w := by
      have hpair : ∀ {w₁ w₂ : W} {b₁ b₂ : E}, H w₁ w₁ = 0 → H w₂ w₂ = 0 → H w₁ w₂ ≠ 0 →
          s w₁ = b₁ • w₁ → s w₂ = b₂ • w₂ → b₁ = b₂ := by
        intro w₁ w₂ b₁ b₂ h₁ h₂ h₁₂ hb₁ hb₂
        have hμ : (c₀ / H w₁ w₂) * H w₁ w₂ + hE.bar ((c₀ / H w₁ w₂) * H w₁ w₂) = 0 := by
          rw [div_mul_cancel₀ _ h₁₂]
          exact hc₀t
        have h := hermComm_rel hE hℓ hH hHl (RingHom.id E) s hs hcomm h₁ h₂ h₁₂ hb₁ hb₂ hμ
        rw [RingHom.id_apply, mul_comm (c₀ / H w₁ w₂)] at h
        exact mul_right_cancel₀ (div_ne_zero hc₀ h₁₂) h
      intro w hw0 hw
      obtain ⟨b, hb⟩ := hermComm_line hE hℓ hH hHl (RingHom.id E) s hs hcomm hw
      obtain ⟨w₃, hw₃, hu₃, hw₃'⟩ := exists_isotropic_common hE hℓ hH hHl hu0 hu hw0 hw
      obtain ⟨b₃, hb₃⟩ := hermComm_line hE hℓ hH hHl (RingHom.id E) s hs hcomm hw₃
      have e1 := hpair hu hw₃ hu₃ ha hb₃
      have e2 := hpair hw hw₃ hw₃' hb hb₃
      rw [hb, e2, ← e1]
    refine ⟨a, fun w => ?_⟩
    have hspan := UnitaryHigher.span_isotropic_eq_top hE hH hHl hW
    have hw : w ∈ Submodule.span E {v : W | v ≠ 0 ∧ H v v = 0} := by
      rw [hspan]
      exact Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact hconst x hx.1 hx.2
    | zero => rw [map_zero, smul_zero]
    | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
    | smul e x _ hx => rw [hs, RingHom.id_apply, hx, smul_comm]

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
