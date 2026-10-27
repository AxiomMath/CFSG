module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.RankOne

namespace NormInvolution

variable {E : Type*} [Field E]

theorem eq_of_add_eq_zero [CharP E 2] {a b : E} (h : a + b = 0) : b = a := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination h - a * h2

theorem exists_eq_add_mul [CharP E 2] (ρ : E →+* E) (hρρ : ∀ x, ρ (ρ x) = x) {ω : E}
    (hω : ρ ω ≠ ω) (d : E) : ∃ l m : E, ρ l = l ∧ ρ m = m ∧ d = l + m * ω := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hτ : ω + ρ ω ≠ 0 := fun h => hω (eq_of_add_eq_zero h)
  obtain ⟨m, hmdef⟩ : ∃ m, m = (d + ρ d) / (ω + ρ ω) := ⟨_, rfl⟩
  have hm : ρ m = m := by
    rw [hmdef, map_div₀, map_add, map_add, hρρ, hρρ, add_comm (ρ d), add_comm (ρ ω)]
  have hmτ : m * (ω + ρ ω) = d + ρ d := by rw [hmdef]; exact div_mul_cancel₀ _ hτ
  refine ⟨d + m * ω, m, ?_, hm, ?_⟩
  · apply eq_of_add_eq_zero
    rw [map_add, map_mul, hm]
    linear_combination hmτ + (d + ρ d) * h2
  · linear_combination (-(m * ω)) * h2

theorem eq_and_eq_of_add_mul_eq (ρ : E →+* E) {ω : E} (hω : ρ ω ≠ ω) {l m l' m' : E}
    (hl : ρ l = l) (hm : ρ m = m) (hl' : ρ l' = l') (hm' : ρ m' = m')
    (h : l + m * ω = l' + m' * ω) : l = l' ∧ m = m' := by
  have hmm : m = m' := by
    by_contra hne
    apply hω
    have hsub : m - m' ≠ 0 := sub_ne_zero.mpr hne
    have e : ω = (l' - l) / (m - m') := by
      rw [eq_div_iff hsub]
      linear_combination h
    rw [e, map_div₀, map_sub, map_sub, hl, hl', hm, hm']
  refine ⟨?_, hmm⟩
  rw [hmm] at h
  linear_combination h

theorem card_eq_sq [CharP E 2] (ρ : E →+* E) (hρρ : ∀ x, ρ (ρ x) = x) {ω : E} (hω : ρ ω ≠ ω) :
    Nat.card E = Nat.card {x : E // ρ x = x} ^ 2 := by
  let f : {x : E // ρ x = x} × {x : E // ρ x = x} → E := fun p => p.1.1 + p.2.1 * ω
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨l, hl⟩, ⟨m, hm⟩⟩ ⟨⟨l', hl'⟩, ⟨m', hm'⟩⟩ h
      obtain ⟨e1, e2⟩ := eq_and_eq_of_add_mul_eq ρ hω hl hm hl' hm' h
      subst e1
      subst e2
      rfl
    · intro d
      obtain ⟨l, m, hl, hm, rfl⟩ := exists_eq_add_mul ρ hρρ hω d
      exact ⟨(⟨l, hl⟩, ⟨m, hm⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, sq]

theorem pow_card_eq_of_fixed [Finite E] (ρ : E →+* E) {x : E} (hx : ρ x = x) :
    x ^ Nat.card {y : E // ρ y = y} = x := by
  let K := ρ.eqLocusField (RingHom.id E)
  have : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card {y : E // ρ y = y} = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => Iff.rfl)
  have h := congrArg Subtype.val (FiniteField.pow_card (⟨x, hx⟩ : K))
  rw [hcard]
  simpa using h

theorem sigma_sigma [Finite E] (σ : E →+* E) {q : ℕ} (hσq : ∀ x, σ x = x ^ q)
    (hE : Nat.card E = q ^ 2) (y : E) : σ (σ y) = y := by
  have : Fintype E := Fintype.ofFinite E
  rw [hσq, hσq, ← pow_mul, ← sq, ← hE, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_sigma_ne [Finite E] (σ : E →+* E) {q : ℕ} (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) : ∃ ω : E, σ ω ≠ ω := by
  by_contra hall
  push Not at hall
  have h := Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  rw [hF, hE] at h
  have hgt : 1 < Nat.card E := Finite.one_lt_card
  rw [hE] at hgt
  nlinarith

theorem fixed_of_normalized [CharP E 2] [Finite E] (σ : E →+* E) {q : ℕ}
    (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q)
    (φ χ : E → E) (hφadd : ∀ a b, φ (a + b) = φ a + φ b) (hφφ : ∀ a, φ (φ a) = a)
    (hφ1 : φ 1 = 1) (hχadd : ∀ a b, σ a = a → σ b = b → χ (a + b) = χ a + χ b)
    (hχ : ∀ a, χ (a * σ a) = φ a * σ (φ a)) {x : E} (hx : σ x = x) : χ x = x := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hσσ := sigma_sigma σ hσq hE
  obtain ⟨ω, hω⟩ := exists_sigma_ne σ hE hF
  have hσ1 : σ 1 = 1 := map_one σ
  have hφ0 : φ 0 = 0 := by
    have h := hφadd 0 0
    rw [add_zero] at h
    linear_combination -h
  have hχ0 : χ 0 = 0 := by
    have h := hχadd 0 0 (map_zero σ) (map_zero σ)
    rw [add_zero] at h
    linear_combination -h
  have hNfix : ∀ a, σ (a * σ a) = a * σ a := fun a => by rw [map_mul, hσσ, mul_comm]
  have hTrfix : ∀ a, σ (a + σ a) = a + σ a := fun a => by rw [map_add, hσσ, add_comm]
  have hBfix : ∀ a b, σ (a * σ b + σ a * b) = a * σ b + σ a * b := fun a b => by
    rw [map_add, map_mul, map_mul, hσσ, hσσ]
    ring
  have hB : ∀ a b, χ (a * σ b + σ a * b) = φ a * σ (φ b) + σ (φ a) * φ b := by
    intro a b
    have e : (a + b) * σ (a + b) = (a * σ a + b * σ b) + (a * σ b + σ a * b) := by
      rw [map_add]
      ring
    have h1 := hχ (a + b)
    rw [e, hχadd _ _ (by rw [map_add, hNfix, hNfix]) (hBfix a b),
      hχadd _ _ (hNfix a) (hNfix b), hχ a, hχ b, hφadd, map_add] at h1
    linear_combination h1
  have hTr : ∀ c, φ c + σ (φ c) = χ (c + σ c) := by
    intro c
    have h := hB 1 c
    simp only [hσ1, hφ1, one_mul] at h
    rw [add_comm c, add_comm (φ c)]
    exact h.symm
  have hFF : ∀ l, σ l = l → σ (φ l) = φ l := by
    intro l hl
    have h := hTr l
    rw [hl, CharTwo.add_self_eq_zero, hχ0] at h
    exact eq_of_add_eq_zero h
  have hτ : ω + σ ω ≠ 0 := fun h => hω (eq_of_add_eq_zero h)
  have hστ : σ (ω + σ ω) = ω + σ ω := hTrfix ω
  have hTrsurj : ∀ m, σ m = m →
      m * (ω + σ ω)⁻¹ * ω + σ (m * (ω + σ ω)⁻¹ * ω) = m := by
    intro m hm
    rw [map_mul, map_mul, map_inv₀, hm, hστ]
    have e : m * (ω + σ ω)⁻¹ * ω + m * (ω + σ ω)⁻¹ * σ ω =
        m * ((ω + σ ω)⁻¹ * (ω + σ ω)) := by ring
    rw [e, inv_mul_cancel₀ hτ, mul_one]
  have hχmul : ∀ l m, σ l = l → σ m = m → χ (l * m) = φ l * χ m := by
    intro l m hl hm
    obtain ⟨c, hcdef⟩ : ∃ c, c = m * (ω + σ ω)⁻¹ * ω := ⟨_, rfl⟩
    have hc : c + σ c = m := by rw [hcdef]; exact hTrsurj m hm
    have h := hB l c
    have e1 : l * σ c + σ l * c = l * m := by rw [hl, ← hc]; ring
    have e2 : φ l * σ (φ c) + σ (φ l) * φ c = φ l * χ m := by
      rw [hFF l hl, ← hc, ← hTr c]
      ring
    rw [e1, e2] at h
    exact h
  have hχ1 : χ 1 = 1 := by
    have h := hχ 1
    simp only [hσ1, hφ1, mul_one] at h
    exact h
  have hχφ : ∀ l, σ l = l → χ l = φ l := by
    intro l hl
    have h := hχmul l 1 hl hσ1
    rw [mul_one, hχ1, mul_one] at h
    exact h
  have hsemi : ∀ l c, σ l = l → φ (l * c) = φ l * φ c := by
    intro l c hl
    obtain ⟨w, hw⟩ : ∃ w, w = φ (l * c) - φ l * φ c := ⟨_, rfl⟩
    have hBw : ∀ e, w * σ e + σ w * e = 0 := by
      intro e
      have h := hB (l * c) (φ e)
      have e1 : l * c * σ (φ e) + σ (l * c) * φ e = l * (c * σ (φ e) + σ c * φ e) := by
        rw [map_mul, hl]
        ring
      rw [e1, hχmul l _ hl (hBfix c (φ e)), hB c (φ e), hφφ] at h
      rw [hw, map_sub, map_mul, hFF l hl]
      linear_combination -h
    have hw1 : σ w = w := by
      have h := hBw 1
      rw [hσ1, mul_one, mul_one] at h
      exact eq_of_add_eq_zero h
    have hw0 : w = 0 := by
      have h := hBw ω
      rw [hw1] at h
      have e : w * (ω + σ ω) = 0 := by linear_combination h
      rcases mul_eq_zero.mp e with h' | h'
      · exact h'
      · exact absurd h' hτ
    rw [hw] at hw0
    exact sub_eq_zero.mp hw0
  have hsq : ∀ c, φ (c * c) = φ c * φ c := by
    intro c
    have e : c * c = (c + σ c) * c + c * σ c := by linear_combination (-(c * σ c)) * h2
    rw [e, hφadd, hsemi _ _ (hTrfix c), ← hχφ _ (hTrfix c), ← hχφ _ (hNfix c), hχ c, ← hTr c]
    linear_combination (φ c * σ (φ c)) * h2
  have hmulω : ∀ c, φ (c * ω) = φ c * φ ω := by
    intro c
    obtain ⟨l, m, hl, hm, rfl⟩ := exists_eq_add_mul σ hσσ hω c
    have e : (l + m * ω) * ω = l * ω + m * (ω * ω) := by ring
    rw [e, hφadd, hsemi l ω hl, hsemi m _ hm, hsq, hφadd, hsemi m ω hm]
    ring
  have hmul : ∀ c d, φ (c * d) = φ c * φ d := by
    intro c d
    obtain ⟨l, m, hl, hm, rfl⟩ := exists_eq_add_mul σ hσσ hω d
    have e : c * (l + m * ω) = l * c + m * (c * ω) := by ring
    rw [e, hφadd, hsemi l c hl, hsemi m _ hm, hmulω, hφadd, hsemi m ω hm]
    ring
  let φR : E →+* E :=
    { toFun := φ, map_one' := hφ1, map_mul' := hmul, map_zero' := hφ0, map_add' := hφadd }
  have hφRφR : ∀ y, φR (φR y) = y := hφφ
  rw [hχφ x hx]
  by_cases hall : ∀ y, φ y = y
  · exact hall x
  push Not at hall
  obtain ⟨ω', hω'⟩ := hall
  have hK : Nat.card {y : E // φR y = y} = q := by
    have h := card_eq_sq φR hφRφR (ω := ω') hω'
    rw [hE] at h
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h).symm
  have hsub : ∀ y, φ y = y → σ y = y := by
    intro y hy
    have h := pow_card_eq_of_fixed φR (x := y) hy
    rw [hK] at h
    rw [hσq, h]
  let f : {y : E // φR y = y} → {y : E // σ y = y} := fun y => ⟨y.1, hsub y.1 y.2⟩
  have hfinj : Function.Injective f := by
    intro y y' h
    apply Subtype.ext
    have h' : (f y).1 = (f y').1 := by rw [h]
    exact h'
  obtain ⟨y, hy⟩ := (hfinj.bijective_of_nat_card_le (by rw [hF, hK])).2 ⟨x, hx⟩
  have hyx : y.1 = x := congrArg Subtype.val hy
  rw [← hyx]
  exact y.2

theorem norm_apply_eq_of_involutive [CharP E 2] [Finite E] (σ : E →+* E) {q : ℕ}
    (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q)
    (φ χ : E → E) (hφadd : ∀ a b, φ (a + b) = φ a + φ b) (hφφ : ∀ a, φ (φ a) = a)
    (hχadd : ∀ a b, σ a = a → σ b = b → χ (a + b) = χ a + χ b)
    (hχ : ∀ a, χ (a * σ a) = φ a * σ (φ a)) (a : E) : φ a * σ (φ a) = a * σ a := by
  have hσσ := sigma_sigma σ hσq hE
  by_cases hall : ∀ b, φ b = b
  · rw [hall]
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ = b + φ b := ⟨_, rfl⟩
  have ha₀ne : a₀ ≠ 0 := fun h => hb (eq_of_add_eq_zero (ha₀ ▸ h))
  have hφa₀ : φ a₀ = a₀ := by rw [ha₀, hφadd, hφφ, add_comm]
  have hσa₀ : σ a₀ ≠ 0 := (map_ne_zero σ).mpr ha₀ne
  have hnfix : ∀ z, σ z = z → σ (a₀ * σ a₀ * z) = a₀ * σ a₀ * z := fun z hz => by
    rw [map_mul, map_mul, hσσ, hz, mul_comm (σ a₀)]
  have key : ∀ x, σ x = x → (a₀ * σ a₀)⁻¹ * χ (a₀ * σ a₀ * x) = x := fun x hx =>
    fixed_of_normalized σ hσq hE hF (fun c => a₀⁻¹ * φ (a₀ * c))
    (fun z => (a₀ * σ a₀)⁻¹ * χ (a₀ * σ a₀ * z))
    (fun c d => by simp only [mul_add, hφadd])
    (fun c => by simp only [mul_inv_cancel_left₀ ha₀ne, hφφ, inv_mul_cancel_left₀ ha₀ne])
    (by simp only [mul_one, hφa₀, inv_mul_cancel₀ ha₀ne])
    (fun z w hz hw => by simp only [mul_add, hχadd _ _ (hnfix z hz) (hnfix w hw)])
    (fun c => by
      have e : a₀ * σ a₀ * (c * σ c) = a₀ * c * σ (a₀ * c) := by rw [map_mul]; ring
      rw [e, hχ, map_mul, map_inv₀, mul_inv]
      ring) hx
  have hfix : σ ((a₀ * σ a₀)⁻¹ * (a * σ a)) = (a₀ * σ a₀)⁻¹ * (a * σ a) := by
    rw [map_mul, map_inv₀, map_mul, map_mul, hσσ, hσσ, mul_comm (σ a₀), mul_comm (σ a)]
  have h := key _ hfix
  rw [mul_inv_cancel_left₀ (mul_ne_zero ha₀ne hσa₀)] at h
  have h' : χ (a * σ a) = a * σ a := by
    have hn : a₀ * σ a₀ ≠ 0 := mul_ne_zero ha₀ne hσa₀
    have := congrArg (fun z => a₀ * σ a₀ * z) h
    simp only [mul_inv_cancel_left₀ hn] at this
    exact this
  rw [← hχ a, h']

end NormInvolution

end CFSG.SeitzReduction.RankOne
