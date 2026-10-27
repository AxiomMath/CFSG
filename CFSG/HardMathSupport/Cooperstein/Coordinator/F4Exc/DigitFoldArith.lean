module

public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

@[expose] def DigitRes (f x e : ℕ) : Prop := x = e ∨ x = e + f ∨ x = e + 2 * f

instance (f x e : ℕ) : Decidable (DigitRes f x e) :=
  inferInstanceAs (Decidable (x = e ∨ x = e + f ∨ x = e + 2 * f))

theorem exists_digitRes {f : ℕ} (hf : 0 < f) {x : ℕ} (hx : x < 3 * f) :
    ∃ e < f, DigitRes f x e := by
  refine ⟨x % f, Nat.mod_lt _ hf, ?_⟩
  have h := Nat.div_add_mod x f
  have hq : x / f < 3 := by
    rw [Nat.div_lt_iff_lt_mul hf]; linarith
  unfold DigitRes
  generalize x / f = q at h hq
  generalize x % f = r at h ⊢
  interval_cases q <;> omega

theorem dvd_pow_sub_of_res {f x e : ℕ} (h : DigitRes f x e) : ((2 : ℤ) ^ f - 1) ∣ 2 ^ x - 2 ^ e := by
  rcases h with rfl | rfl | rfl
  · simp
  · exact ⟨2 ^ e, by ring⟩
  · exact ⟨2 ^ e * (2 ^ f + 1), by ring⟩

theorem coprime_pow_two {f : ℕ} (hf : 1 ≤ f) (k : ℕ) : IsCoprime ((2 : ℤ) ^ f - 1) (2 ^ k) := by
  refine IsCoprime.pow_right ?_
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact ⟨-1, 2 ^ g, by ring⟩

theorem seven_le {f : ℕ} (hf : 3 ≤ f) : (7 : ℤ) ≤ 2 ^ f - 1 := by
  have : (2 : ℤ) ^ 3 ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
  norm_num at this; linarith

theorem pow_eq_of_dvd {f : ℕ} (hf : 3 ≤ f) {e₁ e₂ : ℕ} (h₁ : e₁ < f) (h₂ : e₂ < f)
    (h : ((2 : ℤ) ^ f - 1) ∣ 2 ^ e₁ - 2 ^ e₂) : e₁ = e₂ := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hP : (4 : ℤ) ≤ 2 ^ g := by
    have : (2 : ℤ) ^ 2 ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hx : (2 : ℤ) ^ e₁ ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
  have hy : (2 : ℤ) ^ e₂ ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
  have hx1 : (1 : ℤ) ≤ 2 ^ e₁ := one_le_pow₀ (by norm_num)
  have hy1 : (1 : ℤ) ≤ 2 ^ e₂ := one_le_pow₀ (by norm_num)
  have hsucc : (2 : ℤ) ^ (g + 1) = 2 * 2 ^ g := by ring
  have h0 : (2 : ℤ) ^ e₁ - 2 ^ e₂ = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h ?_
    rw [abs_lt]; constructor <;> linarith
  have : (2 : ℤ) ^ e₁ = 2 ^ e₂ := by linarith
  exact pow_right_injective₀ (by norm_num : (0 : ℤ) < 2) (by norm_num : (2 : ℤ) ≠ 1) this

theorem not_dvd_pow_add {f : ℕ} (hf : 3 ≤ f) {e₁ e₂ : ℕ} (h₁ : e₁ < f) (h₂ : e₂ < f) :
    ¬ ((2 : ℤ) ^ f - 1) ∣ 2 ^ e₁ + 2 ^ e₂ := by
  rintro ⟨k, hk⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  have hP : (4 : ℤ) ≤ 2 ^ g := by
    have : (2 : ℤ) ^ 2 ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hx : (2 : ℤ) ^ e₁ ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
  have hy : (2 : ℤ) ^ e₂ ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
  have hx1 : (1 : ℤ) ≤ 2 ^ e₁ := one_le_pow₀ (by norm_num)
  have hy1 : (1 : ℤ) ≤ 2 ^ e₂ := one_le_pow₀ (by norm_num)
  have hsucc : (2 : ℤ) ^ (g + 1) = 2 * 2 ^ g := by ring
  have par : ∀ e : ℕ, (2 : ℤ) ^ e = 1 ∨ ∃ t : ℤ, (2 : ℤ) ^ e = 2 * t := by
    intro e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · left; simp
    · right; exact ⟨2 ^ (e - 1), by rw [← pow_succ']; congr 1; omega⟩
  rw [hsucc] at hk
  have hk1 : k = 1 := by
    have hpos : 0 < k := by
      by_contra hk0
      push Not at hk0
      nlinarith
    by_contra hne
    have : 2 ≤ k := by omega
    nlinarith
  subst hk1
  have p₁ := par e₁
  have p₂ := par e₂
  clear par
  generalize (2 : ℤ) ^ e₁ = x at *
  generalize (2 : ℤ) ^ e₂ = y at *
  generalize (2 : ℤ) ^ g = P at *
  rcases p₁ with h | ⟨t, ht⟩ <;> rcases p₂ with h' | ⟨t', ht'⟩ <;> omega

theorem rep_unique {f : ℕ} (hf : 3 ≤ f) {σ₁ σ₂ : ℤ} (hσ₁ : σ₁ = 1 ∨ σ₁ = -1)
    (hσ₂ : σ₂ = 1 ∨ σ₂ = -1) {e₁ e₂ : ℕ} (h₁ : e₁ < f) (h₂ : e₂ < f)
    (h : ((2 : ℤ) ^ f - 1) ∣ σ₁ * 2 ^ e₁ - σ₂ * 2 ^ e₂) : σ₁ = σ₂ ∧ e₁ = e₂ := by
  rcases hσ₁ with rfl | rfl <;> rcases hσ₂ with rfl | rfl
  · exact ⟨rfl, pow_eq_of_dvd hf h₁ h₂ (by simpa using h)⟩
  · exact absurd (by convert h using 1; ring) (not_dvd_pow_add hf h₁ h₂)
  · refine absurd ?_ (not_dvd_pow_add hf h₁ h₂)
    have := (dvd_neg).2 h
    convert this using 1; ring
  · refine ⟨rfl, pow_eq_of_dvd hf h₁ h₂ ?_⟩
    have := (dvd_neg).2 h
    convert this using 1; ring

theorem step_rep {f : ℕ} (hf : 3 ≤ f) (a : ℤ) {dg : ℕ} (hdg : dg < 2 * f)
    (H : ((2 : ℤ) ^ f - 1) ∣ a - 2 ^ dg ∨ ((2 : ℤ) ^ f - 1) ∣ a + 2 ^ dg ∨
      ((2 : ℤ) ^ f - 1) ∣ 2 * a - 2 ^ dg) :
    ∃ σ : ℤ, ∃ e < f, (σ = 1 ∨ σ = -1) ∧ ((2 : ℤ) ^ f - 1) ∣ 2 * a - σ * 2 ^ e ∧
      ((σ = 1 ∧ (DigitRes f (dg + 1) e ∨ DigitRes f dg e)) ∨ (σ = -1 ∧ DigitRes f (dg + 1) e)) := by
  rcases H with h | h | h
  · obtain ⟨e, he, hr⟩ := exists_digitRes (f := f) (by omega) (x := dg + 1) (by omega)
    refine ⟨1, e, he, Or.inl rfl, ?_, Or.inl ⟨rfl, Or.inl hr⟩⟩
    have h2 := dvd_pow_sub_of_res hr
    have := dvd_add (dvd_mul_of_dvd_right h 2) h2
    convert this using 1; ring
  · obtain ⟨e, he, hr⟩ := exists_digitRes (f := f) (by omega) (x := dg + 1) (by omega)
    refine ⟨-1, e, he, Or.inr rfl, ?_, Or.inr ⟨rfl, hr⟩⟩
    have h2 := dvd_pow_sub_of_res hr
    have := dvd_sub (dvd_mul_of_dvd_right h 2) h2
    convert this using 1; ring
  · obtain ⟨e, he, hr⟩ := exists_digitRes (f := f) (by omega) (x := dg) (by omega)
    refine ⟨1, e, he, Or.inl rfl, ?_, Or.inl ⟨rfl, Or.inr hr⟩⟩
    have h2 := dvd_pow_sub_of_res hr
    have := dvd_add h h2
    convert this using 1; ring

theorem card_res_zero {f : ℕ} {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 2 * f) (e : ℕ) :
    (J.filter fun b => DigitRes f b e).card ≤ 2 := by
  have : (J.filter fun b => DigitRes f b e) ⊆ {e, e + f} := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have := hJ b hb.1
    have h := hb.2
    unfold DigitRes at h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  exact (Finset.card_le_card this).trans Finset.card_le_two

theorem card_res_succ {f : ℕ} {J : Finset ℕ} (hJ : ∀ i ∈ J, i < 2 * f) {e : ℕ} (he : e < f) :
    (J.filter fun b => DigitRes f (b + 1) e).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · have : (J.filter fun b => DigitRes f (b + 1) 0) ⊆ {f - 1, 2 * f - 1} := by
      intro b hb
      rw [Finset.mem_filter] at hb
      have := hJ b hb.1
      have h := hb.2
      unfold DigitRes at h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card this).trans Finset.card_le_two
  · have : (J.filter fun b => DigitRes f (b + 1) e) ⊆ {e - 1, e + f - 1} := by
      intro b hb
      rw [Finset.mem_filter] at hb
      have := hJ b hb.1
      have h := hb.2
      unfold DigitRes at h
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    exact (Finset.card_le_card this).trans Finset.card_le_two

theorem not_dvd_small {f : ℕ} (hf : 3 ≤ f) {k : ℤ} (hk1 : 1 ≤ k) (hk5 : k ≤ 5) (e : ℕ)
    (h : ((2 : ℤ) ^ f - 1) ∣ k * 2 ^ e) : False := by
  have h1 := (coprime_pow_two (by omega) e).dvd_of_dvd_mul_right h
  have := Int.le_of_dvd (by omega) h1
  have := seven_le hf
  omega

theorem exists_good_digit {f : ℕ} (hf : 3 ≤ f) (J : Finset ℕ) (hJ : ∀ i ∈ J, i < 2 * f)
    (hc : 2 ≤ J.card) :
    ∃ dg ∈ J, ¬ ((2 : ℤ) ^ f - 1) ∣ (∑ b ∈ J, (2 : ℤ) ^ b) - 2 ^ dg ∧
      ¬ ((2 : ℤ) ^ f - 1) ∣ (∑ b ∈ J, (2 : ℤ) ^ b) + 2 ^ dg ∧
      ¬ ((2 : ℤ) ^ f - 1) ∣ 2 * (∑ b ∈ J, (2 : ℤ) ^ b) - 2 ^ dg := by
  by_contra hcon
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = ∑ b ∈ J, (2 : ℤ) ^ b := ⟨_, rfl⟩
  rw [← ha] at hcon
  have H : ∀ dg ∈ J, ((2 : ℤ) ^ f - 1) ∣ a - 2 ^ dg ∨ ((2 : ℤ) ^ f - 1) ∣ a + 2 ^ dg ∨
      ((2 : ℤ) ^ f - 1) ∣ 2 * a - 2 ^ dg := by
    intro dg hdg
    by_contra h
    push Not at h
    exact hcon ⟨dg, hdg, h.1, h.2.1, h.2.2⟩
  have hrep := fun dg (hdg : dg ∈ J) => step_rep hf a (hJ dg hdg) (H dg hdg)
  obtain ⟨dg0, hdg0⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨σ0, e0, he0, hσ0, hd0, -⟩ := hrep dg0 hdg0
  have hall : ∀ dg ∈ J, (σ0 = 1 ∧ (DigitRes f (dg + 1) e0 ∨ DigitRes f dg e0)) ∨
      (σ0 = -1 ∧ DigitRes f (dg + 1) e0) := by
    intro dg hdg
    obtain ⟨σ, e, he, hσ, hd, hrel⟩ := hrep dg hdg
    have h1 : ((2 : ℤ) ^ f - 1) ∣ σ * 2 ^ e - σ0 * 2 ^ e0 := by
      have := dvd_sub hd0 hd
      convert this using 1; ring
    obtain ⟨h2, h3⟩ := rep_unique hf hσ hσ0 he he0 h1
    subst h2; subst h3
    exact hrel
  rcases hσ0 with rfl | rfl
  ·
    have hJ0 := card_res_zero hJ e0
    have hJ1 : (J.filter fun b => ¬ DigitRes f b e0).card ≤ 2 := by
      refine le_trans (Finset.card_le_card ?_) (card_res_succ hJ he0)
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨hb.1, ?_⟩
      rcases hall b hb.1 with ⟨-, h | h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hb.2
      · omega
    have hsplit := Finset.card_filter_add_card_filter_not (s := J) (fun b => DigitRes f b e0)
    have hs := Finset.sum_filter_add_sum_filter_not J (fun b => DigitRes f b e0)
      (fun b => (2 : ℤ) ^ b)
    have h0 : ((2 : ℤ) ^ f - 1) ∣ ∑ b ∈ J.filter (fun b => DigitRes f b e0),
        (2 * 2 ^ b - 2 * 2 ^ e0 : ℤ) := by
      refine Finset.dvd_sum fun b hb => ?_
      rw [Finset.mem_filter] at hb
      have := dvd_mul_of_dvd_right (dvd_pow_sub_of_res hb.2) 2
      convert this using 1; ring
    have h1 : ((2 : ℤ) ^ f - 1) ∣ ∑ b ∈ J.filter (fun b => ¬ DigitRes f b e0),
        (2 * 2 ^ b - 2 ^ e0 : ℤ) := by
      refine Finset.dvd_sum fun b hb => ?_
      rw [Finset.mem_filter] at hb
      rcases hall b hb.1 with ⟨-, h | h⟩ | ⟨h, -⟩
      · have := dvd_pow_sub_of_res h
        convert this using 1; ring
      · exact absurd h hb.2
      · omega
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h0 h1
    have hk : ((2 : ℤ) ^ f - 1) ∣
        ((2 * (J.filter fun b => DigitRes f b e0).card +
          (J.filter fun b => ¬ DigitRes f b e0).card - 1 : ℤ)) * 2 ^ e0 := by
      have := dvd_sub (dvd_sub hd0 h0) h1
      convert this using 1
      have hs' : a = ∑ b ∈ J.filter (fun b => DigitRes f b e0), (2 : ℤ) ^ b +
          ∑ b ∈ J.filter (fun b => ¬ DigitRes f b e0), (2 : ℤ) ^ b := by rw [hs, ha]
      rw [hs']; ring
    refine not_dvd_small hf (k := 2 * (J.filter fun b => DigitRes f b e0).card +
          (J.filter fun b => ¬ DigitRes f b e0).card - 1) ?_ ?_ e0 hk
    · omega
    · omega
  ·
    have hJs : J ⊆ J.filter fun b => DigitRes f (b + 1) e0 := by
      intro b hb
      rw [Finset.mem_filter]
      refine ⟨hb, ?_⟩
      rcases hall b hb with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    have hJ2 := (Finset.card_le_card hJs).trans (card_res_succ hJ he0)
    have h1 : ((2 : ℤ) ^ f - 1) ∣ ∑ b ∈ J, (2 * 2 ^ b - 2 ^ e0 : ℤ) := by
      refine Finset.dvd_sum fun b hb => ?_
      have := dvd_pow_sub_of_res (Finset.mem_filter.1 (hJs hb)).2
      convert this using 1; ring
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      ← ha] at h1
    have hk : ((2 : ℤ) ^ f - 1) ∣ ((J.card + 1 : ℤ)) * 2 ^ e0 := by
      have := dvd_sub (by simpa using hd0 : ((2 : ℤ) ^ f - 1) ∣ 2 * a + 2 ^ e0) h1
      convert this using 1; ring
    exact not_dvd_small hf (k := J.card + 1) (by omega) (by omega) e0 hk

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc
