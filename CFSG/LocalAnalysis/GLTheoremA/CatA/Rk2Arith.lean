module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Num

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

@[expose] def rk2Norm (lab : GLALabel) : GLALabel :=
  ⟨if lab.tag = .C then .B else lab.tag, lab.rank, lab.n⟩

section Count

theorem rk2Cnt_large (fs : List (ℕ × Bool)) (N : ℕ) (hfs : ∀ f ∈ fs, 0 < f.1 ∧ 2 * f.1 ≤ N) {m : ℕ}
    (hm : N < m) : rk2Cnt fs m = 0 := by
  unfold rk2Cnt
  rw [List.countP_eq_zero]
  intro f hf
  obtain ⟨h1, h2⟩ := hfs f hf
  cases hb : f.2
  · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq, not_and, not_not]
    intro hd
    exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
  · simp only [↓reduceIte, decide_eq_true_eq]
    intro hd
    exact absurd (Nat.le_of_dvd h1 hd) (by omega)

private theorem E6_small : ∀ m < 61,
    3 ≤ rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m →
      m = 1 ∨ m = 2 ∨ m = 3 := by decide

theorem rk2_E6_ge3 {m : ℕ}
    (h : 3 ≤ rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m) :
    m = 1 ∨ m = 2 ∨ m = 3 := by
  by_cases hm : m ≤ 60
  · exact E6_small m (by omega) h
  · have := rk2Cnt_large [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem E6_le_four_small : ∀ m < 61, 2 ≤ m →
    rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m ≤ 4 := by decide

theorem rk2Cnt_E6_le_four {m : ℕ} (hm : 2 ≤ m) :
    rk2Cnt [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] m ≤ 4 := by
  by_cases h : m < 61
  · exact E6_le_four_small m h hm
  · have := rk2Cnt_large [(2, true), (5, true), (6, true), (8, true), (9, true), (12, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (m := m)
      (by omega)
    omega

private theorem E7_small : ∀ m < 61,
    3 ≤ rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] m →
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by decide

theorem rk2_E7_ge3 {m : ℕ}
    (h : 3 ≤ rk2Cnt [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] m) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 6 := by
  by_cases hm : m ≤ 60
  · exact E7_small m (by omega) h
  · have := rk2Cnt_large [(2, true), (6, true), (8, true), (10, true), (12, true), (14, true), (18, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem E8_small : ∀ m < 61,
    3 ≤ rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)] m →
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 := by decide

theorem rk2_E8_ge3 {m : ℕ}
    (h : 3 ≤ rk2Cnt [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)] m) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 := by
  by_cases hm : m ≤ 60
  · exact E8_small m (by omega) h
  · have := rk2Cnt_large [(2, true), (8, true), (12, true), (14, true), (18, true), (20, true), (24, true), (30, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem F4_small : ∀ m < 61, 3 ≤ rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m →
    m = 1 ∨ m = 2 := by decide

theorem rk2_F4_ge3 {m : ℕ} (h : 3 ≤ rk2Cnt [(2, true), (6, true), (8, true), (12, true)] m) :
    m = 1 ∨ m = 2 := by
  by_cases hm : m ≤ 60
  · exact F4_small m (by omega) h
  · have := rk2Cnt_large [(2, true), (6, true), (8, true), (12, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem twE6_small : ∀ m < 61,
    3 ≤ rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m →
      m = 1 ∨ m = 2 ∨ m = 6 := by decide

theorem rk2_twE6_ge3 {m : ℕ}
    (h : 3 ≤ rk2Cnt [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] m) :
    m = 1 ∨ m = 2 ∨ m = 6 := by
  by_cases hm : m ≤ 60
  · exact twE6_small m (by omega) h
  · have := rk2Cnt_large [(2, true), (5, false), (6, true), (8, true), (9, false), (12, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem triD4_small : ∀ m < 61,
    rk2Cnt [(2, true), (6, true), (12, true)] m - rk2Cnt [(4, true)] m ≤ 2 := by decide

theorem rk2_triD4_le {m : ℕ} :
    rk2Cnt [(2, true), (6, true), (12, true)] m - rk2Cnt [(4, true)] m ≤ 2 := by
  by_cases hm : m ≤ 60
  · exact triD4_small m (by omega)
  · have := rk2Cnt_large [(2, true), (6, true), (12, true)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

private theorem twF4_small : ∀ m < 61, rk2Cnt [(1, true), (3, false), (4, true), (6, false)] m ≤ 2 := by
  decide

theorem rk2_twF4_le {m : ℕ} : rk2Cnt [(1, true), (3, false), (4, true), (6, false)] m ≤ 2 := by
  by_cases hm : m ≤ 60
  · exact twF4_small m (by omega)
  · have := rk2Cnt_large [(1, true), (3, false), (4, true), (6, false)] 60
      (by intro f hf; simp at hf; rcases hf with rfl | rfl | rfl | rfl <;> simp) (m := m) (by omega)
    omega

theorem rk2_G2_le {m : ℕ} : rk2Cnt [(2, true), (6, true)] m ≤ 2 := by
  unfold rk2Cnt
  exact List.countP_le_length

theorem rk2_twB2_le {m : ℕ} : rk2Cnt [(1, true), (2, false)] m ≤ 2 := by
  unfold rk2Cnt
  exact List.countP_le_length

end Count

section Half

variable {p : ℕ} {lab : GLALabel} {c : Prop}

theorem rk2_half_of_split (h : GLASplit16 p lab) : GLAHalfSplit16 p lab c := Or.inl h

theorem rk2_split_untw (ht : CFSG.Assembly.LargeEvenUntwisted lab.tag) (hd : p ∣ 2 ^ lab.n - 1) :
    GLASplit16 p lab := Or.inl ⟨ht, hd⟩

theorem rk2_split_tw (ht : ¬ CFSG.Assembly.LargeEvenUntwisted lab.tag) (h1 : lab.tag ≠ .twB2)
    (h2 : lab.tag ≠ .twF4) (hd : p ∣ 2 ^ lab.n + 1) : GLASplit16 p lab :=
  Or.inr (Or.inl ⟨ht, h1, h2, hd⟩)

theorem rk2_split_c (ht : lab.tag = .twD ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4)
    (hd : p ∣ 2 ^ lab.n - 1) : GLASplit16 p lab := Or.inr (Or.inr (Or.inl ⟨ht, hd⟩))

theorem rk2_split_n1 (hn : lab.n = 1) (hp : p = 3) : GLASplit16 p lab :=
  Or.inr (Or.inr (Or.inr ⟨hn, hp⟩))

theorem rk2_half_b (ht : lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hd : p ∣ 2 ^ lab.n + 1) : GLAHalfSplit16 p lab c := Or.inr (Or.inl ⟨ht, hd⟩)

theorem rk2_half_c (ht : (lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6) (hd : p ∣ 2 ^ lab.n - 1) :
    GLAHalfSplit16 p lab c := Or.inr (Or.inr (Or.inl ⟨ht, hd⟩))

theorem rk2_half_d (ht : (lab.tag = .A ∧ lab.rank = 5) ∨ lab.tag = .E6) (hn : lab.n = 2) (hc : c)
    (hp : p = 5) : GLAHalfSplit16 p lab c := Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hn, hc, hp⟩)))

theorem rk2_half_e1 (ht : lab.tag = .A) (hr : lab.rank = 8) (hn : lab.n = 1) (hp : p = 7) :
    GLAHalfSplit16 p lab c := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hr, hn, hp⟩))))

theorem rk2_half_e2 (ht : lab.tag = .E6) (hn : lab.n = 1) (hp : p = 7) : GLAHalfSplit16 p lab c :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, hn, hp⟩))))

end Half

section Tags

variable {p : ℕ} {c : Prop} {e : ℕ}

private theorem prime_eq_five {p : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ 2 + 1) : p = 5 :=
  (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (by simpa using h)

theorem rk2_half_A {ℓ n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hE : Rk2ELowAt ⟨.A, ℓ, n⟩ c e)
    (hr : 3 ≤ rk2Mult ⟨.A, ℓ, n⟩ (rk2Ord p n)) (he : e ≤ rk2Mult ⟨.A, ℓ, n⟩ (rk2Ord p n) + 1) :
    GLAHalfSplit16 p ⟨.A, ℓ, n⟩ c := by
  by_cases hm1 : rk2Ord p n = 1
  · exact rk2_half_of_split (rk2_split_untw trivial (rk2Ord_eq_one_iff.1 hm1))
  have hmpos := rk2Ord_pos hp hp2 n
  have hmult : rk2Mult ⟨.A, ℓ, n⟩ (rk2Ord p n) = (ℓ + 1) / rk2Ord p n := by simp [rk2Mult, hm1]
  rw [hmult] at hr he
  generalize hm : rk2Ord p n = m at *
  have h3m : 3 * m ≤ ℓ + 1 := (Nat.le_div_iff_mul_le hmpos).1 hr
  by_cases hn1 : n = 1
  · subst hn1
    by_cases hp3 : p = 3
    · exact rk2_half_of_split (rk2_split_n1 rfl hp3)
    have hm3 : 3 ≤ m := by
      by_contra hlt
      have h2 : m = 2 := by omega
      exact hp3 ((rk2Ord_one_eq_two_iff hp hp2).1 (hm.trans h2))
    have hq : (ℓ + 1) / m ≤ (ℓ + 1) / 3 := Nat.div_le_div_left hm3 (by norm_num)
    have hlow := hE.a_one rfl rfl
    have h8 : ℓ = 8 ∧ m = 3 := by simp only at hlow; omega
    obtain ⟨hℓ, hm3'⟩ := h8
    exact rk2_half_e1 rfl hℓ rfl ((rk2Ord_one_eq_three_iff hp).1 (hm.trans hm3'))
  · have hn2 : 2 ≤ n := by
      have := hmpos
      by_contra hlt
      have : n = 0 := by omega
      subst this
      have h1 : rk2Ord p 0 = 1 := by simp [rk2Ord]
      omega
    have hm2 : 2 ≤ m := by omega
    have hq : (ℓ + 1) / m ≤ (ℓ + 1) / 2 := Nat.div_le_div_left hm2 (by norm_num)
    have hlow := hE.a_ge rfl hn2
    have h5 : ℓ = 5 ∧ m = 2 := by simp only at hlow; omega
    obtain ⟨hℓ, hm2'⟩ := h5
    by_cases hc : c
    · by_cases hn3 : 3 ≤ n
      · exfalso
        have := hE.a_five ⟨rfl, hℓ, hn2⟩ (Or.inl hn3)
        subst hℓ
        subst hm2'
        omega
      · have hn2' : n = 2 := by omega
        have hp5 : p = 5 := prime_eq_five hp (by
          have := (rk2Ord_eq_two_iff hp hp2 (n := n)).1 (hm.trans hm2')
          rwa [hn2'] at this)
        exact rk2_half_d (Or.inl ⟨rfl, hℓ⟩) hn2' hc hp5
    · exfalso
      have := hE.a_five ⟨rfl, hℓ, hn2⟩ (Or.inr hc)
      subst hℓ
      subst hm2'
      omega

theorem rk2Norm_of_ne {lab : GLALabel} (h : lab.tag ≠ .C) : rk2Norm lab = lab := by
  obtain ⟨t, ℓ, n⟩ := lab
  simp only at h
  simp [rk2Norm, h]

theorem rk2Norm_tag_of_C {lab : GLALabel} (h : lab.tag = .C) : (rk2Norm lab).tag = .B := by
  simp [rk2Norm, h]

@[simp] theorem rk2Norm_n (lab : GLALabel) : (rk2Norm lab).n = lab.n := rfl

@[simp] theorem rk2Norm_rank (lab : GLALabel) : (rk2Norm lab).rank = lab.rank := rfl

private theorem rk2_bcdiv_le (ℓ m : ℕ) (hm : 3 ≤ m) :
    (if m % 2 = 0 then 2 * ℓ / m else ℓ / m) ≤ ℓ / 2 := by
  split_ifs with h
  · have hm4 : 4 ≤ m := by omega
    calc 2 * ℓ / m ≤ 2 * ℓ / 4 := Nat.div_le_div_left hm4 (by norm_num)
      _ = ℓ / 2 := by omega
  · calc ℓ / m ≤ ℓ / 3 := Nat.div_le_div_left hm (by norm_num)
      _ ≤ ℓ / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)

theorem rk2Mult_bcd_le {lab : GLALabel}
    (ht : lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) {m : ℕ} (hm : 3 ≤ m) :
    rk2Mult lab m ≤ lab.rank / 2 := by
  have h := rk2_bcdiv_le lab.rank m hm
  rcases ht with ht | ht | ht | ht
  · simpa [rk2Mult, ht] using h
  · simpa [rk2Mult, ht] using h
  · simp only [rk2Mult, ht]
    split_ifs at h ⊢ <;> omega
  · simp only [rk2Mult, ht]
    split_ifs at h ⊢ <;> omega

theorem rk2Mult_twA_le {lab : GLALabel} (ht : lab.tag = .twA) {m : ℕ} (hm : 3 ≤ m) :
    rk2Mult lab m ≤ (lab.rank + 1) / 3 := by
  simp only [rk2Mult, ht]
  have h2 : m ≠ 2 := by omega
  simp only [h2, ↓reduceIte]
  split_ifs with h4 h1
  · have hm6 : 6 ≤ m := by omega
    calc 2 * (lab.rank + 1) / m ≤ 2 * (lab.rank + 1) / 6 := Nat.div_le_div_left hm6 (by norm_num)
      _ = (lab.rank + 1) / 3 := by omega
  · have hm6 : 6 ≤ 2 * m := by omega
    calc (lab.rank + 1) / (2 * m) ≤ (lab.rank + 1) / 6 := Nat.div_le_div_left hm6 (by norm_num)
      _ ≤ (lab.rank + 1) / 3 := Nat.div_le_div_left (by norm_num) (by norm_num)
  · have hm4 : 4 ≤ m := by omega
    calc (lab.rank + 1) / m ≤ (lab.rank + 1) / 4 := Nat.div_le_div_left hm4 (by norm_num)
      _ ≤ (lab.rank + 1) / 3 := Nat.div_le_div_left (by norm_num) (by norm_num)

end Tags

end CFSG.LocalAnalysis.GLTheoremA
