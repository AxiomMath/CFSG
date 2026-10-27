module

public import CFSG.Certificates.Kernel.SporSch.SylowCover
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.KS.SporSch.J2OG

open CFSG.KS.SylowCount Subgroup

variable {G : Type*} [Group G] [Finite G]

structure J2Data (G : Type*) [Group G] (a b u v x₇ y z : G) : Prop where
  card : Nat.card G = 604800
  ha : a = y ^ 5
  hu : u = y ^ 3
  oy : orderOf y = 15
  ob : orderOf b = 3
  ov : orderOf v = 5
  ox : orderOf x₇ = 7
  cA : Nat.card (centralizer {a}) ≤ 1080
  cB : Nat.card (centralizer {b}) ≤ 36
  cU : Nat.card (centralizer {u}) ≤ 300
  cV : Nat.card (centralizer {v}) ≤ 50
  s3 : ∃ H : Subgroup G, Nat.card H = 27 ∧ H ≤ centralizer {a} ∧
    ∀ s ∈ H, s = 1 ∨ IsConj a s ∨ IsConj b s
  s5 : ∃ H : Subgroup G, Nat.card H = 25 ∧ H ≤ centralizer {u} ∧
    ∀ s ∈ H, s = 1 ∨ IsConj u s ∨ IsConj (u ^ 2) s ∨ IsConj v s ∨ IsConj (v ^ 2) s
  s5v : ∃ H : Subgroup G, Nat.card H = 25 ∧ H ≤ centralizer {v}
  k4 : ∃ H : Subgroup G, Nat.card H = 4 ∧ H ≤ centralizer {b}
  e4 : ∃ e : G, orderOf e = 4 ∧ e * a = a * e
  e5 : ∃ e : G, orderOf e = 5 ∧ e * a = a * e
  t2 : ∃ t : G, orderOf t = 2 ∧ t * u = u * t
  c7 : ∀ k ∈ [1, 2, 3, 4, 5, 6], IsConj x₇ (x₇ ^ k)
  c15 : ∀ m ∈ [1, 2, 7, 11], IsConj y (y ^ m) ∨ IsConj z (y ^ m)

theorem mem_cent {x e : G} (h : e * x = x * e) : e ∈ centralizer ({x} : Set G) :=
  mem_centralizer_singleton_iff.2 h

theorem orderOf_dvd_cent {x e : G} (h : e * x = x * e) :
    orderOf e ∣ Nat.card (centralizer {x}) := by
  have := orderOf_dvd_natCard (⟨e, mem_cent h⟩ : centralizer ({x} : Set G))
  rwa [← Subgroup.orderOf_coe] at this

theorem isConj_conj (c x : G) : IsConj x (c * x * c⁻¹) := isConj_iff.2 ⟨c, rfl⟩

theorem cent_pos (x : G) : 0 < Nat.card (centralizer ({x} : Set G)) := Nat.card_pos

theorem ord_conj {g h : G} (hc : IsConj g h) : orderOf g = orderOf h := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact (orderOf_conj' c g).symm

theorem pow_part {g : G} {e : ℕ} (he : e ∣ orderOf g) :
    orderOf (g ^ (orderOf g / e)) = e := orderOf_pow_orderOf_div (orderOf_pos g).ne' he

theorem conj_to {h r : G} {k : ℕ} (hc : IsConj r (h ^ k)) :
    ∃ c : G, (c * h * c⁻¹) ^ k = r := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  refine ⟨c⁻¹, ?_⟩
  rw [conj_pow, ← hc]
  group

theorem eq_pow3_sq {x : G} (hx5 : orderOf x = 5) : x = (x ^ 2) ^ 3 := by
  rw [← pow_mul]
  nth_rw 1 [← pow_one x]
  rw [← pow_mod_orderOf x 6, hx5]

theorem divisors_4725 : ∀ d ∈ Nat.divisors 4725,
    d ∈ [1, 3, 5, 7, 15] ∨ ∃ e ∈ [9, 21, 25, 35], e ∣ d := by
  decide +kernel

variable {a b u v x₇ y z : G} (D : J2Data G a b u v x₇ y z)
include D

theorem oa : orderOf a = 3 := by
  rw [D.ha, orderOf_pow_of_dvd (by norm_num) (by rw [D.oy]; norm_num), D.oy]

theorem ou : orderOf u = 5 := by
  rw [D.hu, orderOf_pow_of_dvd (by norm_num) (by rw [D.oy]; norm_num), D.oy]

theorem au : a * u = u * a := by
  rw [D.ha, D.hu, ← pow_add, ← pow_add, add_comm]

theorem dA : 540 ∣ Nat.card (centralizer ({a} : Set G)) := by
  obtain ⟨H, hc, hle, -⟩ := D.s3
  obtain ⟨e, he, hea⟩ := D.e4
  obtain ⟨f, hf, hfa⟩ := D.e5
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := orderOf_dvd_cent hea
  have h3 := orderOf_dvd_cent hfa
  rw [hc] at h1
  rw [he] at h2
  rw [hf] at h3
  have h4 : 4 * 5 ∣ Nat.card (centralizer ({a} : Set G)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 27) (n := 20) (by norm_num) h1 h4

theorem dB : 12 ∣ Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨H, hc, hle⟩ := D.k4
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := orderOf_dvd_cent (x := b) (e := b) rfl
  rw [hc] at h1
  rw [D.ob] at h2
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 4) (n := 3) (by norm_num) h1 h2

theorem dU : 150 ∣ Nat.card (centralizer ({u} : Set G)) := by
  obtain ⟨H, hc, hle, -⟩ := D.s5
  obtain ⟨t, ht, htu⟩ := D.t2
  have h1 := Subgroup.card_dvd_of_le hle
  have h2 := orderOf_dvd_cent htu
  have h3 := orderOf_dvd_cent (au D)
  rw [hc] at h1
  rw [ht] at h2
  rw [oa D] at h3
  have h4 : 2 * 3 ∣ Nat.card (centralizer ({u} : Set G)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 25) (n := 6) (by norm_num) h1 h4

theorem dV : 25 ∣ Nat.card (centralizer ({v} : Set G)) := by
  obtain ⟨H, hc, hle⟩ := D.s5v
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [hc] at h1

theorem not7 {x : G} (hx : x = a ∨ x = b ∨ x = u ∨ x = v) :
    ¬7 ∣ Nat.card (centralizer ({x} : Set G)) := by
  have p := cent_pos x
  rcases hx with rfl | rfl | rfl | rfl
  · have := dA D
    have := D.cA
    omega
  · have := dB D
    have := D.cB
    omega
  · have := dU D
    have := D.cU
    omega
  · have := dV D
    have := D.cV
    omega

theorem three {h : G} {e : ℕ} (he : orderOf h = 3 ^ e) : h = 1 ∨ IsConj a h ∨ IsConj b h := by
  obtain ⟨H, hc, -, hcov⟩ := D.s3
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hcH⟩ := conj_into_of_card (p := 3) (k := 3) H (by rw [hc]; norm_num)
    (by rw [D.card]; norm_num) he
  have hh : IsConj (c * h * c⁻¹) h := (isConj_conj c h).symm
  rcases hcov _ hcH with h1 | h1 | h1
  · left
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  · exact Or.inr (Or.inl (h1.trans hh))
  · exact Or.inr (Or.inr (h1.trans hh))

theorem five {h : G} {e : ℕ} (he : orderOf h = 5 ^ e) :
    h = 1 ∨ IsConj u h ∨ IsConj (u ^ 2) h ∨ IsConj v h ∨ IsConj (v ^ 2) h := by
  obtain ⟨H, hc, -, hcov⟩ := D.s5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hcH⟩ := conj_into_of_card (p := 5) (k := 2) H (by rw [hc]; norm_num)
    (by rw [D.card]; norm_num) he
  have hh : IsConj (c * h * c⁻¹) h := (isConj_conj c h).symm
  rcases hcov _ hcH with h1 | h1 | h1 | h1 | h1
  · left
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  · exact Or.inr (Or.inl (h1.trans hh))
  · exact Or.inr (Or.inr (Or.inl (h1.trans hh)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (h1.trans hh))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (h1.trans hh))))

theorem seven {h : G} (he : orderOf h = 7) : IsConj x₇ h := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨i, hi, hc⟩ := conj_pow_of_orderOf (p := 7) (by rw [D.card]; norm_num) D.ox he
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [pow_zero, isConj_one_right] at hc
    rw [hc, orderOf_one] at he
    omega
  · exact (D.c7 i (by interval_cases i <;> simp)).trans hc

theorem ou2 : orderOf (u ^ 2) = 5 := by
  rw [Nat.Coprime.orderOf_pow (by rw [ou D]; norm_num), ou D]

theorem ov2 : orderOf (v ^ 2) = 5 := by
  rw [Nat.Coprime.orderOf_pow (by rw [D.ov]; norm_num), D.ov]

theorem ord3 {h : G} {e : ℕ} (he : orderOf h = 3 ^ e) : orderOf h = 1 ∨ orderOf h = 3 := by
  rcases three D he with rfl | hc | hc
  · exact Or.inl orderOf_one
  · exact Or.inr ((ord_conj hc).symm.trans (oa D))
  · exact Or.inr ((ord_conj hc).symm.trans D.ob)

theorem ord5 {h : G} {e : ℕ} (he : orderOf h = 5 ^ e) : orderOf h = 1 ∨ orderOf h = 5 := by
  rcases five D he with rfl | hc | hc | hc | hc
  · exact Or.inl orderOf_one
  · exact Or.inr ((ord_conj hc).symm.trans (ou D))
  · exact Or.inr ((ord_conj hc).symm.trans (ou2 D))
  · exact Or.inr ((ord_conj hc).symm.trans D.ov)
  · exact Or.inr ((ord_conj hc).symm.trans (ov2 D))

theorem no_mixed {g : G} {p : ℕ} (hg : orderOf g = p * 7) (hp : p = 3 ∨ p = 5) : False := by
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> norm_num
  have h1 : orderOf (g ^ 7) = p := by
    have := pow_part (g := g) (e := p) (by rw [hg]; exact Dvd.intro 7 rfl)
    rwa [hg, Nat.mul_div_cancel_left 7 hp0] at this
  have h2 : orderOf (g ^ p) = 7 := by
    have := pow_part (g := g) (e := 7) (by rw [hg]; exact Dvd.intro_left p rfl)
    rwa [hg, Nat.mul_div_cancel p (by norm_num : 0 < 7)] at this
  have keyc : ∀ x, (x = a ∨ x = b ∨ x = u ∨ x = v) → ∀ j, (j = 1 ∨ (j = 2 ∧ orderOf x = 5)) →
      IsConj (x ^ j) (g ^ 7) → False := by
    intro x hx j hj hc
    obtain ⟨c, hc⟩ := conj_to hc
    apply not7 D hx
    rw [← h2, ← orderOf_conj' c (g ^ p), ← conj_pow]
    refine orderOf_dvd_cent ?_
    have hcom : (c * g * c⁻¹) ^ p * x ^ j = x ^ j * (c * g * c⁻¹) ^ p := by
      rw [← hc]
      exact (Commute.pow_pow_self _ _ _).eq
    rcases hj with rfl | ⟨rfl, hx5⟩
    · simpa using hcom
    · rw [eq_pow3_sq hx5]
      exact (Commute.pow_right hcom 3).eq
  rcases hp with rfl | rfl
  · rcases three D (e := 1) (by rw [h1, pow_one]) with h0 | hc | hc
    · rw [h0, orderOf_one] at h1
      omega
    · exact keyc a (Or.inl rfl) 1 (Or.inl rfl) (by simpa using hc)
    · exact keyc b (Or.inr (Or.inl rfl)) 1 (Or.inl rfl) (by simpa using hc)
  · rcases five D (e := 1) (by rw [h1, pow_one]) with h0 | hc | hc | hc | hc
    · rw [h0, orderOf_one] at h1
      omega
    · exact keyc u (Or.inr (Or.inr (Or.inl rfl))) 1 (Or.inl rfl) (by simpa using hc)
    · exact keyc u (Or.inr (Or.inr (Or.inl rfl))) 2 (Or.inr ⟨rfl, ou D⟩) hc
    · exact keyc v (Or.inr (Or.inr (Or.inr rfl))) 1 (Or.inl rfl) (by simpa using hc)
    · exact keyc v (Or.inr (Or.inr (Or.inr rfl))) 2 (Or.inr ⟨rfl, D.ov⟩) hc

theorem prod_pow {k i : ℕ} (hk : k = 1 ∨ k = 2) (hi : i = 1 ∨ i = 2) :
    ∃ m ∈ [1, 2, 7, 11], (u ^ k) * (u ^ k) * (a ^ i)⁻¹ = y ^ m := by
  have hy : y ^ 15 = 1 := by
    rw [← D.oy]
    exact pow_orderOf_eq_one y
  rw [D.ha, D.hu]
  rcases hk with rfl | rfl <;> rcases hi with rfl | rfl
  · exact ⟨1, by simp, by group⟩
  · refine ⟨11, by simp, ?_⟩
    calc (y ^ 3) ^ 1 * (y ^ 3) ^ 1 * ((y ^ 5) ^ 2)⁻¹ = (y ^ 3) ^ 1 * (y ^ 3) ^ 1 *
        ((y ^ 5) ^ 2)⁻¹ * y ^ 15 := by rw [hy, mul_one]
      _ = y ^ 11 := by group
  · exact ⟨7, by simp, by group⟩
  · exact ⟨2, by simp, by group⟩

theorem fifteen {g : G} (hg : orderOf g = 15) : IsConj y g ∨ IsConj z g := by
  have h5 : orderOf (g ^ 3) = 5 := by
    have := pow_part (g := g) (e := 5) (by rw [hg]; norm_num)
    rwa [hg] at this
  have key : ∀ x, (x = u ∨ x = v) → ∀ k, (k = 1 ∨ k = 2) → IsConj (x ^ k) (g ^ 3) →
      IsConj y g ∨ IsConj z g := by
    intro x hx k hk hc
    obtain ⟨c, hc⟩ := conj_to hc
    set g' := c * g * c⁻¹ with hg'
    have og : orderOf g' = 15 := by rw [hg', orderOf_conj', hg]
    have hgc : IsConj g' g := (isConj_conj c g).symm
    have o3 : orderOf (g' ^ 5) = 3 := by
      have := pow_part (g := g') (e := 3) (by rw [og]; norm_num)
      rwa [og] at this
    have hx5 : orderOf x = 5 := by rcases hx with rfl | rfl; exacts [ou D, D.ov]
    have hcom : g' ^ 5 * x = x * g' ^ 5 := by
      have h0 : g' ^ 5 * x ^ k = x ^ k * g' ^ 5 := by
        rw [← hc]
        exact (Commute.pow_pow_self _ _ _).eq
      rcases hk with rfl | rfl
      · simpa using h0
      · rw [eq_pow3_sq hx5]
        exact (Commute.pow_right h0 3).eq
    rcases hx with hxu | hxv
    ·
      rw [hxu] at hcom hc
      have hK9' : ¬9 ∣ Nat.card (centralizer ({u} : Set G)) := by
        have := dU D
        have := D.cU
        have := cent_pos u
        omega
      set K := centralizer ({u} : Set G)
      have hK9 : ¬3 ^ 2 ∣ Nat.card K := hK9'
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have haK : a ∈ K := mem_cent (au D)
      have htK : g' ^ 5 ∈ K := mem_cent hcom
      have o0 : orderOf (⟨a, haK⟩ : K) = 3 := by
        rw [← Subgroup.orderOf_coe]
        exact oa D
      have o1 : orderOf (⟨g' ^ 5, htK⟩ : K) = 3 := by
        rw [← Subgroup.orderOf_coe]
        exact o3
      obtain ⟨i, hi, hci⟩ := conj_pow_of_orderOf (p := 3) hK9 o0 o1
      obtain ⟨c', hc'⟩ := isConj_iff.1 hci
      have hc'' : (c' : G) * a ^ i * (c' : G)⁻¹ = g' ^ 5 := by
        have := congrArg Subtype.val hc'
        simpa using this
      have hi0 : i = 1 ∨ i = 2 := by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | h | h
        · rw [pow_zero, mul_one, mul_inv_cancel] at hc''
          rw [← hc'', orderOf_one] at o3
          omega
        · exact Or.inl h
        · exact Or.inr h
      have hcu : (c' : G) * u = u * c' := mem_centralizer_singleton_iff.1 c'.2
      have hcU : (c' : G) * (u ^ k * u ^ k) = (u ^ k * u ^ k) * c' :=
        ((Commute.pow_right hcu k).mul_right (Commute.pow_right hcu k)).eq
      obtain ⟨m, hm, hme⟩ := prod_pow D hk hi0
      have e : g' = (c' : G) * y ^ m * (c' : G)⁻¹ := by
        rw [← hme]
        calc g' = g' ^ 3 * g' ^ 3 * (g' ^ 5)⁻¹ := by group
          _ = u ^ k * u ^ k * ((c' : G) * a ^ i * (c' : G)⁻¹)⁻¹ := by rw [hc, hc'']
          _ = (u ^ k * u ^ k) * c' * (a ^ i)⁻¹ * (c' : G)⁻¹ := by group
          _ = c' * (u ^ k * u ^ k) * (a ^ i)⁻¹ * (c' : G)⁻¹ := by rw [← hcU]
          _ = c' * (u ^ k * u ^ k * (a ^ i)⁻¹) * (c' : G)⁻¹ := by group
      have hym : IsConj (y ^ m) g := by
        rw [e] at hgc
        exact (isConj_conj _ _).trans hgc
      rcases D.c15 m hm with h | h
      · exact Or.inl (h.trans hym)
      · exact Or.inr (h.trans hym)
    · exfalso
      rw [hxv] at hcom
      have h3 := orderOf_dvd_cent hcom
      rw [o3] at h3
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (m := 25) (n := 3) (by norm_num) (dV D) h3
      have := D.cV
      have := cent_pos v
      omega
  rcases five D (e := 1) (by rw [h5, pow_one]) with h0 | hc | hc | hc | hc
  · rw [h0, orderOf_one] at h5
    omega
  · exact key u (Or.inl rfl) 1 (Or.inl rfl) (by simpa using hc)
  · exact key u (Or.inl rfl) 2 (Or.inr rfl) hc
  · exact key v (Or.inr rfl) 1 (Or.inl rfl) (by simpa using hc)
  · exact key v (Or.inr rfl) 2 (Or.inr rfl) hc

theorem odd_cover (g : G) (hg : Nat.Coprime (orderOf g) 2) :
    orderOf g ∈ [1, 3, 5, 7, 15] ∧ (g = 1 ∨ IsConj a g ∨ IsConj b g ∨ IsConj u g ∨
      IsConj (u ^ 2) g ∨ IsConj v g ∨ IsConj (v ^ 2) g ∨ IsConj x₇ g ∨ IsConj y g ∨
      IsConj z g) := by
  have h1 : orderOf g ∣ 4725 * 2 ^ 7 := by
    have := orderOf_dvd_natCard g
    rwa [D.card] at this
  have hd : orderOf g ∣ 4725 := (Nat.Coprime.pow_right 7 hg).dvd_of_dvd_mul_right h1
  have ho : orderOf g ∈ [1, 3, 5, 7, 15] := by
    rcases divisors_4725 _ (Nat.mem_divisors.2 ⟨hd, by norm_num⟩) with h | ⟨e, he, hed⟩
    · exact h
    · exfalso
      have hord := pow_part hed
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · rcases ord3 D (e := 2) hord with h | h <;> rw [hord] at h <;> omega
      · exact no_mixed D (p := 3) hord (Or.inl rfl)
      · rcases ord5 D (e := 2) hord with h | h <;> rw [hord] at h <;> omega
      · exact no_mixed D (p := 5) hord (Or.inr rfl)
  refine ⟨ho, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with h | h | h | h | h
  · exact Or.inl (orderOf_eq_one_iff.1 h)
  · rcases three D (e := 1) (by rw [h, pow_one]) with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · rcases five D (e := 1) (by rw [h, pow_one]) with h' | h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (seven D h))))))))
  · rcases fifteen D h with h' | h'
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))))))

end CFSG.KS.SporSch.J2OG

end
