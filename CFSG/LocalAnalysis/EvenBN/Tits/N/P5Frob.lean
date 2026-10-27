module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup

variable {Γ : Type*} [Group Γ]

structure IsF20 (x y : Γ) : Prop where
  x5 : x ^ 5 = 1
  x_ne : x ≠ 1
  y4 : y ^ 4 = 1
  conj : y * x * y⁻¹ = x ^ 3

@[expose] def F20 (x y : Γ) : Subgroup Γ := zpowers x ⊔ zpowers y

namespace IsF20

variable {x y : Γ}

theorem orderOf_x (h : IsF20 x y) : orderOf x = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime h.x5 h.x_ne

theorem conj_y_pow (h : IsF20 x y) (j i : ℕ) :
    y ^ j * x ^ i * (y ^ j)⁻¹ = x ^ (i * 3 ^ j) := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : y ^ (n + 1) * x ^ i * (y ^ (n + 1))⁻¹ = y * (y ^ n * x ^ i * (y ^ n)⁻¹) * y⁻¹ := by
      rw [pow_succ']; group
    rw [e, ih, ← conj_pow, h.conj, ← pow_mul]
    congr 1
    ring

theorem y_inv_conj (h : IsF20 x y) : y⁻¹ * x * y = x ^ 2 := by
  have h6 : y * x ^ 2 * y⁻¹ = x := by
    have := h.conj_y_pow 1 2
    simp only [pow_one] at this
    rw [this]
    calc x ^ (2 * 3) = x * x ^ 5 := by rw [← pow_succ']
      _ = x := by rw [h.x5, mul_one]
  calc y⁻¹ * x * y = y⁻¹ * (y * x ^ 2 * y⁻¹) * y := by rw [h6]
    _ = x ^ 2 := by group

theorem orderOf_y (h : IsF20 x y) : orderOf y = 4 := by
  have hy2 : ¬ y ^ 2 = 1 := by
    intro hy
    have h9 := h.conj_y_pow 2 1
    rw [hy] at h9
    simp only [one_mul, inv_one, mul_one, pow_one] at h9
    have h8 : x ^ 8 = 1 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at h9
      calc x ^ 8 = x ^ 9 * x⁻¹ := by group
        _ = 1 := by rw [← h9]; group
    have := (pow_gcd_eq_one (a := x)).2 ⟨h8, h.x5⟩
    simp at this
    exact h.x_ne this
  have hy4 : y ^ 2 ^ (1 + 1) = 1 := by simpa using h.y4
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := y) (by simpa using hy2) hy4
  simpa using this

theorem y_mem_normalizer (h : IsF20 x y) :
    y ∈ normalizer ((zpowers x : Subgroup Γ) : Set Γ) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    rw [← conj_zpow, h.conj, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (mem_zpowers x) _
  · intro hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hg
    have hc := conj_zpow (a := y⁻¹) (b := x) (i := k)
    rw [inv_inv] at hc
    have : g = (y⁻¹ * x * y) ^ k := by
      rw [hc, hk]
      group
    rw [this, h.y_inv_conj, ← zpow_natCast, ← zpow_mul]
    exact Subgroup.zpow_mem _ (mem_zpowers x) _

theorem disjoint_zpowers (h : IsF20 x y) : Disjoint (zpowers x) (zpowers y) := by
  rw [disjoint_iff]
  have hc : Nat.Coprime (Nat.card (zpowers x)) (Nat.card (zpowers y)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_x, h.orderOf_y]
    decide
  exact Subgroup.inf_eq_bot_of_coprime hc

theorem mem_F20_iff (h : IsF20 x y) {f : Γ} : f ∈ F20 x y ↔ ∃ i j : ℕ, f = x ^ i * y ^ j := by
  have hle : zpowers y ≤ normalizer ((zpowers x : Subgroup Γ) : Set Γ) :=
    (zpowers_le).2 h.y_mem_normalizer
  have hx : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨5, by norm_num, h.x5⟩
  have hy : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.2 ⟨4, by norm_num, h.y4⟩
  constructor
  · intro hf
    have hs : f ∈ ((zpowers x ⊔ zpowers y : Subgroup Γ) : Set Γ) := hf
    rw [coe_mul_of_right_le_normalizer_left _ _ hle] at hs
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    obtain ⟨i, hi⟩ := (hx.mem_powers_iff_mem_zpowers).2 ha
    obtain ⟨j, hj⟩ := (hy.mem_powers_iff_mem_zpowers).2 hb
    exact ⟨i, j, by simp only at hi hj; rw [hi, hj]⟩
  · rintro ⟨i, j, rfl⟩
    exact mul_mem (mem_sup_left (Subgroup.pow_mem _ (mem_zpowers x) i))
      (mem_sup_right (Subgroup.pow_mem _ (mem_zpowers y) j))

theorem card_F20 [Finite Γ] (h : IsF20 x y) : Nat.card (F20 x y) = 20 := by
  have hle : zpowers y ≤ normalizer ((zpowers x : Subgroup Γ) : Set Γ) :=
    (zpowers_le).2 h.y_mem_normalizer
  rw [F20, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hle
    h.disjoint_zpowers, Nat.card_zpowers, Nat.card_zpowers, h.orderOf_x, h.orderOf_y]

theorem y_sq_conj (h : IsF20 x y) : y ^ 2 * x * (y ^ 2)⁻¹ = x⁻¹ := by
  have h9 := h.conj_y_pow 2 1
  rw [pow_one] at h9
  rw [h9]
  have : x ^ (1 * 3 ^ 2) * x = 1 := by
    calc x ^ (1 * 3 ^ 2) * x = x ^ 5 * x ^ 5 := by
          rw [← pow_succ]; norm_num
          rw [← pow_add]
      _ = 1 := by rw [h.x5, one_mul]
  exact eq_inv_of_mul_eq_one_left this

theorem exists_form (h : IsF20 x y) {f : Γ} (hf : f ∈ F20 x y) :
    ∃ i j : ℕ, i < 5 ∧ j < 4 ∧ f = x ^ i * y ^ j := by
  obtain ⟨i, j, rfl⟩ := h.mem_F20_iff.1 hf
  refine ⟨i % 5, j % 4, Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← h.orderOf_x, ← h.orderOf_y, pow_mod_orderOf, pow_mod_orderOf]

theorem sq_form (h : IsF20 x y) (i j : ℕ) :
    (x ^ i * y ^ j) * (x ^ i * y ^ j) = x ^ (i + i * 3 ^ j) * y ^ (2 * j) := by
  have e := h.conj_y_pow j i
  calc (x ^ i * y ^ j) * (x ^ i * y ^ j)
      = x ^ i * (y ^ j * x ^ i * (y ^ j)⁻¹) * (y ^ j * y ^ j) := by group
    _ = x ^ (i + i * 3 ^ j) * y ^ (2 * j) := by
      rw [e, ← pow_add, ← pow_add, two_mul]

theorem pow_eq_one_of_two_mul (h : IsF20 x y) {k : ℕ} (hk : x ^ (2 * k) = 1) : x ^ k = 1 := by
  have h5 : 5 ∣ 2 * k := by rw [← h.orderOf_x]; exact orderOf_dvd_of_pow_eq_one hk
  have h5k : 5 ∣ k := by omega
  rw [← h.orderOf_x] at h5k
  exact orderOf_dvd_iff_pow_eq_one.1 h5k

theorem involution_form (h : IsF20 x y) {f : Γ} (hf : f ∈ F20 x y) (hf2 : f * f = 1)
    (hf1 : f ≠ 1) : ∃ i : ℕ, f = x ^ i * y ^ 2 := by
  obtain ⟨i, j, hi, hj, rfl⟩ := h.exists_form hf
  have hf2' := hf2
  rw [h.sq_form] at hf2'
  have hyj : y ^ (2 * j) = (x ^ (i + i * 3 ^ j))⁻¹ := eq_inv_of_mul_eq_one_right hf2'
  have hmem : y ^ (2 * j) ∈ zpowers x ⊓ zpowers y := by
    refine ⟨?_, Subgroup.pow_mem _ (mem_zpowers y) _⟩
    rw [hyj]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_zpowers x) _)
  have hy1 : y ^ (2 * j) = 1 := by
    have := h.disjoint_zpowers
    rw [disjoint_iff] at this
    rw [this] at hmem
    exact mem_bot.1 hmem
  have hdvd : 4 ∣ 2 * j := by
    rw [← h.orderOf_y]; exact orderOf_dvd_of_pow_eq_one hy1
  have hj' : j = 0 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl
  · exfalso
    apply hf1
    have hx2 : x ^ (2 * i) = 1 := by
      have := hf2'
      simp only [pow_zero, mul_one, mul_zero] at this
      rw [two_mul]
      exact this
    simp [h.pow_eq_one_of_two_mul hx2]
  · exact ⟨i, rfl⟩

theorem inv_of_involution (h : IsF20 x y) {f : Γ} (hf : f ∈ F20 x y) (hf2 : f * f = 1)
    (hf1 : f ≠ 1) : f * x * f⁻¹ = x⁻¹ := by
  obtain ⟨i, rfl⟩ := h.involution_form hf hf2 hf1
  calc (x ^ i * y ^ 2) * x * (x ^ i * y ^ 2)⁻¹
      = x ^ i * (y ^ 2 * x * (y ^ 2)⁻¹) * (x ^ i)⁻¹ := by group
    _ = x⁻¹ := by rw [h.y_sq_conj]; group

theorem F20_le_normalizer (h : IsF20 x y) :
    F20 x y ≤ normalizer ((zpowers x : Subgroup Γ) : Set Γ) :=
  sup_le Subgroup.le_normalizer ((zpowers_le).2 h.y_mem_normalizer)

theorem eq_of_involutions_comm (h : IsF20 x y) {f g : Γ} (hf : f ∈ F20 x y) (hg : g ∈ F20 x y)
    (hf2 : f * f = 1) (hg2 : g * g = 1) (hf1 : f ≠ 1) (hg1 : g ≠ 1) (hfg : f * g = g * f) :
    f = g := by
  obtain ⟨i, rfl⟩ := h.involution_form hf hf2 hf1
  obtain ⟨j, rfl⟩ := h.involution_form hg hg2 hg1
  have hmul : (x ^ i * y ^ 2) * (x ^ j * y ^ 2) = x ^ (i + j * 3 ^ 2) := by
    have e := h.conj_y_pow 2 j
    calc (x ^ i * y ^ 2) * (x ^ j * y ^ 2)
        = x ^ i * (y ^ 2 * x ^ j * (y ^ 2)⁻¹) * (y ^ 2 * y ^ 2) := by group
      _ = x ^ (i + j * 3 ^ 2) := by
        rw [e, ← pow_add]
        have : y ^ 2 * y ^ 2 = 1 := by rw [← pow_add]; exact h.y4
        rw [this, mul_one]
  have hsq : ((x ^ i * y ^ 2) * (x ^ j * y ^ 2)) * ((x ^ i * y ^ 2) * (x ^ j * y ^ 2)) = 1 := by
    calc ((x ^ i * y ^ 2) * (x ^ j * y ^ 2)) * ((x ^ i * y ^ 2) * (x ^ j * y ^ 2))
        = (x ^ i * y ^ 2) * ((x ^ j * y ^ 2) * (x ^ i * y ^ 2)) * (x ^ j * y ^ 2) := by group
      _ = (x ^ i * y ^ 2) * ((x ^ i * y ^ 2) * (x ^ j * y ^ 2)) * (x ^ j * y ^ 2) := by rw [hfg]
      _ = ((x ^ i * y ^ 2) * (x ^ i * y ^ 2)) * ((x ^ j * y ^ 2) * (x ^ j * y ^ 2)) := by group
      _ = 1 := by rw [hf2, hg2, one_mul]
  rw [hmul, ← pow_add, ← two_mul] at hsq
  have hm : x ^ (i + j * 3 ^ 2) = 1 := h.pow_eq_one_of_two_mul hsq
  rw [hm] at hmul
  have hinv : (x ^ i * y ^ 2) = (x ^ j * y ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [hinv]
  exact inv_eq_of_mul_eq_one_right hg2

theorem centralizer_x (h : IsF20 x y) {f : Γ} (hf : f ∈ F20 x y) (hfx : f * x = x * f) :
    f ∈ zpowers x := by
  obtain ⟨i, j, hi, hj, rfl⟩ := h.exists_form hf
  have hyx : y ^ j * x = x * y ^ j := by
    have : x ^ i * (y ^ j * x) = x ^ i * (x * y ^ j) := by
      calc x ^ i * (y ^ j * x) = (x ^ i * y ^ j) * x := by group
        _ = x * (x ^ i * y ^ j) := hfx
        _ = x ^ i * (x * y ^ j) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ']
    exact mul_left_cancel this
  have hxj : x ^ (3 ^ j) = x := by
    have e := h.conj_y_pow j 1
    rw [pow_one, one_mul] at e
    rw [← e]
    calc y ^ j * x * (y ^ j)⁻¹ = x * y ^ j * (y ^ j)⁻¹ := by rw [hyx]
      _ = x := by group
  have hj0 : j = 0 := by
    have hdvd : 5 ∣ 3 ^ j - 1 := by
      have h1 : x ^ (3 ^ j - 1) = 1 := by
        have : x ^ (3 ^ j - 1) * x = x := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num))]
          exact hxj
        simpa using this
      rw [← h.orderOf_x]
      exact orderOf_dvd_of_pow_eq_one h1
    interval_cases j
    · rfl
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
  subst hj0
  simpa using Subgroup.pow_mem _ (mem_zpowers x) i

theorem normal_eq_bot (h : IsF20 x y) {N : Subgroup Γ} (hN : N ≤ F20 x y)
    (hNn : ∀ n ∈ N, ∀ f ∈ F20 x y, f * n * f⁻¹ ∈ N) (hNx : N ⊓ zpowers x = ⊥) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  have hxF : x ∈ F20 x y := mem_sup_left (mem_zpowers x)
  have hnF : n ∈ F20 x y := hN hn
  have h1 : n * x * n⁻¹ * x⁻¹ ∈ N := by
    have := hNn n⁻¹ (N.inv_mem hn) x hxF
    have e : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by group
    rw [e]
    exact N.mul_mem hn this
  have h2 : n * x * n⁻¹ * x⁻¹ ∈ zpowers x := by
    have hnorm := (mem_normalizer_iff.1 (h.F20_le_normalizer hnF) x).1 (mem_zpowers x)
    exact mul_mem hnorm (inv_mem (mem_zpowers x))
  have h3 : n * x * n⁻¹ * x⁻¹ ∈ N ⊓ zpowers x := ⟨h1, h2⟩
  rw [hNx, mem_bot] at h3
  have hc : n * x = x * n := by
    have : n * x * n⁻¹ = x := by
      calc n * x * n⁻¹ = (n * x * n⁻¹ * x⁻¹) * x := by group
        _ = x := by rw [h3, one_mul]
    calc n * x = (n * x * n⁻¹) * n := by group
      _ = x * n := by rw [this]
  have hnx : n ∈ zpowers x := h.centralizer_x hnF hc
  have : n ∈ N ⊓ zpowers x := ⟨hn, hnx⟩
  rw [hNx] at this
  exact this

end IsF20

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
