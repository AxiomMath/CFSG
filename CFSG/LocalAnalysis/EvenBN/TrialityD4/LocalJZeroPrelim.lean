module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalVPrelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

theorem card_le_of_forall_pow_eq_one_D4 {K : Type*} [Group K] [Finite K] [IsCyclic K] {n : ℕ}
    (hn : 0 < n) (h : ∀ x : K, x ^ n = 1) : Nat.card K ≤ n := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hn (orderOf_dvd_of_pow_eq_one (h g))

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem weyl_conj_eq_of_mul_mul_inv_eq {x h w y j j' : X} (hx : x ∈ d.S) (hh : h ∈ d.J)
    (hw : w ∈ d.weyl) (hy : y ∈ d.Uminus w) (hj : j ∈ d.J) (hj' : j' ∈ d.J)
    (hjg : j * (x * h * w * y) * j'⁻¹ = x * h * w * y) : w * j' * w⁻¹ = j := by
  have hwj : w * j'⁻¹ * w⁻¹ ∈ d.J := d.conj_mem_J hw (inv_mem hj')
  have hcomm : h * j = j * h := d.J_commute hh hj
  have e : j * (x * h * w * y) * j'⁻¹ =
      (j * x * j⁻¹) * (h * (j * (w * j'⁻¹ * w⁻¹))) * w * (j' * y * j'⁻¹) := by
    calc j * (x * h * w * y) * j'⁻¹ = j * x * j⁻¹ * (j * h) * w * y * j'⁻¹ := by group
      _ = j * x * j⁻¹ * (h * j) * w * y * j'⁻¹ := by rw [hcomm]
      _ = _ := by group
  rw [e] at hjg
  have hjS : j ∈ normalizer (d.S : Set X) := by
    rw [d.normalizer_S]
    exact le_sup_right (a := d.S) hj
  obtain ⟨-, h2, -, -⟩ := d.bruhat_normal_form_unique
    ((mem_normalizer_iff.1 hjS x).1 hx) (mul_mem hh (mul_mem hj hwj)) hw
    (d.conj_mem_Uminus hj' hy) hx hh hw hy hjg
  have h3 : j * (w * j'⁻¹ * w⁻¹) = 1 := mul_eq_left.1 h2
  have h5 : w * j'⁻¹ * w⁻¹ = j⁻¹ := eq_inv_of_mul_eq_one_right h3
  have h6 := congrArg (·⁻¹) h5
  simpa [mul_assoc] using h6

theorem units_pow_two_pow_three_mul {f : ℕ} (hq : q = 2 ^ f) (m : d.Γˣ) :
    m ^ 2 ^ (3 * f) = m := by
  have h1 : m ^ (q ^ 3 - 1) = 1 := by
    rw [← d.card_units_Γ]
    exact pow_card_eq_one'
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by rw [hq]; positivity)
  have he : q ^ 3 - 1 + 1 = 2 ^ (3 * f) := by
    rw [Nat.sub_add_cancel hq3, hq, ← pow_mul, mul_comm]
  calc m ^ 2 ^ (3 * f) = m ^ (q ^ 3 - 1 + 1) := by rw [he]
    _ = m := by rw [pow_succ, h1, one_mul]

theorem sq_add_le_two_pow_of_forall {s : ℕ} (hs : 1 ≤ s) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (H : ∀ m ∈ d.nmUnits.ker, (m ^ 2 ^ s) ^ ε = m) : q ^ 2 + q ≤ 2 ^ s := by
  have hK := d.card_ker_nmUnits
  have hs1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
  have hs2 : 2 ≤ 2 ^ s := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  rcases hε with rfl | rfl
  · have h1 : ∀ m : d.nmUnits.ker, m ^ (2 ^ s - 1) = 1 := by
      intro m
      have e := H m m.2
      rw [zpow_one] at e
      have e2 : (m : d.Γˣ) ^ (2 ^ s - 1) * m = m := by
        rw [← pow_succ, Nat.sub_add_cancel hs1, e]
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact mul_eq_right.1 e2
    have h2 := card_le_of_forall_pow_eq_one_D4 (by omega) h1
    omega
  · have h1 : ∀ m : d.nmUnits.ker, m ^ (2 ^ s + 1) = 1 := by
      intro m
      have e := H m m.2
      rw [zpow_neg_one] at e
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_succ]
      calc (m : d.Γˣ) ^ 2 ^ s * m = (m : d.Γˣ) ^ 2 ^ s * ((m : d.Γˣ) ^ 2 ^ s)⁻¹ := by rw [e]
        _ = 1 := mul_inv_cancel _
    have h2 := card_le_of_forall_pow_eq_one_D4 (by omega) h1
    omega

theorem not_forall_pow_two_pow_zpow_eq {f : ℕ} (hq : q = 2 ^ f) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : r < 3 * f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ¬ ∀ m ∈ d.nmUnits.ker, (m ^ 2 ^ r) ^ ε = m := by
  intro H
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have H' : ∀ m ∈ d.nmUnits.ker, (m ^ 2 ^ (3 * f - r)) ^ ε = m := by
    intro m hm
    have h1 := H _ (pow_mem hm (2 ^ (3 * f - r)))
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hr.le, d.units_pow_two_pow_three_mul hq] at h1
    rw [← h1, ← zpow_mul, hεε, zpow_one]
  have h1 := d.sq_add_le_two_pow_of_forall hr1 hε H
  have h2 := d.sq_add_le_two_pow_of_forall (by omega) hε H'
  have h3 : (q ^ 2 + q) * (q ^ 2 + q) ≤ q ^ 3 := by
    calc (q ^ 2 + q) * (q ^ 2 + q) ≤ 2 ^ r * 2 ^ (3 * f - r) := Nat.mul_le_mul h1 h2
      _ = q ^ 3 := by rw [← pow_add, Nat.add_sub_cancel' hr.le, hq, ← pow_mul, mul_comm]
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : q ^ 3 * q ≤ (q ^ 2 + q) * (q ^ 2 + q) := by
    have e : q ^ 3 * q = q ^ 2 * q ^ 2 := by ring
    rw [e]
    exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have h5 : q ^ 3 * 2 ≤ q ^ 3 * q := Nat.mul_le_mul_left _ hq2
  have h6 : 0 < q ^ 3 := by positivity
  linarith

theorem exists_conj_of_centralizes_J₀ {f : ℕ} (hq : q = 2 ^ f) {α : MulAut X}
    (hα : ∀ j ∈ d.J₀, α j = j) : ∃ g ∈ centralizer (d.J₀ : Set X), α = MulAut.conj g := by
  obtain ⟨g, k, rfl⟩ := d.aut_eq α
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      have h1 := d.card_Γ
      have he : q ^ 3 = 1 := by rw [hq, h0, pow_zero, one_pow]
      rw [he] at h1
      have h2 : 1 < Nat.card d.Γ := Finite.one_lt_card
      omega
    · exact h0
  have hφ : d.φ ^ k = d.φ ^ (k % (3 * f)) := by
    rw [← d.orderOf_φ_eq_three_mul hq, pow_mod_orderOf]
  obtain ⟨r, hr, hrlt⟩ : ∃ r, r = k % (3 * f) ∧ r < 3 * f := ⟨_, rfl, Nat.mod_lt _ (by omega)⟩
  rw [hφ, ← hr] at hα ⊢
  suffices hk : d.φ ^ r = 1 by
    refine ⟨g, mem_centralizer_iff.2 fun j hj => ?_, by rw [hk, mul_one]⟩
    have e := hα j hj
    rw [hk, mul_one, MulAut.conj_apply] at e
    calc j * g = g * j * g⁻¹ * g := by rw [e]
      _ = g * j := by group
  by_contra hne
  have hr0 : 1 ≤ r := Nat.one_le_iff_ne_zero.2 fun h0 => hne (by rw [h0, pow_zero])
  obtain ⟨x, hx, h, hh, w, hw, y, hy, rfl⟩ := d.exists_bruhat_normal_form g
  obtain ⟨k₀, rfl⟩ := d.exists_weylWord_eq hw
  have hε : uSign (weylList k₀) = 1 ∨ uSign (weylList k₀) = -1 := by
    have h2 : ∀ k : Fin 12, uSign (weylList k) = 1 ∨ uSign (weylList k) = -1 := by decide
    exact h2 k₀
  refine d.not_forall_pow_two_pow_zpow_eq hq hr0 hrlt hε fun m hm => ?_
  have hm1 : d.nmUnits m = 1 := MonoidHom.mem_ker.1 hm
  have hm' : d.nmUnits (m ^ 2 ^ r) = 1 := by rw [map_pow, hm1, one_pow]
  have e1 := hα _ (d.torus_one_mem_J₀ hm1)
  rw [MulAut.mul_apply, d.φ_pow_torus, MulAut.conj_apply, Prod.pow_mk, one_pow] at e1
  have e2 : d.torus (1, m) * (x * h * d.weylWord k₀ * y) * (d.torus (1, m ^ 2 ^ r))⁻¹ =
      x * h * d.weylWord k₀ * y := by
    rw [← e1]
    group
  have e3 := d.weyl_conj_eq_of_mul_mul_inv_eq hx hh hw hy (d.torus_mem_J _) (d.torus_mem_J _) e2
  have e4 := d.word_torus_J₀ (weylList k₀) hm'
  change d.weylWord k₀ * d.torus (1, m ^ 2 ^ r) * (d.weylWord k₀)⁻¹ = _ at e4
  rw [e3] at e4
  exact (congrArg Prod.snd (d.torus_injective e4)).symm

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4
