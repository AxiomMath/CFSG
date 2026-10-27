module

public import Mathlib.GroupTheory.Sylow
import CFSG.Mathlib.GroupTheory.PermCommute
import CFSG.Quasithin.Recognition.HSTypeOutS5
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.OddStandard.SmallF3.Omega

private theorem sec5pe8s_perm4_no_order_six :
    ∀ σ : Equiv.Perm (Fin 4), σ ^ 6 = 1 → σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by
  decide +kernel

private theorem sec5pe8s_odd_dvd_24 {n : ℕ} (hn : n ∣ 24) (ho : Odd n) : n = 1 ∨ n = 3 := by
  have hc : n.Coprime 8 := by
    have h2 : n.Coprime 2 := ho.coprime_two_right
    have h3 : n.Coprime (2 ^ 3) :=
      (Nat.coprime_pow_right_iff (by norm_num : 0 < 3) n 2).mpr h2
    simpa only [show (2 : ℕ) ^ 3 = 8 by norm_num] using h3
  have h3 : n ∣ 3 := by
    refine (Nat.Coprime.dvd_mul_left hc).mp ?_
    rw [show (8 : ℕ) * 3 = 24 by norm_num]
    exact hn
  exact (Nat.dvd_prime Nat.prime_three).mp h3

theorem sec5pe8s_aut_eq_one_of_perm_four {Y : Type} [Group Y] (P : Sylow 2 Y)
    (e : Y ≃* Equiv.Perm (Fin 4)) (κ : MulAut Y) (hodd : Odd (orderOf κ))
    (hfix : ∀ x ∈ (P : Subgroup Y), κ x = x) : κ = 1 := by
  classical
  haveI : Fintype Y := Fintype.ofEquiv (Equiv.Perm (Fin 4)) e.toEquiv.symm
  obtain ⟨ρ, hρ⟩ := CFSG.Quasithin.HSType.perm_four_aut_inner (e.symm.trans (κ.trans e))
  let l : Y := e.symm ρ
  have hl : ∀ x : Y, κ x = l * x * l⁻¹ := by
    intro x
    change κ x = e.symm ρ * x * (e.symm ρ)⁻¹
    apply e.injective
    have h := hρ (e x)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
    rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hZ : ∀ y : Y, (∀ x : Y, y * x = x * y) → y = 1 := by
    intro y hy
    apply e.injective
    rw [map_one]
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro σ
    obtain ⟨x, rfl⟩ := e.surjective σ
    rw [← map_mul, ← map_mul, hy x]
  set m : ℕ := orderOf κ with hm
  have hpow : ∀ k : ℕ, ∀ x : Y, (κ ^ k) x = l ^ k * x * (l ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have h1 : (κ ^ (k + 1)) x = (κ ^ k) (κ x) := by
          rw [pow_succ, MulAut.mul_apply]
        rw [h1, ih (κ x), hl x, pow_succ]
        group
  have hcent : l ^ m = 1 := by
    apply hZ
    intro x
    have h1 : (κ ^ m) x = l ^ m * x * (l ^ m)⁻¹ := hpow m x
    have h2 : (κ ^ m) x = x := by
      rw [hm, pow_orderOf_eq_one]
      rfl
    rw [h2] at h1
    calc l ^ m * x = l ^ m * x * (l ^ m)⁻¹ * l ^ m := by group
      _ = x * l ^ m := by rw [← h1]
  have hdvd : orderOf l ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hcent
  have hoddm : Odd m := by rw [hm]; exact hodd
  have hoddl : Odd (orderOf l) := hoddm.of_dvd_nat hdvd
  have hcardY : Nat.card Y = 24 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num
  have hcardP_dvd : 2 ∣ Nat.card ↥(P : Subgroup Y) := by
    rw [Sylow.card_eq_multiplicity (P := P), hcardY]
    have hle : 1 ≤ Nat.factorization 24 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two (by norm_num)).mp (by norm_num)
    simpa only [pow_one] using pow_dvd_pow 2 hle
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup Y)) 2 hcardP_dvd
  let d : Y := x
  have hdP : d ∈ (P : Subgroup Y) := x.2
  have hdord : orderOf d = 2 := by
    change orderOf (x : Y) = 2
    rw [Subgroup.orderOf_coe, hx]
  have hcomm_ld : Commute l d := by
    rw [commute_iff_eq]
    have hk : κ d = d := hfix d hdP
    have h := hl d
    rw [hk] at h
    calc l * d = l * d * l⁻¹ * l := by group
      _ = d * l := by rw [← h]
  have hcases : orderOf l = 1 ∨ orderOf l = 3 := by
    refine sec5pe8s_odd_dvd_24 ?_ hoddl
    rw [← hcardY]
    exact orderOf_dvd_natCard l
  rcases hcases with h1 | h3
  · have hl1 : l = 1 := orderOf_eq_one_iff.mp h1
    ext x
    rw [hl x, hl1]
    simp
  · exfalso
    have hco : (orderOf l).Coprime (orderOf d) := by
      rw [h3, hdord]
      norm_num
    have h6 : orderOf (l * d) = 6 := by
      rw [hcomm_ld.orderOf_mul_eq_mul_orderOf_of_coprime hco, h3, hdord]
    have h6' : orderOf (e (l * d)) = 6 := by
      rw [MulEquiv.orderOf_eq, h6]
    have h6p : (e (l * d)) ^ 6 = 1 := by
      rw [← h6', pow_orderOf_eq_one]
    rcases sec5pe8s_perm4_no_order_six (e (l * d)) h6p with h | h
    · have hd2 : orderOf (e (l * d)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [h6'] at hd2
      obtain ⟨k, hk⟩ := hd2
      omega
    · have hd3 : orderOf (e (l * d)) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h
      rw [h6'] at hd3
      obtain ⟨k, hk⟩ := hd3
      omega

end CFSG.OddStandard.SmallF3.Omega
