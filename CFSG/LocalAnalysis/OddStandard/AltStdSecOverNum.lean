module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

theorem card_centralizer_perm_involution {n : ℕ} (π : Equiv.Perm (Fin n)) (h : π * π = 1) :
    ∃ k : ℕ, 2 * k ≤ n ∧
      Nat.card (Subgroup.centralizer ({π} : Set (Equiv.Perm (Fin n)))) =
        (n - 2 * k).factorial * (2 ^ k * k.factorial) := by
  have hord : orderOf π ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have hmem : ∀ m ∈ π.cycleType, m = 2 := fun m hm =>
    le_antisymm (Nat.le_of_dvd two_pos ((Equiv.Perm.dvd_of_mem_cycleType hm).trans hord))
      (Equiv.Perm.two_le_of_mem_cycleType hm)
  obtain ⟨k, hk⟩ : ∃ k, π.cycleType = Multiset.replicate k 2 :=
    ⟨_, Multiset.eq_replicate_card.2 hmem⟩
  have hsum : π.cycleType.sum = 2 * k := by
    rw [hk, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hprod : π.cycleType.prod = 2 ^ k := by
    rw [hk, Multiset.prod_replicate]
  have hfin : ∏ m ∈ π.cycleType.toFinset, (π.cycleType.count m).factorial = k.factorial := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [hk]
    · have h2 : π.cycleType.toFinset = {2} := by
        ext x
        simp only [Multiset.mem_toFinset, hk, Multiset.mem_replicate, Finset.mem_singleton]
        exact ⟨fun hx => hx.2, fun hx => ⟨hpos.ne', hx⟩⟩
      rw [h2, Finset.prod_singleton, hk, Multiset.count_replicate_self]
  refine ⟨k, ?_, ?_⟩
  · have := Equiv.Perm.sum_cycleType_le π
    rw [hsum, Fintype.card_fin] at this
    exact this
  · rw [Equiv.Perm.nat_card_centralizer, hsum, hprod, hfin, Fintype.card_fin, mul_assoc]

theorem padicValNat_centralizer_add_choose {n k : ℕ} (hk : 2 * k ≤ n) :
    padicValNat 2 ((n - 2 * k).factorial * (2 ^ k * k.factorial)) + padicValNat 2 (n.choose (2 * k))
      = padicValNat 2 n.factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have hne1 : n.choose (2 * k) ≠ 0 := (Nat.choose_pos hk).ne'
  have hne2 : (2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hne3 : (n - 2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hne4 : 2 ^ k * k.factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero _)
  have h2 : padicValNat 2 n.factorial = padicValNat 2 (n.choose (2 * k)) +
      padicValNat 2 (2 * k).factorial + padicValNat 2 (n - 2 * k).factorial := by
    rw [← h1, padicValNat.mul (mul_ne_zero hne1 hne2) hne3, padicValNat.mul hne1 hne2]
  have h3 : padicValNat 2 (2 * k).factorial = padicValNat 2 k.factorial + k :=
    padicValNat_factorial_mul k
  have h4 : padicValNat 2 (2 ^ k * k.factorial) = k + padicValNat 2 k.factorial := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) (Nat.factorial_ne_zero _),
      padicValNat.pow 2 k, padicValNat_self, mul_one]
  rw [padicValNat.mul hne3 hne4, h4, h2, h3]
  omega

theorem padicValNat_choose_le_log (n j : ℕ) : padicValNat 2 (n.choose j) ≤ Nat.log 2 n := by
  have h := @Nat.factorization_choose_le_log 2 n j
  rwa [Nat.factorization_def _ Nat.prime_two] at h

private theorem padicValNat_two_pow_factorial (L : ℕ) :
    padicValNat 2 (2 ^ L).factorial = 2 ^ L - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    have h := padicValNat_factorial_mul (p := 2) (2 ^ L)
    have h1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    rw [pow_succ', h, ih]
    omega

private theorem padicValNat_factorial_mono {a b : ℕ} (hab : a ≤ b) :
    padicValNat 2 a.factorial ≤ padicValNat 2 b.factorial :=
  (padicValNat_dvd_iff_le (Nat.factorial_ne_zero b)).1
    (pow_padicValNat_dvd.trans (Nat.factorial_dvd_factorial hab))

private theorem two_mul_add_four_le_two_pow {L : ℕ} (hL : 4 ≤ L) : 2 * L + 4 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih => rw [pow_succ]; omega

private theorem padicValNat_two_factorial_twelve : padicValNat 2 (12 : ℕ).factorial = 10 := by
  rw [padicValNat_factorial (b := 4) (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

theorem two_mul_log_add_three_le_padicValNat_factorial {n : ℕ} (hn : 12 ≤ n) :
    2 * Nat.log 2 n + 3 ≤ padicValNat 2 n.factorial := by
  have hL3 : 3 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega : 2 ^ 3 ≤ n)
  have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  rcases Nat.lt_or_ge (Nat.log 2 n) 4 with hlt | hge
  · have hL : Nat.log 2 n = 3 := by omega
    rw [hL]
    have h12 := padicValNat_factorial_mono hn
    rw [padicValNat_two_factorial_twelve] at h12
    omega
  · have h1 := padicValNat_factorial_mono hpow
    rw [padicValNat_two_pow_factorial] at h1
    have h2 := two_mul_add_four_le_two_pow hge
    omega

private theorem padicValNat_two_eq_of_eq {a k m : ℕ} (h : a = 2 ^ k * m) (hm : ¬ 2 ∣ m) :
    padicValNat 2 a = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
  rw [h, padicValNat.mul (by positivity) hm0, padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, add_zero]

private theorem seven_le_padicValNat_eleven {k : ℕ} (hk : 2 * k ≤ 11) :
    7 ≤ padicValNat 2 ((11 - 2 * k).factorial * (2 ^ k * k.factorial)) := by
  have hk5 : k ≤ 5 := by omega
  interval_cases k
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 0).factorial * (2 ^ 0 * Nat.factorial 0))
      (k := 8) (m := 155925) (by decide) (by decide)
    omega
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 1).factorial * (2 ^ 1 * Nat.factorial 1))
      (k := 8) (m := 2835) (by decide) (by decide)
    omega
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 2).factorial * (2 ^ 2 * Nat.factorial 2))
      (k := 7) (m := 315) (by decide) (by decide)
    omega
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 3).factorial * (2 ^ 3 * Nat.factorial 3))
      (k := 7) (m := 45) (by decide) (by decide)
    omega
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 4).factorial * (2 ^ 4 * Nat.factorial 4))
      (k := 8) (m := 9) (by decide) (by decide)
    omega
  · have := padicValNat_two_eq_of_eq (a := (11 - 2 * 5).factorial * (2 ^ 5 * Nat.factorial 5))
      (k := 8) (m := 15) (by decide) (by decide)
    omega

theorem padicValNat_card_centralizer_add {n : ℕ} (hn : 11 ≤ n) (π₁ π₂ : Equiv.Perm (Fin n))
    (h₁ : π₁ * π₁ = 1) (h₂ : π₂ * π₂ = 1) :
    padicValNat 2 n.factorial + 3 ≤
      padicValNat 2 (Nat.card (Subgroup.centralizer ({π₁} : Set (Equiv.Perm (Fin n))))) +
        padicValNat 2 (Nat.card (Subgroup.centralizer ({π₂} : Set (Equiv.Perm (Fin n))))) := by
  obtain ⟨k₁, hk₁, hc₁⟩ := card_centralizer_perm_involution π₁ h₁
  obtain ⟨k₂, hk₂, hc₂⟩ := card_centralizer_perm_involution π₂ h₂
  rw [hc₁, hc₂]
  rcases (by omega : n = 11 ∨ 12 ≤ n) with rfl | hn
  · have h11 : padicValNat 2 (11 : ℕ).factorial = 8 :=
      padicValNat_two_eq_of_eq (k := 8) (m := 155925) (by decide) (by decide)
    have l₁ := seven_le_padicValNat_eleven hk₁
    have l₂ := seven_le_padicValNat_eleven hk₂
    omega
  have e₁ := padicValNat_centralizer_add_choose hk₁
  have e₂ := padicValNat_centralizer_add_choose hk₂
  have l₁ := padicValNat_choose_le_log n (2 * k₁)
  have l₂ := padicValNat_choose_le_log n (2 * k₂)
  have l₄ := two_mul_log_add_three_le_padicValNat_factorial hn
  omega

theorem card_dvd_two_mul_inf_alternatingGroup {α : Type*} [DecidableEq α] [Fintype α]
    (C : Subgroup (Equiv.Perm α)) :
    Nat.card C ∣ 2 * Nat.card (C ⊓ alternatingGroup α : Subgroup (Equiv.Perm α)) := by
  have h1 := Subgroup.relIndex_mul_card (alternatingGroup α) C
  rw [inf_comm] at h1
  have hd : (alternatingGroup α).relIndex C ∣ 2 := by
    refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
    rcases subsingleton_or_nontrivial α with h | h
    · rw [alternatingGroup.index_eq_one]
      exact one_dvd _
    · rw [alternatingGroup.index_eq_two]
  rw [← h1]
  exact Nat.mul_dvd_mul_right hd _

end CFSG.OddStandard.AltStdSec
