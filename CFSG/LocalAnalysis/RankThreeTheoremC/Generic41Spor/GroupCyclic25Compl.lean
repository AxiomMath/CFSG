module

public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

theorem cyc25_conj_pow {R : Type} [Group R] {g u : R} {ν : ℤ} (h : u * g * u⁻¹ = g ^ ν)
    (i : ℕ) (n : ℤ) : u ^ i * g ^ n * (u ^ i)⁻¹ = g ^ (n * ν ^ i) := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    have e1 : u ^ (i + 1) * g ^ n * (u ^ (i + 1))⁻¹ =
        u ^ i * (u * g ^ n * u⁻¹) * (u ^ i)⁻¹ := by
      rw [pow_succ]; group
    rw [e1, ← conj_zpow, h, ← zpow_mul, ih]
    congr 1; ring

theorem cyc25_pow_mul {R : Type} [Group R] {x v : R} {m : ℤ} (h : v * x * v⁻¹ = x ^ m)
    (n : ℕ) : (x * v) ^ n = x ^ (∑ k ∈ Finset.range n, m ^ k) * v ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : v ^ n * x = x ^ (m ^ n) * v ^ n := by
      have := cyc25_conj_pow h n 1
      simp only [zpow_one, one_mul] at this
      calc v ^ n * x = (v ^ n * x * (v ^ n)⁻¹) * v ^ n := by group
        _ = x ^ (m ^ n) * v ^ n := by rw [this]
    calc (x * v) ^ (n + 1) = (x * v) ^ n * (x * v) := pow_succ _ _
      _ = x ^ (∑ k ∈ Finset.range n, m ^ k) * (v ^ n * x) * v := by rw [ih]; group
      _ = x ^ (∑ k ∈ Finset.range n, m ^ k) * (x ^ (m ^ n) * v ^ n) * v := by rw [hc]
      _ = x ^ (∑ k ∈ Finset.range (n + 1), m ^ k) * v ^ (n + 1) := by
          rw [Finset.sum_range_succ, zpow_add, pow_succ]; group

theorem cyc25_nu_cases :
    ∀ N : ZMod 25, N ^ 5 = 1 → N ≠ 1 → N = 6 ∨ N = 11 ∨ N = 16 ∨ N = 21 := by
  decide

theorem cyc25_exists_C (N : ZMod 25) (hN : N ^ 5 = 1) (hN1 : N ≠ 1) (i : ℕ) (hi0 : 0 < i)
    (hi5 : i < 5) (A : ZMod 25) (h : A * ∑ k ∈ Finset.range 5, (N ^ i) ^ k = 0) :
    ∃ C : ZMod 25, A + C * (1 - N ^ i) = 0 := by
  rcases cyc25_nu_cases N hN hN1 with rfl | rfl | rfl | rfl <;> interval_cases i <;>
    revert A <;> decide

theorem complement_conj_of_cyclic25 {R : Type} [Group R] (S : Subgroup R) (hS : Nat.card S = 25)
    (hcyc : IsCyclic S) (hSn : S.Normal) {u : R} (hu5 : u ^ 5 = 1)
    (hnt : ∃ s ∈ S, u * s * u⁻¹ ≠ s)
    (hR : ∀ r : R, ∃ s ∈ S, ∃ i : ℕ, r = s * u ^ i)
    {w : R} (hw5 : w ^ 5 = 1) (hwS : w ∉ S) :
    ∃ s ∈ S, ∃ j : ℕ, 0 < j ∧ j < 5 ∧ s * w * s⁻¹ = u ^ j := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg₀S : (g : R) ∈ S := g.2
  have hord : orderOf (g : R) = 25 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hS]
  have hmem : ∀ s ∈ S, ∃ n : ℤ, (g : R) ^ n = s := by
    intro s hs
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨s, hs⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hzp : ∀ n m : ℤ, (g : R) ^ n = (g : R) ^ m ↔ (n : ZMod 25) = m := by
    intro n m
    rw [zpow_eq_zpow_iff_modEq, hord, ZMod.intCast_eq_intCast_iff]
  obtain ⟨ν, hν⟩ : ∃ ν : ℤ, (g : R) ^ ν = u * (g : R) * u⁻¹ :=
    hmem _ (hSn.conj_mem _ hg₀S u)
  have hconj := cyc25_conj_pow hν.symm
  have hν5 : (ν : ZMod 25) ^ 5 = 1 := by
    have h1 := hconj 5 1
    rw [hu5] at h1
    have h2 : (g : R) ^ (1 : ℤ) = (g : R) ^ (ν ^ 5) := by simpa using h1
    have := (hzp 1 (ν ^ 5)).mp h2
    simpa using this.symm
  have hν1 : (ν : ZMod 25) ≠ 1 := by
    intro h
    obtain ⟨s, hs, hne⟩ := hnt
    obtain ⟨n, rfl⟩ := hmem s hs
    apply hne
    have h3 := hconj 1 n
    simp only [pow_one] at h3
    rw [h3, hzp]
    push_cast
    rw [h, mul_one]
  obtain ⟨s, hs, i, hwi⟩ := hR w
  obtain ⟨a, rfl⟩ := hmem s hs
  have hui : u ^ i = u ^ (i % 5) := pow_eq_pow_mod i hu5
  have hj5 : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hj0 : 0 < i % 5 := by
    rcases Nat.eq_zero_or_pos (i % 5) with h0 | h0
    · exfalso
      apply hwS
      rw [hwi, hui, h0, pow_zero, mul_one]
      exact zpow_mem hg₀S a
    · exact h0
  generalize i % 5 = j at hui hj5 hj0
  have hwj : w = (g : R) ^ a * u ^ j := by rw [hwi, hui]
  clear hwi hui
  subst hwj
  have hmj : u ^ j * (g : R) ^ a * (u ^ j)⁻¹ = ((g : R) ^ a) ^ (ν ^ j) := by
    rw [hconj, ← zpow_mul]
  have h5 := cyc25_pow_mul hmj 5
  have hv5 : (u ^ j) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu5, one_pow]
  rw [h5, hv5, mul_one, ← zpow_mul] at hw5
  have h6 := (hzp _ 0).mp (by simpa using hw5)
  push_cast at h6
  obtain ⟨C, hC⟩ := cyc25_exists_C (ν : ZMod 25) hν5 hν1 j hj0 hj5 (a : ZMod 25) h6
  obtain ⟨c, hcC⟩ : ∃ c : ℤ, (c : ZMod 25) = C :=
    ⟨((C.val : ℕ) : ℤ), by rw [Int.cast_natCast, ZMod.natCast_zmod_val]⟩
  refine ⟨(g : R) ^ c, zpow_mem hg₀S c, j, hj0, hj5, ?_⟩
  have h1 : (g : R) ^ (c + a + (-c) * ν ^ j) = 1 := by
    rw [← zpow_zero (g : R), hzp]
    push_cast
    rw [hcC, ← hC]
    ring
  have h2 := hconj j (-c)
  calc (g : R) ^ c * ((g : R) ^ a * u ^ j) * ((g : R) ^ c)⁻¹
      = (g : R) ^ c * (g : R) ^ a * (u ^ j * (g : R) ^ (-c) * (u ^ j)⁻¹) * u ^ j := by group
    _ = (g : R) ^ c * (g : R) ^ a * (g : R) ^ (-c * ν ^ j) * u ^ j := by rw [h2]
    _ = (g : R) ^ (c + a + (-c) * ν ^ j) * u ^ j := by rw [zpow_add, zpow_add]
    _ = u ^ j := by rw [h1, one_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
