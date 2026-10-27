module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem mem_closure_pair {a b : G} (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a) {g : G}
    (hg : g ∈ Subgroup.closure ({a, b} : Set G)) : ∃ i j : ℕ, g = a ^ i * b ^ j := by
  have hc : ∀ i j : ℕ, Commute (a ^ i) (b ^ j) :=
    fun i j => (Commute.pow_pow (show Commute a b from hab) i j)
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | hz
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul u v _ _ hu hv =>
    obtain ⟨i, j, rfl⟩ := hu
    obtain ⟨k, l, rfl⟩ := hv
    refine ⟨i + k, j + l, ?_⟩
    rw [pow_add, pow_add]
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [(hc k j).eq]
      _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
  | inv u _ hu =>
    obtain ⟨i, j, rfl⟩ := hu
    refine ⟨3 * i, 3 * j, ?_⟩
    have h3a : a⁻¹ = a ^ 3 := by
      have : a ^ 3 * a = 1 := by rw [← pow_succ]; exact ha
      exact inv_eq_of_mul_eq_one_left this
    have h3b : b⁻¹ = b ^ 3 := by
      have : b ^ 3 * b = 1 := by rw [← pow_succ]; exact hb
      exact inv_eq_of_mul_eq_one_left this
    rw [mul_inv_rev, ← inv_pow, ← inv_pow, h3a, h3b, ← pow_mul, ← pow_mul]
    exact (hc (3 * i) (3 * j)).symm.eq

theorem z4_inj {a b : G} [Finite G] (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a)
    (hcard : Nat.card (Subgroup.closure ({a, b} : Set G)) = 16) :
    ∀ i j k l : ℕ, a ^ i * b ^ j = a ^ k * b ^ l → i % 4 = k % 4 ∧ j % 4 = l % 4 := by
  have hmem : ∀ i j : ℕ, a ^ i * b ^ j ∈ Subgroup.closure ({a, b} : Set G) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) i)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) j)
  let φ : Fin 4 × Fin 4 → Subgroup.closure ({a, b} : Set G) := fun p =>
    ⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), hmem _ _⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨g, hg⟩
    obtain ⟨i, j, rfl⟩ := mem_closure_pair ha hb hab hg
    refine ⟨(⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    show a ^ (i % 4) * b ^ (j % 4) = a ^ i * b ^ j
    rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb]
  have hbij := hsurj.bijective_of_nat_card_le (by rw [hcard]; simp)
  intro i j k l h
  have h1 : φ (⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩) =
      φ (⟨k % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨l % 4, Nat.mod_lt _ (by norm_num)⟩) := by
    apply Subtype.ext
    show a ^ (i % 4) * b ^ (j % 4) = a ^ (k % 4) * b ^ (l % 4)
    rw [← pow_eq_pow_mod i ha, ← pow_eq_pow_mod j hb, ← pow_eq_pow_mod k ha,
      ← pow_eq_pow_mod l hb]
    exact h
  have h2 := hbij.1 h1
  have h3 := congrArg (fun p : Fin 4 × Fin 4 => ((p.1 : ℕ), (p.2 : ℕ))) h2
  simp only [Prod.mk.injEq] at h3
  exact h3

theorem z4_sq_one {a b : G} [Finite G] (ha : a ^ 4 = 1) (hb : b ^ 4 = 1) (hab : a * b = b * a)
    (hcard : Nat.card (Subgroup.closure ({a, b} : Set G)) = 16) {h : G}
    (hh : h ∈ Subgroup.closure ({a, b} : Set G)) (h2 : h * h = 1) :
    h = 1 ∨ h = a ^ 2 ∨ h = b ^ 2 ∨ h = a ^ 2 * b ^ 2 := by
  obtain ⟨i, j, rfl⟩ := mem_closure_pair ha hb hab hh
  have hc : Commute (b ^ j) (a ^ i) := (Commute.pow_pow (show Commute b a from hab.symm) j i)
  have e : a ^ i * b ^ j * (a ^ i * b ^ j) = a ^ (2 * i) * b ^ (2 * j) := by
    calc a ^ i * b ^ j * (a ^ i * b ^ j) = a ^ i * (b ^ j * a ^ i) * b ^ j := by group
      _ = a ^ i * (a ^ i * b ^ j) * b ^ j := by rw [hc.eq]
      _ = a ^ (2 * i) * b ^ (2 * j) := by rw [two_mul, two_mul, pow_add, pow_add]; group
  rw [e] at h2
  have h3 : a ^ (2 * i) * b ^ (2 * j) = a ^ 0 * b ^ 0 := by simpa using h2
  obtain ⟨h4, h5⟩ := z4_inj ha hb hab hcard _ _ _ _ h3
  have hi : i % 2 = 0 := by omega
  have hj : j % 2 = 0 := by omega
  have ha2 : (a ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact ha
  have hb2 : (b ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hb
  obtain ⟨i', rfl⟩ : ∃ i', i = 2 * i' := ⟨i / 2, by omega⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = 2 * j' := ⟨j / 2, by omega⟩
  rw [pow_mul, pow_mul, pow_eq_pow_mod i' ha2, pow_eq_pow_mod j' hb2]
  rcases Nat.mod_two_eq_zero_or_one i' with h6 | h6 <;> rcases Nat.mod_two_eq_zero_or_one j' with h7 | h7 <;>
    simp [h6, h7]

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
