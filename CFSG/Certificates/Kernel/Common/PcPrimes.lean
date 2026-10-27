module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

public section

namespace CFSG.KC.PcPrimes

variable {G : Type*} [Group G]

@[expose] def pcSub (x : ℕ → G) (n i : ℕ) : Subgroup G := Subgroup.closure (x '' Set.Ico i n)

structure PcSeq (x : ℕ → G) (p : ℕ → ℕ) (n : ℕ) : Prop where
  pos : ∀ j < n, 0 < p j
  pow_mem : ∀ j < n, x j ^ p j ∈ pcSub x n (j + 1)
  conj_mem : ∀ j k, j < k → k < n → (x j)⁻¹ * x k * x j ∈ pcSub x n (j + 1)

variable {x : ℕ → G} {p : ℕ → ℕ} {n : ℕ}

theorem x_mem {i k : ℕ} (hi : i ≤ k) (hk : k < n) : x k ∈ pcSub x n i :=
  Subgroup.subset_closure ⟨k, ⟨hi, hk⟩, rfl⟩

theorem pcSub_anti {i j : ℕ} (h : i ≤ j) : pcSub x n j ≤ pcSub x n i :=
  Subgroup.closure_mono (Set.image_mono (Set.Ico_subset_Ico_left h))

theorem pcSub_of_ge {i : ℕ} (hi : n ≤ i) : pcSub x n i = ⊥ := by
  unfold pcSub
  rw [Set.Ico_eq_empty (by omega), Set.image_empty, Subgroup.closure_empty]

section Seq

variable (hP : PcSeq x p n)
include hP

theorem conj_inv_mem {j : ℕ} {m : G} (hm : m ∈ pcSub x n (j + 1)) :
    (x j)⁻¹ * m * x j ∈ pcSub x n (j + 1) := by
  induction hm using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hy
    exact hP.conj_mem j k (by omega) hk2
  | one => rw [mul_one, inv_mul_cancel]; exact one_mem _
  | mul a b _ _ ha hb =>
    have e : (x j)⁻¹ * (a * b) * x j = ((x j)⁻¹ * a * x j) * ((x j)⁻¹ * b * x j) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : (x j)⁻¹ * a⁻¹ * x j = ((x j)⁻¹ * a * x j)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem conjPow_inv_mem {j : ℕ} {m : G} (hm : m ∈ pcSub x n (j + 1)) (e : ℕ) :
    (x j ^ e)⁻¹ * m * x j ^ e ∈ pcSub x n (j + 1) := by
  induction e with
  | zero => simpa using hm
  | succ e ih =>
    have := conj_inv_mem hP ih
    have e1 : (x j ^ (e + 1))⁻¹ * m * x j ^ (e + 1) =
        (x j)⁻¹ * ((x j ^ e)⁻¹ * m * x j ^ e) * x j := by
      rw [pow_succ]; group
    rw [e1]
    exact this

theorem decomp {j : ℕ} (hj : j < n) {g : G} (hg : g ∈ pcSub x n j) :
    ∃ e < p j, (x j ^ e)⁻¹ * g ∈ pcSub x n (j + 1) := by
  have hp := hP.pos j hj
  have hpw := hP.pow_mem j hj
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨m, ⟨hm1, hm2⟩, rfl⟩ := hy
    by_cases hmj : m = j
    · subst hmj
      by_cases hp1 : p m = 1
      · refine ⟨0, hp, ?_⟩
        rw [pow_zero, inv_one, one_mul]
        simpa [hp1] using hpw
      · exact ⟨1, by omega, by rw [pow_one, inv_mul_cancel]; exact one_mem _⟩
    · exact ⟨0, hp, by rw [pow_zero, inv_one, one_mul]; exact x_mem (by omega) hm2⟩
  | one => exact ⟨0, hp, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨e, he, ha'⟩ := ha
    obtain ⟨f, hf, hb'⟩ := hb
    have hc := conjPow_inv_mem hP ha' f
    by_cases hef : e + f < p j
    · refine ⟨e + f, hef, ?_⟩
      have eq : (x j ^ (e + f))⁻¹ * (a * b) =
          ((x j ^ f)⁻¹ * ((x j ^ e)⁻¹ * a) * x j ^ f) * ((x j ^ f)⁻¹ * b) := by
        rw [pow_add]; group
      rw [eq]
      exact mul_mem hc hb'
    · refine ⟨e + f - p j, by omega, ?_⟩
      have eq : (x j ^ (e + f - p j))⁻¹ * (a * b) =
          x j ^ p j * (((x j ^ f)⁻¹ * ((x j ^ e)⁻¹ * a) * x j ^ f) * ((x j ^ f)⁻¹ * b)) := by
        have : x j ^ (e + f) = x j ^ p j * x j ^ (e + f - p j) := by
          rw [← pow_add]; congr 1; omega
        rw [show (x j ^ (e + f - p j))⁻¹ = x j ^ p j * (x j ^ (e + f))⁻¹ by rw [this]; group,
          pow_add]
        group
      rw [eq]
      exact mul_mem hpw (mul_mem hc hb')
  | inv a _ ha =>
    obtain ⟨e, he, ha'⟩ := ha
    by_cases e0 : e = 0
    · subst e0
      rw [pow_zero, inv_one, one_mul] at ha'
      exact ⟨0, hp, by rw [pow_zero, inv_one, one_mul]; exact inv_mem ha'⟩
    · refine ⟨p j - e, by omega, ?_⟩
      have hc := conjPow_inv_mem hP (inv_mem ha') (p j - e)
      have eq : (x j ^ (p j - e))⁻¹ * a⁻¹ =
          ((x j ^ (p j - e))⁻¹ * ((x j ^ e)⁻¹ * a)⁻¹ * x j ^ (p j - e)) * (x j ^ p j)⁻¹ := by
        have : x j ^ p j = x j ^ e * x j ^ (p j - e) := by rw [← pow_add]; congr 1; omega
        rw [this]
        group
      rw [eq]
      exact mul_mem hc (inv_mem hpw)

variable [Finite G]

theorem card_step {j : ℕ} (hj : j < n) :
    Nat.card (pcSub x n j) ≤ p j * Nat.card (pcSub x n (j + 1)) := by
  let f : Fin (p j) × pcSub x n (j + 1) → pcSub x n j := fun q =>
    ⟨x j ^ (q.1 : ℕ) * q.2, mul_mem (pow_mem (x_mem le_rfl hj) _) (pcSub_anti (Nat.le_succ j) q.2.2)⟩
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨e, he, hg⟩ := decomp hP hj g.2
    refine ⟨(⟨e, he⟩, ⟨_, hg⟩), Subtype.ext ?_⟩
    change x j ^ e * ((x j ^ e)⁻¹ * g) = g
    group
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin (p j)), Fintype.card_fin] at this

theorem card_le_from : ∀ i ≤ n, Nat.card (pcSub x n i) ≤ ∏ j ∈ Finset.Ico i n, p j := by
  intro i hi
  induction h : n - i generalizing i with
  | zero =>
    rw [show i = n by omega, pcSub_of_ge le_rfl, Subgroup.card_bot, Finset.Ico_self,
      Finset.prod_empty]
  | succ m ih =>
    rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
    exact le_trans (card_step hP (by omega))
      (Nat.mul_le_mul_left _ (ih (i + 1) (by omega) (by omega)))

theorem card_le : Nat.card (pcSub x n 0) ≤ ∏ j ∈ Finset.range n, p j := by
  rw [Finset.range_eq_Ico]
  exact card_le_from hP 0 (Nat.zero_le n)

end Seq

end CFSG.KC.PcPrimes

end
