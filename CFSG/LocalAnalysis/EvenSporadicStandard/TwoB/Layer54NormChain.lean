module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup

variable {G : Type*} [Group G] [Finite G]

private lemma closure_image_Iio_le_centralizer (Q : ℕ → Subgroup G) (s : ℕ → G) (n : ℕ)
    (hs : ∀ j < n, s j ∈ Q j)
    (hcomm : ∀ j < n, ∀ x ∈ Q j, ∀ y ∈ Q n, x * y = y * x) :
    closure (s '' Set.Iio n) ≤ centralizer (Q n : Set G) := by
  rw [closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_centralizer_iff.2 fun y hy => (hcomm j hj _ (hs j hj) y hy).symm

private lemma two_mul_card_le_of_lt {H K : Subgroup G} (h : H < K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨c, hc⟩ := card_dvd_of_le h.le
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hc0 : c ≠ 0 := by
    rintro rfl
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact h.ne (eq_of_le_of_card_ge h.le (by omega))
  have h2 : 2 ≤ c := by omega
  calc 2 * Nat.card H ≤ c * Nat.card H := Nat.mul_le_mul_right _ h2
    _ = Nat.card K := by rw [hc, mul_comm]

theorem two_pow_le_card_closure_of_noncomm (Q : ℕ → Subgroup G) (s : ℕ → G) (n : ℕ)
    (hs : ∀ j < n, s j ∈ Q j)
    (hcomm : ∀ j < n, ∀ k < n, j ≠ k → ∀ x ∈ Q j, ∀ y ∈ Q k, x * y = y * x)
    (hnc : ∀ j < n, ∃ q ∈ Q j, s j * q ≠ q * s j) :
    2 ^ n ≤ Nat.card (closure (s '' Set.Iio n) : Subgroup G) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : n < n + 1 := n.lt_succ_self
    have ih' := ih (fun j hj => hs j (by omega))
      (fun j hj k hk hjk => hcomm j (by omega) k (by omega) hjk) (fun j hj => hnc j (by omega))
    have hle : closure (s '' Set.Iio n) ≤ closure (s '' Set.Iio (n + 1)) :=
      closure_mono (Set.image_mono (Set.Iio_subset_Iio n.le_succ))
    have hmem : s n ∈ closure (s '' Set.Iio (n + 1)) := subset_closure ⟨n, hn, rfl⟩
    have hnot : s n ∉ closure (s '' Set.Iio n) := by
      intro h
      obtain ⟨q, hq, hne⟩ := hnc n hn
      have hcent := closure_image_Iio_le_centralizer Q s n (fun j hj => hs j (by omega))
        (fun j hj x hx y hy => hcomm j (by omega) n hn (by omega) x hx y hy) h
      exact hne (mem_centralizer_iff.1 hcent q hq).symm
    have hlt : closure (s '' Set.Iio n) < closure (s '' Set.Iio (n + 1)) :=
      lt_of_le_of_ne hle fun h => hnot (h ▸ hmem)
    have := two_mul_card_le_of_lt hlt
    rw [pow_succ]
    omega

theorem closure_comm_of_noncomm (Q : ℕ → Subgroup G) (s : ℕ → G) (n : ℕ)
    (hs : ∀ j < n, s j ∈ Q j)
    (hcomm : ∀ j < n, ∀ k < n, j ≠ k → ∀ x ∈ Q j, ∀ y ∈ Q k, x * y = y * x) :
    ∀ a ∈ (closure (s '' Set.Iio n) : Subgroup G), ∀ b ∈ (closure (s '' Set.Iio n) : Subgroup G),
      a * b = b * a := by
  have hgen : ∀ x ∈ s '' Set.Iio n, ∀ y ∈ s '' Set.Iio n, x * y = y * x := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
    by_cases hjk : j = k
    · rw [hjk]
    · exact hcomm j hj k hk hjk _ (hs j hj) _ (hs k hk)
  have hcl : ∀ x ∈ s '' Set.Iio n, ∀ b ∈ (closure (s '' Set.Iio n) : Subgroup G),
      x * b = b * x := by
    intro x hx
    have : closure (s '' Set.Iio n) ≤ centralizer ({x} : Set G) := by
      rw [closure_le]
      intro y hy
      exact mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hgen x hx y hy
    intro b hb
    exact mem_centralizer_iff.1 (this hb) x rfl
  intro a ha
  have : closure (s '' Set.Iio n) ≤ centralizer (closure (s '' Set.Iio n) : Set G) := by
    rw [closure_le]
    intro x hx
    exact mem_centralizer_iff.2 fun b hb => (hcl x hx b hb).symm
  intro b hb
  exact (mem_centralizer_iff.1 (this ha) b hb).symm

end CFSG.EvenSporadicStandard.TwoB
