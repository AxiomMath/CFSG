module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Tables
public import Certificates.Data.RouteP.Q0Planes
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

theorem anyIn_eq_true {lo hi : ℕ} {p : ℕ → Bool} :
    anyIn lo hi p = true ↔ ∃ i, lo ≤ i ∧ i < hi ∧ p i = true := by
  unfold anyIn
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allIn_eq_true]
  constructor
  · intro h
    by_contra hc
    exact h fun i hlo hhi => by
      rw [Bool.not_eq_true']
      exact Bool.eq_false_iff.2 fun h' => hc ⟨i, hlo, hhi, h'⟩
  · rintro ⟨i, hlo, hhi, h⟩ H
    have := H i hlo hhi
    rw [h] at this
    exact Bool.false_ne_true this

theorem memRow_eq_true {r : Array ℕ} {p : ℕ} : memRow r p = true ↔ ∃ j < 24, r[j]! = p := by
  unfold memRow
  rw [anyIn_eq_true]
  constructor
  · rintro ⟨j, _, hj, h⟩
    exact ⟨j, hj, eq_of_beq h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, Nat.zero_le j, hj, beq_of_eq h⟩

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n s : ℕ} (hs : s < n) :
    ((Array.range n).map f)[s]! = f s := by
  rw [getElem!_pos _ _ (by simpa using hs)]
  simp

theorem planeWordG_append {G : Type*} [Group G] (gensG : ℤ → G) (u v : List ℤ) :
    wordG gensG (u ++ v) = wordG gensG u * wordG gensG v := by
  simp only [wordG, List.map_append, List.prod_append]

theorem letterPerm_neg {G : Type*} [Group G] (π : ℕ → G) (m : ℕ) (l : ℤ) :
    letterPerm π m (-l) = (letterPerm π m l)⁻¹ := by
  rcases lt_trichotomy l 0 with hl | hl | hl
  ·
    by_cases hj : (-l - 1).toNat < m
    · have h1 : 0 < -l ∧ (-l - 1).toNat < m := by omega
      have hA : letterPerm π m (-l) = π ((-l - 1).toNat) := by
        simp only [letterPerm, neg_neg, if_pos h1]
      have h3 : ¬ (0 < l ∧ (l - 1).toNat < m) := by omega
      have h4 : l < 0 ∧ (-l - 1).toNat < m := by omega
      have hB : letterPerm π m l = (π ((-l - 1).toNat))⁻¹ := by
        simp only [letterPerm, if_neg h3, if_pos h4]
      rw [hA, hB, inv_inv]
    · have h1 : ¬ (0 < -l ∧ (-l - 1).toNat < m) := by omega
      have h2 : ¬ (-l < 0 ∧ (l - 1).toNat < m) := by omega
      have hA : letterPerm π m (-l) = 1 := by
        simp only [letterPerm, neg_neg, if_neg h1, if_neg h2]
      have h3 : ¬ (0 < l ∧ (l - 1).toNat < m) := by omega
      have h4 : ¬ (l < 0 ∧ (-l - 1).toNat < m) := by omega
      have hB : letterPerm π m l = 1 := by
        simp only [letterPerm, if_neg h3, if_neg h4]
      rw [hA, hB, inv_one]
  ·
    subst hl
    simp [letterPerm, inv_one]
  ·
    by_cases hk : (l - 1).toNat < m
    · have h1 : ¬ (0 < -l ∧ (-l - 1).toNat < m) := by omega
      have h2 : -l < 0 ∧ (l - 1).toNat < m := by omega
      have hA : letterPerm π m (-l) = (π ((l - 1).toNat))⁻¹ := by
        simp only [letterPerm, neg_neg, if_neg h1, if_pos h2]
      have h2' : 0 < l ∧ (l - 1).toNat < m := by omega
      have hB : letterPerm π m l = π ((l - 1).toNat) := by
        simp only [letterPerm, if_pos h2']
      rw [hA, hB]
    · have h1 : ¬ (0 < -l ∧ (-l - 1).toNat < m) := by omega
      have h2 : ¬ (-l < 0 ∧ (l - 1).toNat < m) := by omega
      have hA : letterPerm π m (-l) = 1 := by
        simp only [letterPerm, neg_neg, if_neg h1, if_neg h2]
      have h3 : ¬ (0 < l ∧ (l - 1).toNat < m) := by omega
      have h4 : ¬ (l < 0 ∧ (-l - 1).toNat < m) := by omega
      have hB : letterPerm π m l = 1 := by
        simp only [letterPerm, if_neg h3, if_neg h4]
      rw [hA, hB, inv_one]

theorem wordG_planeInvWord {G : Type*} [Group G] (gensG : ℤ → G)
    (hneg : ∀ l, gensG (-l) = (gensG l)⁻¹) (w : List ℤ) :
    wordG gensG (planeInvWord w) = (wordG gensG w)⁻¹ := by
  induction w with
  | nil => simp [planeInvWord, wordG]
  | cons a w ih =>
    have e : planeInvWord (a :: w) = planeInvWord w ++ [-a] := by
      simp [planeInvWord, List.reverse_cons, List.map_append]
    have hsingle : wordG gensG [-a] = gensG (-a) := by simp [wordG]
    have hcons : wordG gensG (a :: w) = gensG a * wordG gensG w := by simp [wordG]
    rw [e, planeWordG_append, ih, hsingle, hcons, mul_inv_rev, hneg]

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
