module

public import CFSG.FeitThompson.Representations.GramArrayLineNoOppositeSigns
public import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import CFSG.FeitThompson.Representations.GramArrayDistinctRowColumnPivots
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Matrix

variable {ι : Type*} [Fintype ι]

section SignedCoord

variable [DecidableEq ι]

theorem isSignedCoordVec_of_dotProduct_self_eq_one {u : ι → ℤ} (hu : u ⬝ᵥ u = 1) :
    IsSignedCoordVec u := by
  obtain ⟨a, ha⟩ : ∃ a, u a ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    simp [dotProduct, h] at hu
  have h1 : u a ^ 2 = 1 := by
    have hle := sq_le_dotProduct_self u a
    rw [hu] at hle
    have h0 : u a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have h0' : 0 ≤ u a ^ 2 := sq_nonneg _
    omega
  have hsingle : u = Pi.single a (u a) :=
    eq_single_of_dotProduct_self_eq_sq (by rw [hu, h1])
  rw [hsingle]
  exact isSignedCoordVec_single (sq_eq_one_iff.mp h1)

theorem IsSignedCoordVec.dotProduct_eq_zero_of_support_ne {v w : ι → ℤ}
    (hv : IsSignedCoordVec v) (hw : IsSignedCoordVec w)
    (h : Function.support v ≠ Function.support w) : v ⬝ᵥ w = 0 := by
  obtain ⟨q, hq, -⟩ := hv.exists_support_eq
  obtain ⟨q', hq', -⟩ := hw.exists_support_eq
  have hne : q ≠ q' := by rintro rfl; exact h (hq.trans hq'.symm)
  rw [eq_single_of_support_eq hq, single_dotProduct,
    apply_eq_zero_of_support_eq_singleton hq' hne, mul_zero]

theorem IsSignedCoordVec.dotProduct_eq_ite_of_support_pairwise_ne {κ : Type*} [DecidableEq κ]
    {v : κ → ι → ℤ} (hv : ∀ i, IsSignedCoordVec (v i))
    (hne : ∀ i k, i ≠ k → Function.support (v i) ≠ Function.support (v k)) (i k : κ) :
    v i ⬝ᵥ v k = if i = k then 1 else 0 := by
  by_cases h : i = k
  · subst h; rw [if_pos rfl]; exact (hv i).dotProduct_self
  · rw [if_neg h]
    exact (hv i).dotProduct_eq_zero_of_support_ne (hv k) (hne i k h)

end SignedCoord

section Residue

variable {μ ν : Type*} {b : μ → ν → ι → ℤ} {r : μ → ι → ℤ} {c : ν → ι → ℤ}

theorem sub_pivots_dotProduct_row [DecidableEq μ]
    (hrr : ∀ i k, r i ⬝ᵥ r k = if i = k then 1 else 0)
    (hcr : ∀ j k, c j ⬝ᵥ r k = 0) (hbr : ∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0)
    (i : μ) (j : ν) (k : μ) : (b i j - r i - c j) ⬝ᵥ r k = 0 := by
  rw [sub_dotProduct, sub_dotProduct, hbr, hrr, hcr, sub_zero, sub_self]

theorem sub_pivots_dotProduct_col [DecidableEq ν]
    (hcc : ∀ j l, c j ⬝ᵥ c l = if j = l then 1 else 0)
    (hrc : ∀ i l, r i ⬝ᵥ c l = 0) (hbc : ∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0)
    (i : μ) (j : ν) (l : ν) : (b i j - r i - c j) ⬝ᵥ c l = 0 := by
  rw [sub_dotProduct, sub_dotProduct, hbc, hrc, hcc, sub_zero, sub_self]

theorem sub_pivots_dotProduct [DecidableEq μ] [DecidableEq ν] (hb : IsGramArray b)
    (hrr : ∀ i k, r i ⬝ᵥ r k = if i = k then 1 else 0)
    (hcc : ∀ j l, c j ⬝ᵥ c l = if j = l then 1 else 0)
    (hrc : ∀ i l, r i ⬝ᵥ c l = 0) (hcr : ∀ j k, c j ⬝ᵥ r k = 0)
    (hbr : ∀ i j k, b i j ⬝ᵥ r k = if i = k then 1 else 0)
    (hbc : ∀ i j l, b i j ⬝ᵥ c l = if j = l then 1 else 0)
    (i : μ) (j : ν) (k : μ) (l : ν) :
    (b i j - r i - c j) ⬝ᵥ (b k l - r k - c l) = if i = k ∧ j = l then 1 else 0 := by
  have h1 : (b i j - r i - c j) ⬝ᵥ (b k l - r k - c l) = (b i j - r i - c j) ⬝ᵥ b k l := by
    rw [dotProduct_sub, dotProduct_sub, sub_pivots_dotProduct_row hrr hcr hbr,
      sub_pivots_dotProduct_col hcc hrc hbc, sub_zero, sub_zero]
  have hrb : r i ⬝ᵥ b k l = if i = k then 1 else 0 := by
    rw [dotProduct_comm, hbr]; simp [eq_comm]
  have hcb : c j ⬝ᵥ b k l = if j = l then 1 else 0 := by
    rw [dotProduct_comm, hbc]; simp [eq_comm]
  rw [h1, sub_dotProduct, sub_dotProduct, hb.dotProduct_eq, hrb, hcb]
  by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]

end Residue

theorem exists_orthonormal_signed_decomposition_of_isGramArray {d m n : ℕ}
    (hm : 2 ≤ m) (hn : 2 ≤ n) (hme : Even m) (hne : Even n) (hmn : m ≠ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) :
    ∃ (r : Fin m → Fin d → ℤ) (c : Fin n → Fin d → ℤ) (t : Fin m → Fin n → Fin d → ℤ),
      (∀ i, IsSignedCoordVec (r i)) ∧ (∀ j, IsSignedCoordVec (c j)) ∧
      (∀ i j, IsSignedCoordVec (t i j)) ∧
      (∀ i k, r i ⬝ᵥ r k = if i = k then 1 else 0) ∧
      (∀ j l, c j ⬝ᵥ c l = if j = l then 1 else 0) ∧
      (∀ i j k l, t i j ⬝ᵥ t k l = if i = k ∧ j = l then 1 else 0) ∧
      (∀ i j, r i ⬝ᵥ c j = 0) ∧
      (∀ i k l, r i ⬝ᵥ t k l = 0) ∧
      (∀ j k l, c j ⬝ᵥ t k l = 0) ∧
      (∀ i j, b i j = r i + c j + t i j) := by
  obtain ⟨r, c, hrs, hcs, hrne, hcne, hrcne, hbr, hbc⟩ :=
    exists_row_col_pivots_of_isGramArray hm hn hme hne hmn hb
  have hrr := IsSignedCoordVec.dotProduct_eq_ite_of_support_pairwise_ne hrs hrne
  have hcc := IsSignedCoordVec.dotProduct_eq_ite_of_support_pairwise_ne hcs hcne
  have hrc : ∀ i l, r i ⬝ᵥ c l = 0 := fun i l =>
    (hrs i).dotProduct_eq_zero_of_support_ne (hcs l) (hrcne i l)
  have hcr : ∀ j k, c j ⬝ᵥ r k = 0 := fun j k => by rw [dotProduct_comm]; exact hrc k j
  refine ⟨r, c, fun i j => b i j - r i - c j, hrs, hcs, ?_, hrr, hcc,
    fun i j k l => sub_pivots_dotProduct hb hrr hcc hrc hcr hbr hbc i j k l,
    hrc, ?_, ?_, fun i j => by ring⟩
  · intro i j
    refine isSignedCoordVec_of_dotProduct_self_eq_one ?_
    rw [sub_pivots_dotProduct hb hrr hcc hrc hcr hbr hbc i j i j]
    simp
  · intro i k l
    rw [dotProduct_comm]
    exact sub_pivots_dotProduct_row hrr hcr hbr k l i
  · intro j k l
    rw [dotProduct_comm]
    exact sub_pivots_dotProduct_col hcc hrc hbc k l j

end CFSG.FeitThompson
