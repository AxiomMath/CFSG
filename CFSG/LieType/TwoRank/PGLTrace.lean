module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

public section

namespace CFSG.LieType.TwoRank

open Matrix Module

theorem card_le_sq_of_forall_trace_eq_zero {F : Type*} [Field F] {n : Type*} [Fintype n]
    [DecidableEq n] (hn : (Fintype.card n : F) ≠ 0) (E : Subgroup (ProjGenLinGroup n F))
    (htr : ∀ g : GL n F, ProjGenLinGroup.mk g ∈ E → ProjGenLinGroup.mk g ≠ 1 →
      trace (g : Matrix n n F) = 0) :
    Nat.card E ≤ Fintype.card n ^ 2 := by
  classical
  let s : ProjGenLinGroup n F → GL n F := Function.surjInv ProjGenLinGroup.mk_surjective
  have hs : ∀ e : ProjGenLinGroup n F, ProjGenLinGroup.mk (s e) = e :=
    fun e => Function.surjInv_eq ProjGenLinGroup.mk_surjective e
  let v : E → Matrix n n F := fun e => (s (e : ProjGenLinGroup n F) : Matrix n n F)
  have hv_apply : ∀ e : E, v e = (s (e : ProjGenLinGroup n F) : Matrix n n F) :=
    fun _ => rfl
  have hv : LinearIndependent F v := by
    rw [linearIndependent_iff']
    intro t c hrel f hf
    let A : Matrix n n F := ((s (f : ProjGenLinGroup n F))⁻¹ : GL n F)
    have hA : A = ((s (f : ProjGenLinGroup n F))⁻¹ : GL n F) := rfl
    have hcoee : ∀ e : E,
        v e * A = ((s (e : ProjGenLinGroup n F) * (s (f : ProjGenLinGroup n F))⁻¹ :
          GL n F) : Matrix n n F) := by
      intro e
      rw [hv_apply e, hA, GeneralLinearGroup.coe_mul]
    have hzero : ∀ e ∈ t, e ≠ f → c e * trace (v e * A) = 0 := by
      intro e _ hef
      have hmk : ProjGenLinGroup.mk (s (e : ProjGenLinGroup n F) *
          (s (f : ProjGenLinGroup n F))⁻¹) =
          (e : ProjGenLinGroup n F) * (f : ProjGenLinGroup n F)⁻¹ := by
        simp only [map_mul, map_inv, hs]
      have hmem : ProjGenLinGroup.mk (s (e : ProjGenLinGroup n F) *
          (s (f : ProjGenLinGroup n F))⁻¹) ∈ E := by
        rw [hmk]
        exact E.mul_mem e.2 (E.inv_mem f.2)
      have hne : ProjGenLinGroup.mk (s (e : ProjGenLinGroup n F) *
          (s (f : ProjGenLinGroup n F))⁻¹) ≠ 1 := by
        rw [hmk]
        intro h
        exact hef (Subtype.ext (mul_inv_eq_one.mp h))
      have htr_e : trace (v e * A) = 0 := by
        rw [hcoee e]
        exact htr _ hmem hne
      rw [htr_e, mul_zero]
    have hmul : (∑ e ∈ t, c e • v e) * A = 0 := by rw [hrel, zero_mul]
    have htrace : ∑ e ∈ t, c e * trace (v e * A) = 0 := by
      have h := congrArg Matrix.trace hmul
      rw [Matrix.trace_zero] at h
      rw [Finset.sum_mul] at h
      rw [Matrix.trace_sum] at h
      simpa [Matrix.smul_mul, smul_eq_mul] using h
    have hsingle : ∑ e ∈ t, c e * trace (v e * A) = c f * trace (v f * A) :=
      Finset.sum_eq_single_of_mem f hf (fun e he hef => hzero e he hef)
    have hvA : trace (v f * A) = (Fintype.card n : F) := by
      have hone : v f * A = 1 := by
        rw [hcoee f, mul_inv_cancel, GeneralLinearGroup.coe_one]
      rw [hone, Matrix.trace_one]
    have hcf : c f * (Fintype.card n : F) = 0 := by
      rw [← hvA, ← hsingle, htrace]
    exact (mul_eq_zero.mp hcf).resolve_right hn
  haveI : Module.Finite F (Matrix n n F) := Matrix.finiteDimensional
  haveI : Finite E := hv.finite
  haveI : Fintype E := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card E ≤ finrank F (Matrix n n F) := hv.fintype_card_le_finrank
    _ = Fintype.card n * Fintype.card n * finrank F F :=
      Module.finrank_matrix (R := F) (M := F) (m := n) (n := n)
    _ = Fintype.card n ^ 2 := by rw [Module.finrank_self, mul_one, sq]

end CFSG.LieType.TwoRank
