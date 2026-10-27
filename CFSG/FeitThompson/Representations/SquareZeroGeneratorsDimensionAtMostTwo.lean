module

public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.NoncommRing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module Pointwise

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def unitOneAddOfSqEqZero {R : Type*} [Ring R] (f : R) (hf : f ^ 2 = 0) : Rˣ where
  val := 1 + f
  inv := 1 - f
  val_inv := by rw [sq] at hf; noncomm_ring [hf]
  inv_val := by rw [sq] at hf; noncomm_ring [hf]

@[simp]
theorem unitOneAddOfSqEqZero_val {R : Type*} [Ring R] (f : R) (hf : f ^ 2 = 0) :
    (unitOneAddOfSqEqZero f hf : R) = 1 + f := (rfl)

@[simp]
theorem unitOneAddOfSqEqZero_inv_val {R : Type*} [Ring R] (f : R) (hf : f ^ 2 = 0) :
    (((unitOneAddOfSqEqZero f hf)⁻¹ : Rˣ) : R) = 1 - f := (rfl)

theorem mem_stabilizer_of_mapsTo {U : Submodule k V} {u : (End k V)ˣ}
    (h : ∀ x ∈ U, (u : End k V) x ∈ U) (h' : ∀ x ∈ U, ((u⁻¹ : (End k V)ˣ) : End k V) x ∈ U) :
    u ∈ MulAction.stabilizer (End k V)ˣ U := by
  have key : U.map (u : End k V) = U := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun x hx => h x hx) fun x hx => ?_
    refine Submodule.mem_map.mpr ⟨((u⁻¹ : (End k V)ˣ) : End k V) x, h' x hx, ?_⟩
    rw [← Module.End.mul_apply]
    simp
  exact key

theorem mem_stabilizer_of_sq_eq_zero {U : Submodule k V} {f : End k V} (hf : f ^ 2 = 0)
    {u : (End k V)ˣ} (hu : (u : End k V) = 1 + f) (h : ∀ x ∈ U, f x ∈ U) :
    u ∈ MulAction.stabilizer (End k V)ˣ U := by
  have hinv : ((u⁻¹ : (End k V)ˣ) : End k V) = 1 - f := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hu, sq] at *
    noncomm_ring [hf]
  refine mem_stabilizer_of_mapsTo (fun x hx => ?_) (fun x hx => ?_)
  · rw [hu]; exact U.add_mem hx (h x hx)
  · rw [hinv]; exact U.sub_mem hx (h x hx)

theorem eq_bot_or_eq_top_of_forall_mem_stabilizer {S : Set (End k V)ˣ} {U : Submodule k V}
    (hirr : (Representation.ofDistribMulAction k (Subgroup.closure S) V).IsIrreducible)
    (h : ∀ g ∈ S, g ∈ MulAction.stabilizer (End k V)ˣ U) :
    U = ⊥ ∨ U = ⊤ := by
  have hcl : Subgroup.closure S ≤ MulAction.stabilizer (End k V)ˣ U :=
    (Subgroup.closure_le _).mpr h
  set ρ := Representation.ofDistribMulAction k (Subgroup.closure S) V with hρ
  have hinv : ∀ (g : Subgroup.closure S) ⦃x : V⦄, x ∈ U → ρ g x ∈ U := by
    intro g x hx
    have hg : U.map ((g : (End k V)ˣ) : End k V) = U := hcl g.2
    have hgx : ρ g x = ((g : (End k V)ˣ) : End k V) x := rfl
    rw [hgx, ← hg]
    exact Submodule.mem_map_of_mem hx
  rcases hirr.eq_bot_or_eq_top (⟨U, hinv⟩ : Subrepresentation ρ) with h1 | h1
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem rank_le_two_of_sq_eq_zero_of_isIrreducible {X Y : End k V} {t : k} {u w : (End k V)ˣ}
    (hX : X ^ 2 = 0) (hY : Y ^ 2 = 0) (hXY : X * Y + Y * X = t • 1) (hX0 : X ≠ 0)
    (hu : (u : End k V) = 1 + X) (hw : (w : End k V) = 1 + Y)
    (hirr : (Representation.ofDistribMulAction k (Subgroup.closure {u, w}) V).IsIrreducible) :
    Module.rank k V ≤ 2 := by
  obtain ⟨x, hx⟩ : ∃ x, X x ≠ 0 := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    exact hX0 (LinearMap.ext hc)
  set v : V := X x with hv
  have hXv : X v = 0 := by
    have h1 : (X * X) x = 0 := by rw [← sq, hX]; simp
    simpa [Module.End.mul_apply] using h1
  have hXYv : X (Y v) = t • v := by
    have h1 : (X * Y + Y * X) v = (t • (1 : End k V)) v := by rw [hXY]
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hXv, map_zero, add_zero,
      LinearMap.smul_apply, Module.End.one_apply] using h1
  have hYYv : Y (Y v) = 0 := by
    have h1 : (Y * Y) v = 0 := by rw [← sq, hY]; simp
    simpa [Module.End.mul_apply] using h1
  set U : Submodule k V := Submodule.span k {v, Y v} with hU
  have hvU : v ∈ U := Submodule.subset_span (by simp)
  have hYvU : Y v ∈ U := Submodule.subset_span (by simp)
  have key : ∀ f : End k V, f v ∈ U → f (Y v) ∈ U → ∀ y ∈ U, f y ∈ U := by
    intro f h1 h2 y hy
    have hle : U ≤ U.comap f := by
      rw [hU, Submodule.span_le]
      rintro z (rfl | rfl)
      · exact h1
      · exact h2
    exact hle hy
  have hXmaps : ∀ y ∈ U, X y ∈ U :=
    key X (by rw [hXv]; exact U.zero_mem) (by rw [hXYv]; exact U.smul_mem _ hvU)
  have hYmaps : ∀ y ∈ U, Y y ∈ U := key Y hYvU (by rw [hYYv]; exact U.zero_mem)
  have hUtop : U = ⊤ := by
    refine (eq_bot_or_eq_top_of_forall_mem_stabilizer hirr ?_).resolve_left ?_
    · rintro g (rfl | rfl)
      · exact mem_stabilizer_of_sq_eq_zero hX hu hXmaps
      · exact mem_stabilizer_of_sq_eq_zero hY hw hYmaps
    · intro hbot
      exact hx (by simpa [hbot] using hvU)
  have h1 : Module.rank k (Submodule.span k ({v, Y v} : Set V)) ≤ Cardinal.mk ({v, Y v} : Set V) :=
    rank_span_le _
  have h2 : Cardinal.mk ({v, Y v} : Set V) ≤ 2 := by
    have h3 := Cardinal.mk_insert_le (s := ({Y v} : Set V)) (a := v)
    simp only [Cardinal.mk_singleton] at h3
    exact h3.trans (by norm_num)
  rw [← hU, hUtop] at h1
  rw [← rank_top k V]
  exact h1.trans h2

theorem finrank_le_two_of_sq_eq_zero_of_isIrreducible {X Y : End k V} {t : k}
    (hX : X ^ 2 = 0) (hY : Y ^ 2 = 0) (hXY : X * Y + Y * X = t • 1) (hX0 : X ≠ 0)
    (hirr : (Representation.ofDistribMulAction k
      (Subgroup.closure {unitOneAddOfSqEqZero X hX, unitOneAddOfSqEqZero Y hY}) V).IsIrreducible) :
    Module.finrank k V ≤ 2 :=
  Module.finrank_le_of_rank_le <| by
    simpa using rank_le_two_of_sq_eq_zero_of_isIrreducible hX hY hXY hX0
      (unitOneAddOfSqEqZero_val X hX) (unitOneAddOfSqEqZero_val Y hY) hirr

end CFSG.FeitThompson
