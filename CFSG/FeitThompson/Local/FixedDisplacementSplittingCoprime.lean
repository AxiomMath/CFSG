module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {B V : Type*} [Group B] [AddCommGroup V] [DistribMulAction B V]

def displacementAddSubgroup (B V : Type*) [Group B] [AddCommGroup V] [DistribMulAction B V] :
    AddSubgroup V :=
  AddSubgroup.closure {x | ∃ (b : B) (v : V), b • v - v = x}

theorem displacementAddSubgroup_eq_closure :
    displacementAddSubgroup B V
      = AddSubgroup.closure {x | ∃ (b : B) (v : V), b • v - v = x} := (rfl)

theorem sub_mem_displacementAddSubgroup (b : B) (v : V) :
    b • v - v ∈ displacementAddSubgroup B V :=
  AddSubgroup.subset_closure ⟨b, v, rfl⟩

theorem displacementAddSubgroup_le {H : AddSubgroup V}
    (h : ∀ (b : B) (v : V), b • v - v ∈ H) : displacementAddSubgroup B V ≤ H := by
  rw [displacementAddSubgroup_eq_closure, AddSubgroup.closure_le]
  rintro x ⟨b, v, rfl⟩
  exact h b v

theorem smul_mem_displacementAddSubgroup (b : B) {v : V}
    (hv : v ∈ displacementAddSubgroup B V) : b • v ∈ displacementAddSubgroup B V := by
  have h : displacementAddSubgroup B V
      ≤ (displacementAddSubgroup B V).comap (DistribSMul.toAddMonoidHom V b) := by
    refine displacementAddSubgroup_le fun b' v' => ?_
    have hb : b • (b' • v') = (b * b' * b⁻¹) • (b • v') := by
      rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
    simp only [AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply, smul_sub, hb]
    exact sub_mem_displacementAddSubgroup _ _
  exact h hv

open Pointwise in
theorem smul_displacementAddSubgroup (b : B) :
    b • displacementAddSubgroup B V = displacementAddSubgroup B V := by
  refine le_antisymm ?_ ?_ <;> intro x hx
  · obtain ⟨y, hy, rfl⟩ := hx
    exact smul_mem_displacementAddSubgroup b hy
  · refine ⟨b⁻¹ • x, smul_mem_displacementAddSubgroup b⁻¹ hx, ?_⟩
    change b • (b⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel, one_smul]

private theorem zsmul_eq_self_of_bezout {W : Type*} [AddCommGroup W] [Finite W] {n : ℕ} {k m : ℤ}
    (hk : k * n + m * Nat.card W = 1) (v : W) : (k * n) • v = v := by
  have hW : ((Nat.card W : ℤ)) • v = 0 := by
    rw [natCast_zsmul]; exact card_nsmul_eq_zero'
  have h : k * (n : ℤ) = 1 - m * Nat.card W := by linarith
  rw [h, sub_zsmul, one_zsmul, mul_zsmul, hW, smul_zero]
  simp

section Average

variable (B V) [Fintype B]

private def avgHom : V →+ V where
  toFun v := ∑ b : B, b • v
  map_zero' := by simp
  map_add' x y := by simp [smul_add, Finset.sum_add_distrib]

private theorem avgHom_apply (v : V) : avgHom B V v = ∑ b : B, b • v := (rfl)

private theorem avgHom_smul (b₀ : B) (v : V) : avgHom B V (b₀ • v) = avgHom B V v := by
  simp only [avgHom_apply]
  exact Fintype.sum_equiv (Equiv.mulRight b₀) _ _ fun b => (mul_smul b b₀ v).symm

private theorem smul_avgHom (b₀ : B) (v : V) : b₀ • avgHom B V v = avgHom B V v := by
  simp only [avgHom_apply, Finset.smul_sum]
  exact Fintype.sum_equiv (Equiv.mulLeft b₀) _ _ fun b => (mul_smul b₀ b v).symm

private theorem avgHom_of_fixed {v : V} (h : ∀ b : B, b • v = v) :
    avgHom B V v = Nat.card B • v := by
  rw [avgHom_apply, Finset.sum_congr rfl fun b _ => h b, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

private def projHom (k : ℤ) : V →+ V :=
  AddMonoidHom.mk' (fun v => k • avgHom B V v) (fun x y => by simp [smul_add])

private theorem projHom_apply (k : ℤ) (v : V) : projHom B V k v = k • avgHom B V v := (rfl)

private theorem smul_projHom (k : ℤ) (b₀ : B) (v : V) :
    b₀ • projHom B V k v = projHom B V k v := by
  rw [projHom_apply, smul_comm, smul_avgHom]

private theorem avgHom_of_mem_displacement {v : V}
    (hv : v ∈ displacementAddSubgroup B V) : avgHom B V v = 0 := by
  have h : displacementAddSubgroup B V ≤ (avgHom B V).ker := by
    refine displacementAddSubgroup_le fun b v => ?_
    simp only [AddMonoidHom.mem_ker, map_sub, avgHom_smul, sub_self]
  exact h hv

variable [Finite V] {k m : ℤ}

private theorem projHom_of_fixed (hk : k * Nat.card B + m * Nat.card V = 1) {v : V}
    (h : ∀ b : B, b • v = v) : projHom B V k v = v := by
  rw [projHom_apply, avgHom_of_fixed B V h, ← natCast_zsmul, smul_smul]
  exact zsmul_eq_self_of_bezout hk v

private theorem sub_projHom_mem (hk : k * Nat.card B + m * Nat.card V = 1) (v : V) :
    v - projHom B V k v ∈ displacementAddSubgroup B V := by
  have hsum : ∑ b : B, (v - b • v) ∈ displacementAddSubgroup B V := by
    refine AddSubgroup.sum_mem _ fun b _ => ?_
    rw [← neg_sub]
    exact neg_mem (sub_mem_displacementAddSubgroup b v)
  have hval : v - projHom B V k v = k • ∑ b : B, (v - b • v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      smul_sub, ← natCast_zsmul v (Nat.card B), smul_smul, zsmul_eq_self_of_bezout hk v,
      projHom_apply, avgHom_apply]
  rw [hval]
  exact zsmul_mem hsum k

end Average

section Main

variable [Finite B] [Finite V] (hcop : Nat.Coprime (Nat.card B) (Nat.card V))
include hcop

theorem isCompl_fixedPoints_displacementAddSubgroup :
    IsCompl (FixedPoints.addSubgroup B V) (displacementAddSubgroup B V) := by
  cases nonempty_fintype B
  obtain ⟨k, m, hk⟩ := Nat.isCoprime_iff_coprime.2 hcop
  constructor
  · rw [AddSubgroup.disjoint_def]
    intro v hvC hvD
    have h₁ : projHom B V k v = v :=
      projHom_of_fixed B V hk ((FixedPoints.mem_addSubgroup B V v).1 hvC)
    have h₂ : projHom B V k v = 0 := by
      rw [projHom_apply, avgHom_of_mem_displacement B V hvD, smul_zero]
    rw [← h₁, h₂]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hC : projHom B V k v ∈ FixedPoints.addSubgroup B V :=
      (FixedPoints.mem_addSubgroup B V _).2 fun b => smul_projHom B V k b v
    have hD : v - projHom B V k v ∈ displacementAddSubgroup B V := sub_projHom_mem B V hk v
    have h := AddSubgroup.add_mem_sup hC hD
    simpa using h

theorem sup_fixedPoints_displacementAddSubgroup_eq_top :
    FixedPoints.addSubgroup B V ⊔ displacementAddSubgroup B V = ⊤ :=
  (isCompl_fixedPoints_displacementAddSubgroup hcop).sup_eq_top

theorem inf_fixedPoints_displacementAddSubgroup_eq_bot :
    FixedPoints.addSubgroup B V ⊓ displacementAddSubgroup B V = ⊥ :=
  (isCompl_fixedPoints_displacementAddSubgroup hcop).inf_eq_bot

theorem exists_add_eq_of_coprime (v : V) :
    ∃ c ∈ FixedPoints.addSubgroup B V, ∃ d ∈ displacementAddSubgroup B V, c + d = v := by
  have h : v ∈ FixedPoints.addSubgroup B V ⊔ displacementAddSubgroup B V := by
    rw [sup_fixedPoints_displacementAddSubgroup_eq_top hcop]; trivial
  rw [AddSubgroup.mem_sup] at h
  obtain ⟨c, hc, d, hd, rfl⟩ := h
  exact ⟨c, hc, d, hd, rfl⟩

theorem eq_zero_of_mem_displacementAddSubgroup_of_forall_smul_eq
    {v : V} (hv : v ∈ displacementAddSubgroup B V) (h : ∀ b : B, b • v = v) : v = 0 := by
  have hmem : v ∈ FixedPoints.addSubgroup B V ⊓ displacementAddSubgroup B V :=
    ⟨(FixedPoints.mem_addSubgroup B V v).2 h, hv⟩
  rwa [inf_fixedPoints_displacementAddSubgroup_eq_bot hcop, AddSubgroup.mem_bot] at hmem

end Main

end CFSG.FeitThompson
