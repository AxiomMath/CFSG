module

public import CFSG.LargeExtraspecial.DWTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem polar_apply_apply (x : S.O) (v w : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
      polar S.q v w := by
  simp only [polar, ← map_add]
  rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2]

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
include hA

theorem mul_self_eq_one_of_forall_clSub {y : S.O}
    (hy : ∀ v ∈ S.clSub A, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : y * y = 1 := by
  have hmove : ∀ v, (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ S.clSub A := by
    intro v
    rw [← hA.orthogonal_clSub, LinearMap.BilinForm.mem_orthogonal_iff]
    intro a ha
    change polar S.q a ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) = 0
    rw [polar_sub_right, ← polar_apply_apply y a v, hy a ha, sub_self]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  change (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
  have h1 := hy _ (hmove v)
  rw [map_sub] at h1
  have h2 : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (y : S.Qt ≃ₗ[ZMod 2] S.Qt) v + ((y : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
    rw [← h1]
    abel
  rw [h2, ← add_sub_assoc, two_add_self, zero_sub, two_neg]

omit [IsElementaryAbelian 2 A] hA in
theorem apply_mem_clSub (hM : S.M ≤ normalizer (A : Set G)) {x : S.O} (hx : x ∈ S.Mbar)
    {v : S.Qt} (hv : v ∈ S.clSub A) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ S.clSub A := by
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨a, haA, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
  rw [S.ρ_cl g haQ]
  exact S.cl_mem_clSub ((mem_normalizer_iff.mp (hM g.2) a).mp haA)
    (S.conj_mem_QG g.2 haQ)

end MaxEA

variable (S) in
@[expose] def kerAt (A : Subgroup G) : Subgroup S.Mbar where
  carrier := {y | ∀ v ∈ S.clSub A, ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v}
  mul_mem' {y y'} hy hy' v hv := by
    change ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v
    rw [hy' v hv, hy v hv]
  one_mem' _ _ := rfl
  inv_mem' {y} hy v hv := by
    change ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm v = v
    rw [LinearEquiv.symm_apply_eq, hy v hv]

namespace MaxEA

variable {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)

omit [IsElementaryAbelian 2 A] in
theorem kerAt_normal (hM : S.M ≤ normalizer (A : Set G)) : (kerAt S A).Normal := by
  refine ⟨fun y hy g v hv => ?_⟩
  have hgv : ((g⁻¹ : S.Mbar) : S.O).1 v ∈ S.clSub A :=
    apply_mem_clSub hM (g⁻¹ : S.Mbar).2 hv
  change ((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    (((g⁻¹ : S.Mbar) : S.O).1 v)) = v
  rw [hy _ hgv]
  change ((g * g⁻¹ : S.Mbar) : S.O).1 v = v
  rw [mul_inv_cancel]
  rfl

include hA

theorem kerAt_isPGroup : IsPGroup 2 (kerAt S A) := by
  intro y
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  rw [pow_one, pow_two]
  exact hA.mul_self_eq_one_of_forall_clSub y.2

variable (hM : S.M ≤ normalizer (A : Set G))
include hM

theorem eq_one_of_forall_clSub {x : S.O} (hx : x ∈ S.Mbar)
    (h : ∀ v ∈ S.clSub A, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : x = 1 := by
  have hle : kerAt S A ≤ CFSG.pCore 2 S.Mbar :=
    le_sSup ⟨kerAt_normal hM, hA.kerAt_isPGroup⟩
  rw [S.pCore_Mbar_eq_bot] at hle
  have := hle (show (⟨x, hx⟩ : S.Mbar) ∈ kerAt S A from h)
  rw [mem_bot] at this
  exact congrArg Subtype.val this

theorem centralizer_eq : centralizer (A : Set G) = A := by
  refine le_antisymm (fun g hg => ?_) fun a ha => mem_centralizer_iff.mpr fun b hb =>
    comm_of_mem hb ha
  have hgM : g ∈ S.M := mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hg) S.z hA.z_mem).symm
  have hρ : S.ρ ⟨g, hgM⟩ = 1 := by
    refine hA.eq_one_of_forall_clSub hM ⟨⟨g, hgM⟩, rfl⟩ fun v hv => ?_
    obtain ⟨a, haA, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.ρ_cl ⟨g, hgM⟩ haQ]
    change S.cl (g * a * g⁻¹) = S.cl a
    rw [← (mem_centralizer_iff.mp hg) a haA, mul_inv_cancel_right]
  rw [← hA.QG_inf_centralizer]
  exact ⟨(S.ρ_eq_one_iff _).mp hρ, hg⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
