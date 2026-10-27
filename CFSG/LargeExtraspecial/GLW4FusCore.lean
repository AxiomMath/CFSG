module

public import CFSG.LargeExtraspecial.GLW4E

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.GLR

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {K : Type*} [Group K] [Finite K]

structure Lev (T : Setting K) (ι : K →* S.O) (V W : Submodule (ZMod 2) S.Qt) : Prop where
  layered : ∀ α ∈ T.QG, Layered V W (ι α)
  dm_mem : ∀ x, dm (ι T.z) x ∈ V
  dm_onto : ∀ v ∈ V, ∃ x, dm (ι T.z) x = v
  mem_W_of_dm : ∀ x, dm (ι T.z) x = 0 → x ∈ W
  fix_W : ∀ w ∈ W, (ι T.z : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w
  ne_one : ι T.z ≠ 1

namespace Lev

variable {T : Setting K} {ι : K →* S.O} {V W : Submodule (ZMod 2) S.Qt} (L : Lev T ι V W)
include L

omit [Finite K] in
theorem Emap_z_left {β : K} (hβ : β ∈ T.QG) : Emap (ι T.z) (ι β) = 0 :=
  LinearMap.ext fun x => by
    rw [Emap_apply, LinearMap.zero_apply, dm_apply, L.fix_W _ ((L.layered β hβ).mem_W x),
      sub_self]

omit [Finite K] in
theorem Emap_z_right {α : K} (hα : α ∈ T.QG) : Emap (ι α) (ι T.z) = 0 :=
  LinearMap.ext fun x => by
    rw [Emap_apply, LinearMap.zero_apply]
    exact (L.layered α hα).dm_eq_zero (L.dm_mem x)

omit [Finite K] in
theorem Emap_mul_left' {α α' β : K} (hα : α ∈ T.QG) (hα' : α' ∈ T.QG) (hβ : β ∈ T.QG) :
    Emap (ι (α * α')) (ι β) = Emap (ι α) (ι β) + Emap (ι α') (ι β) := by
  rw [map_mul]
  exact Emap_mul_left (L.layered α hα) (L.layered α' hα') (L.layered β hβ)

omit [Finite K] in
theorem Emap_mul_right' {α β β' : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (hβ' : β' ∈ T.QG) :
    Emap (ι α) (ι (β * β')) = Emap (ι α) (ι β) + Emap (ι α) (ι β') := by
  rw [map_mul]
  exact Emap_mul_right (L.layered α hα) (L.layered β hβ) (L.layered β' hβ')

omit [Finite K] in
theorem Emap_cl_left {α α' β : K} (hα : α ∈ T.QG) (hα' : α' ∈ T.QG) (hβ : β ∈ T.QG)
    (h : T.cl α = T.cl α') : Emap (ι α) (ι β) = Emap (ι α') (ι β) := by
  rcases (T.cl_eq_cl_iff hα hα').mp h with rfl | rfl
  · rfl
  · rw [L.Emap_mul_left' hα T.z_mem_QG hβ, L.Emap_z_left hβ, add_zero]

omit [Finite K] in
theorem Emap_cl_right {α β β' : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (hβ' : β' ∈ T.QG)
    (h : T.cl β = T.cl β') : Emap (ι α) (ι β) = Emap (ι α) (ι β') := by
  rcases (T.cl_eq_cl_iff hβ hβ').mp h with rfl | rfl
  · rfl
  · rw [L.Emap_mul_right' hα hβ T.z_mem_QG, L.Emap_z_right hα, add_zero]

theorem Emap_add_swap_of_polar {α β : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG)
    (h1 : polar T.q (T.cl α) (T.cl β) = 1) :
    Emap (ι α) (ι β) + Emap (ι β) (ι α) = dm (ι T.z) := by
  have hne : α * β ≠ β * α := fun h => by
    rw [(T.polar_cl_eq_zero_iff hα hβ).mpr h] at h1
    exact zero_ne_one h1
  have hc : α * β = β * α * T.z := by
    rcases T.commutator_eq_one_or_z hα hβ with h | h
    · exfalso
      apply hne
      calc α * β = α * β * α⁻¹ * β⁻¹ * (β * α) := by group
        _ = β * α := by rw [h, one_mul]
    · calc α * β = (α * β * α⁻¹ * β⁻¹) * (β * α) := by group
        _ = T.z * (β * α) := by rw [h]
        _ = β * α * T.z := (T.z_comm_QG (T.QG.mul_mem hβ hα)).symm
  have hc' : ι α * ι β = ι β * ι α * ι T.z := by
    have := congrArg ι hc
    simpa only [map_mul] using this
  refine Emap_add_swap_of_mul_eq L.dm_mem (fun v hv => ?_) hc'
  rw [← map_mul]
  exact (L.layered _ (T.QG.mul_mem hβ hα)).fix v hv

omit [Finite K] in
theorem polar_Emap_swap {α β : K} (hα : α ∈ T.QG) (hβ : β ∈ T.QG) (x y : S.Qt) :
    polar S.q (Emap (ι α) (ι β) x) y = polar S.q x (Emap (ι β) (ι α) y) := by
  rw [polar_Emap, ← map_inv, ← map_inv,
    L.Emap_cl_left (T.QG.inv_mem hβ) hβ (T.QG.inv_mem hα) (T.cl_inv hβ),
    L.Emap_cl_right hβ (T.QG.inv_mem hα) hα (T.cl_inv hα)]

end Lev

end CFSG.LargeExtraspecial.GLW4
