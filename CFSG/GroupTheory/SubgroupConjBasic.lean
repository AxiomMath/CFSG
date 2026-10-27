module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GroupTheory

open Subgroup

variable {H : Type*} [Group H]

theorem centralizer_zpowers_sup_zpowers (x y : H) :
    Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup H) : Set H) =
      Subgroup.centralizer ({x, y} : Set H) := by
  have h : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup H) =
      Subgroup.closure ({x, y} : Set H) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [h, Subgroup.centralizer_closure]

theorem normalizer_le_of_map_conj_le {M X : Subgroup H} {n : H} (hn : n ∈ M)
    (h : Subgroup.normalizer ((X.map (MulAut.conj n).toMonoidHom : Subgroup H) : Set H) ≤ M) :
    Subgroup.normalizer (X : Set H) ≤ M := by
  intro x hx
  have hmap : n * x * n⁻¹ ∈
      Subgroup.normalizer ((X.map (MulAut.conj n).toMonoidHom : Subgroup H) : Set H) := by
    have hx' : (MulAut.conj n).toMonoidHom x ∈
        (Subgroup.normalizer (X : Set H)).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj n).toMonoidHom hx
    rwa [Subgroup.map_equiv_normalizer_eq] at hx'
  have hxM : n * x * n⁻¹ ∈ M := h hmap
  have hxeq : x = n⁻¹ * (n * x * n⁻¹) * n := by
    symm
    calc n⁻¹ * (n * x * n⁻¹) * n
        = n⁻¹ * ((n * x) * n⁻¹) * n := by rw [mul_assoc]
      _ = (n⁻¹ * (n * x)) * n⁻¹ * n := by rw [← mul_assoc]
      _ = x * n⁻¹ * n := by rw [inv_mul_cancel_left]
      _ = x * (n⁻¹ * n) := by rw [mul_assoc]
      _ = x * 1 := by rw [inv_mul_cancel]
      _ = x := by rw [mul_one]
  rw [hxeq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hn) hxM) hn

theorem zpowers_coe_subgroupOf {K : Subgroup H} (x : K) :
    (Subgroup.zpowers (x : H)).subgroupOf K = Subgroup.zpowers x := by
  change (Subgroup.zpowers (K.subtype x)).subgroupOf K = Subgroup.zpowers x
  rw [← MonoidHom.map_zpowers K.subtype x]
  exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _

end CFSG.GroupTheory
