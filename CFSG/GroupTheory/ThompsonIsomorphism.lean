module

public import CFSG.Foundations.MaxOrderThompsonDefs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG

open Subgroup

section Thompson

variable {S T : Type*} [Group S] [Group T]

theorem isMulCommutative_map_mulEquiv_iff (φ : S ≃* T) (A : Subgroup S) :
    IsMulCommutative (A.map φ.toMonoidHom) ↔ IsMulCommutative A := by
  constructor
  · intro h
    have h' : IsMulCommutative ((A.map φ.toMonoidHom).map φ.symm.toMonoidHom) := inferInstance
    rwa [Subgroup.map_map, show φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id S by
      ext; simp, Subgroup.map_id] at h'
  · intro h
    infer_instance

theorem maxAbelianOrder_eq_of_mulEquiv (φ : S ≃* T) : maxAbelianOrder S = maxAbelianOrder T := by
  unfold maxAbelianOrder
  congr 1
  ext k
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨A.map φ.toMonoidHom, (isMulCommutative_map_mulEquiv_iff φ A).mpr hA, ?_⟩
    exact Subgroup.card_map_of_injective φ.injective
  · rintro ⟨B, hB, rfl⟩
    refine ⟨B.map φ.symm.toMonoidHom, (isMulCommutative_map_mulEquiv_iff φ.symm B).mpr hB, ?_⟩
    exact Subgroup.card_map_of_injective φ.symm.injective

theorem image_maxOrderAbelianFamily (φ : S ≃* T) :
    (fun A : Subgroup S => A.map φ.toMonoidHom) '' maxOrderAbelianFamily S =
      maxOrderAbelianFamily T := by
  ext B
  constructor
  · rintro ⟨A, ⟨hA, hcard⟩, rfl⟩
    refine ⟨(isMulCommutative_map_mulEquiv_iff φ A).mpr hA, ?_⟩
    rw [Subgroup.card_map_of_injective φ.injective, hcard, maxAbelianOrder_eq_of_mulEquiv φ]
  · rintro ⟨hB, hcard⟩
    refine ⟨B.map φ.symm.toMonoidHom,
      ⟨(isMulCommutative_map_mulEquiv_iff φ.symm B).mpr hB, ?_⟩, ?_⟩
    · rw [Subgroup.card_map_of_injective φ.symm.injective, hcard,
        maxAbelianOrder_eq_of_mulEquiv φ]
    · show (B.map φ.symm.toMonoidHom).map φ.toMonoidHom = B
      rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id T by
        ext; simp, Subgroup.map_id]

theorem map_orderThompson (φ : S ≃* T) :
    (orderThompson S).map φ.toMonoidHom = orderThompson T := by
  unfold orderThompson
  rw [(Subgroup.gc_map_comap φ.toMonoidHom).l_sSup, ← sSup_image, image_maxOrderAbelianFamily]

theorem mem_map_center_subtype_iff {G : Type*} [Group G] (K : Subgroup G) (x : G) :
    x ∈ (center K).map K.subtype ↔ x ∈ K ∧ ∀ y ∈ K, y * x = x * y := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, fun y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun y => Subtype.ext (h y y.2), rfl⟩

theorem map_center_subtype_of_mulEquiv (φ : S ≃* T) (K : Subgroup S) :
    ((center K).map K.subtype).map φ.toMonoidHom =
      (center (K.map φ.toMonoidHom)).map (K.map φ.toMonoidHom).subtype := by
  ext x
  rw [mem_map_center_subtype_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    replace hy := (mem_map_center_subtype_iff K y).mp hy
    refine ⟨⟨y, hy.1, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hy.2 z hz]
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    refine ⟨y, (mem_map_center_subtype_iff K y).mpr ⟨hy, fun z hz => φ.injective ?_⟩, rfl⟩
    have := h (φ z) ⟨z, hz, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, map_mul] using this

theorem map_orderZJ (φ : S ≃* T) : (orderZJ S).map φ.toMonoidHom = orderZJ T := by
  unfold orderZJ
  rw [map_center_subtype_of_mulEquiv]
  ext x
  rw [mem_map_center_subtype_iff, mem_map_center_subtype_iff, map_orderThompson φ]

theorem thompson_isomorphism [Finite S] [Finite T] (φ : S ≃* T) :
    maxAbelianOrder S = maxAbelianOrder T ∧
      (fun A : Subgroup S => A.map φ.toMonoidHom) '' maxOrderAbelianFamily S =
        maxOrderAbelianFamily T ∧
      (orderThompson S).map φ.toMonoidHom = orderThompson T ∧
      (orderZJ S).map φ.toMonoidHom = orderZJ T ∧
      (orderThompson S).Characteristic ∧ (orderZJ S).Characteristic :=
  ⟨maxAbelianOrder_eq_of_mulEquiv φ, image_maxOrderAbelianFamily φ, map_orderThompson φ,
    map_orderZJ φ, characteristic_iff_map_eq.mpr fun ψ => map_orderThompson ψ,
    characteristic_iff_map_eq.mpr fun ψ => map_orderZJ ψ⟩

end Thompson

end CFSG
