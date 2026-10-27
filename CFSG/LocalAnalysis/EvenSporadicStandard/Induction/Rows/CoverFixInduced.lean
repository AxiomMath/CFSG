module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.EvenSporadicStandard.Induction.CoverFix

open Subgroup

variable {K G : Type*} [Group K] [Group G]

@[expose] def fixed (α : MulAut K) : Subgroup K where
  carrier := {x | α x = x}
  mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) => by
    show α (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one α
  inv_mem' := fun {a} (ha : α a = a) => by
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixed {α : MulAut K} {x : K} : x ∈ fixed α ↔ α x = x := Iff.rfl

theorem exists_induced (π : K →* G) (hπ : Function.Surjective π) (hker : π.ker = center K)
    (α : MulAut K) : ∃ β : MulAut G, ∀ x, π (α x) = β (π x) := by
  have hmap : π.ker.map α.toMonoidHom = π.ker := by
    rw [hker]
    exact Subgroup.map_center_eq α
  let αq : K ⧸ π.ker ≃* K ⧸ π.ker := QuotientGroup.congr π.ker π.ker α hmap
  let e : K ⧸ π.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨(e.symm.trans αq).trans e, fun x => ?_⟩
  show π (α x) = e (αq (e.symm (π x)))
  have h1 : e.symm (π x) = (x : K ⧸ π.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [h1]
  rfl

theorem isMulCommutative_of_le_center {N : Subgroup K} (hN : N ≤ center K) :
    IsMulCommutative ↥N := ⟨⟨fun a b => Subtype.ext (mem_center_iff.1 (hN b.2) a)⟩⟩

@[expose] def discrHom (π : K →* G) (hZ : π.ker ≤ center K) (α : MulAut K) (C : Subgroup K)
    (h : ∀ x ∈ C, π (α x) = π x) : ↥C →* ↥π.ker where
  toFun x := ⟨(x : K)⁻¹ * α x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h x x.2, inv_mul_cancel]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hx : (x : K)⁻¹ * α x ∈ center K := hZ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h x x.2, inv_mul_cancel])
    have hc := mem_center_iff.1 hx
    show ((x : K) * y)⁻¹ * α (x * y) = ((x : K)⁻¹ * α x) * ((y : K)⁻¹ * α y)
    rw [map_mul, mul_inv_rev]
    calc (y : K)⁻¹ * (x : K)⁻¹ * (α x * α y) = (y : K)⁻¹ * ((x : K)⁻¹ * α x) * α y := by
          group
      _ = ((x : K)⁻¹ * α x) * (y : K)⁻¹ * α y := by rw [hc (y : K)⁻¹]
      _ = ((x : K)⁻¹ * α x) * ((y : K)⁻¹ * α y) := by group

theorem mem_ker_discrHom (π : K →* G) (hZ : π.ker ≤ center K) (α : MulAut K) (C : Subgroup K)
    (h : ∀ x ∈ C, π (α x) = π x) (x : C) :
    x ∈ (discrHom π hZ α C h).ker ↔ α x = x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have h1 : (x : K)⁻¹ * α x = 1 := congrArg Subtype.val hx
    exact (inv_mul_eq_one.1 h1).symm
  · intro hx
    apply Subtype.ext
    show (x : K)⁻¹ * α x = 1
    rw [hx, inv_mul_cancel]

theorem eq_one_of_induced_eq_one (hperf : Group.IsPerfect K) (π : K →* G)
    (hZ : π.ker ≤ center K) {α : MulAut K} (h : ∀ x, π (α x) = π x) : α = 1 := by
  have : IsMulCommutative ↥π.ker := isMulCommutative_of_le_center hZ
  have hperfTop : Group.IsPerfect ↥(⊤ : Subgroup K) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := K)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := K)).symm.surjective
  have hker : commutator ↥(⊤ : Subgroup K) ≤ (discrHom π hZ α ⊤ fun x _ => h x).ker :=
    Abelianization.commutator_subset_ker _
  refine MulEquiv.ext fun x => ?_
  have hx : (⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup K)) ∈
      (discrHom π hZ α ⊤ fun x _ => h x).ker := by
    apply hker
    rw [hperfTop.commutator_eq_top]
    exact Subgroup.mem_top _
  exact (mem_ker_discrHom π hZ α ⊤ (fun x _ => h x) ⟨x, Subgroup.mem_top x⟩).1 hx

theorem eq_conj_of_induced_conj (hperf : Group.IsPerfect K) (π : K →* G)
    (hZ : π.ker ≤ center K) {α : MulAut K} {g : K}
    (h : ∀ x, π (α x) = π (g * x * g⁻¹)) : α = MulAut.conj g := by
  have h1 : (MulAut.conj g)⁻¹ * α = 1 := by
    refine eq_one_of_induced_eq_one hperf π hZ fun x => ?_
    have hx : π ((MulAut.conj g)⁻¹ (α x)) = π (g⁻¹ * α x * g) := by
      congr 1
    rw [MulAut.mul_apply, hx, map_mul, map_mul, map_inv]
    have h2 := h x
    rw [map_mul, map_mul, map_inv] at h2
    rw [h2]
    group
  exact (inv_mul_eq_one.1 h1).symm

theorem induced_ne_one (hperf : Group.IsPerfect K) (π : K →* G) (hZ : π.ker ≤ center K)
    {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x)) (hα : α ≠ 1) : β ≠ 1 := by
  intro hβ
  apply hα
  exact eq_one_of_induced_eq_one hperf π hZ fun x => by rw [h x, hβ]; rfl

theorem induced_sq (π : K →* G) (hπ : Function.Surjective π) {α : MulAut K} {β : MulAut G}
    (h : ∀ x, π (α x) = β (π x)) (hα : α * α = 1) : β * β = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := hπ y
  show β (β (π x)) = π x
  rw [← h, ← h]
  have := congrArg (fun f : MulAut K => f x) hα
  simp only [MulAut.mul_apply, MulAut.one_apply] at this
  rw [this]

theorem not_isSolvable_fixed_of_induced (π : K →* G) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ center K) {α : MulAut K} {β : MulAut G} (h : ∀ x, π (α x) = β (π x))
    (hβ : ¬ Group.IsSolvable ↥(fixed β)) : ¬ Group.IsSolvable ↥(fixed α) := by
  intro hsol
  let C : Subgroup K := (fixed β).comap π
  have hC : ∀ x ∈ C, π (α x) = π x := fun x hx => by
    rw [h x]
    exact hx
  have hleC : fixed α ≤ C := fun x hx => by
    show β (π x) = π x
    rw [← h x]
    exact congrArg π hx
  have hCsol : Group.IsSolvable ↥C := by
    have : Group.IsSolvable ↥π.ker := by
      have : IsMulCommutative ↥π.ker := isMulCommutative_of_le_center hZ
      infer_instance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hleC)
      (discrHom π hZ α C hC) ?_
    intro x hx
    have h1 := (mem_ker_discrHom π hZ α C hC x).1 hx
    exact ⟨⟨x, h1⟩, rfl⟩
  let f : ↥C →* ↥(fixed β) :=
    (π.comp C.subtype).codRestrict (fixed β) fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hβ (Group.isSolvable_of_surjective hf)

end CFSG.EvenSporadicStandard.Induction.CoverFix
