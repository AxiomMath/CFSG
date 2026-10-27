module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

def discrepancyHom {K₂ : Type} [Group K₂] (α : MulAut K₂) (C : Subgroup K₂)
    (h : ∀ x ∈ C, x⁻¹ * α x ∈ center K₂) : ↥C →* ↥(center K₂) where
  toFun x := ⟨(x : K₂)⁻¹ * α x, h x x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have hx : (x : K₂)⁻¹ * α x ∈ center K₂ := h x x.2
    have hc := mem_center_iff.1 hx
    show ((x : K₂) * y)⁻¹ * α (x * y) = ((x : K₂)⁻¹ * α x) * ((y : K₂)⁻¹ * α y)
    rw [map_mul, mul_inv_rev]
    calc (y : K₂)⁻¹ * (x : K₂)⁻¹ * (α x * α y) = (y : K₂)⁻¹ * ((x : K₂)⁻¹ * α x) * α y := by
          group
      _ = ((x : K₂)⁻¹ * α x) * (y : K₂)⁻¹ * α y := by rw [hc (y : K₂)⁻¹]
      _ = ((x : K₂)⁻¹ * α x) * ((y : K₂)⁻¹ * α y) := by group

theorem not_isSolvable_fix_of_cover {K₂ : Type} [Group K₂] [Finite K₂]
    (hperf : Group.IsPerfect K₂) {α : MulAut K₂} (hα1 : α ≠ 1) (hα2 : α * α = 1)
    (hfix : ∀ β : MulAut (K₂ ⧸ center K₂), β ≠ 1 → β * β = 1 →
      ¬ Group.IsSolvable ↥(fixSubgroup β)) :
    ¬ Group.IsSolvable ↥(fixSubgroup α) := by
  intro hsol
  let π : K₂ →* K₂ ⧸ center K₂ := QuotientGroup.mk' (center K₂)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let β : MulAut (K₂ ⧸ center K₂) :=
    QuotientGroup.congr (center K₂) (center K₂) α (Subgroup.map_center_eq α)
  have hβπ : ∀ x, β (π x) = π (α x) := fun x => rfl
  have hαα : ∀ x, α (α x) = x := fun x => by
    have := congrArg (fun f : MulAut K₂ => f x) hα2
    simpa using this
  have hβ2 : β * β = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    show β (β (π x)) = π x
    rw [hβπ, hβπ, hαα]
  have key : ∀ x : K₂, x⁻¹ * α x = 1 → α x = x := fun x h =>
    (inv_inj.1 (mul_eq_one_iff_eq_inv.1 h)).symm
  have hz : ∀ x : K₂, β (π x) = π x → x⁻¹ * α x ∈ center K₂ := fun x hx => by
    rw [hβπ] at hx
    exact (QuotientGroup.eq (a := x) (b := α x)).1 hx.symm
  have hβ1 : β ≠ 1 := by
    intro hβ
    have hall : ∀ x ∈ (⊤ : Subgroup K₂), x⁻¹ * α x ∈ center K₂ := fun x _ =>
      hz x (by rw [hβ]; rfl)
    have hcomm : ∀ a b : ↥(center K₂), a * b = b * a := fun a b =>
      Subtype.ext (mem_center_iff.1 b.2 a)
    have hperfTop : Group.IsPerfect ↥(⊤ : Subgroup K₂) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := K₂)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := K₂)).symm.surjective
    apply hα1
    ext x
    have h1 := Hyp.eq_one_of_perfect_of_comm hperfTop (discrepancyHom α ⊤ hall) hcomm
      ⟨x, mem_top x⟩
    have h2 : x⁻¹ * α x = 1 := congrArg Subtype.val h1
    exact key x h2
  have hfix' := hfix β hβ1 hβ2
  let C : Subgroup K₂ := (fixSubgroup β).comap π
  have hC : ∀ x ∈ C, x⁻¹ * α x ∈ center K₂ := fun x hx => hz x hx
  have hleC : fixSubgroup α ≤ C := fun x hx => by
    show β (π x) = π x
    rw [hβπ]
    exact congrArg π hx
  have hCsol : Group.IsSolvable ↥C := by
    have : Group.IsSolvable ↥(center K₂) := inferInstance
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hleC) (discrepancyHom α C hC) ?_
    intro x hx
    have h1 : (x : K₂)⁻¹ * α x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    exact ⟨⟨x, key x h1⟩, rfl⟩
  let h : ↥C →* ↥(fixSubgroup β) := (π.comp C.subtype).codRestrict (fixSubgroup β) fun x => x.2
  have hh : Function.Surjective h := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  exact hfix' (Group.isSolvable_of_surjective hh)

end CFSG.EvenSporadicStandard.Induction
