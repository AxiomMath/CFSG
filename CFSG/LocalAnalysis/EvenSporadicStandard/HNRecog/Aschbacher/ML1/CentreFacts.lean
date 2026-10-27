module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.CenterCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

variable {C : Type} [Group C] {Q : Subgroup C} [Q.Normal]

theorem AschbacherHyp.exists_centre [Finite C] (hC : AschbacherHyp C Q) :
    ∃ z : C, z ∈ Q ∧ z ≠ 1 ∧ (∀ g : C, g * z = z * g) ∧
      ∀ x ∈ Q, (∀ y ∈ Q, x * y = y * x) → x = 1 ∨ x = z := by
  classical
  have hE : IsExtraspecialPGroup 2 ↥Q := hC.plus.isExtraspecialPGroup
  obtain ⟨z0, hz0ne, hz0⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.center ↥Q)).1 hE.2.2.2
  let z' : ↥Q := (z0 : ↥Q)
  let z : C := (z' : C)
  have hzQ : z ∈ Q := z'.2
  have hz'1 : z' ≠ 1 := fun h => hz0ne (Subtype.ext h)
  have hz1 : z ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hzcenterOf : z ∈ centerOf Q := (mem_centerOf_iff z').2 z0.2
  have hzcenter : z ∈ Subgroup.center C := hC.centerOf_le_center hzcenterOf
  have hzcomm : ∀ g : C, g * z = z * g := Subgroup.mem_center_iff.mp hzcenter
  refine ⟨z, hzQ, hz1, hzcomm, ?_⟩
  intro x hx hxcomm
  let x' : ↥Q := ⟨x, hx⟩
  have hx'center : x' ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((hxcomm y y.2).symm)
  by_cases hx1 : x' = 1
  · exact Or.inl (congrArg Subtype.val hx1)
  · refine Or.inr ?_
    have hx'ne : (⟨x', hx'center⟩ : Subgroup.center ↥Q) ≠ 1 := by
      intro h
      exact hx1 (congrArg Subtype.val h)
    have hxz0 : (⟨x', hx'center⟩ : Subgroup.center ↥Q) = z0 := hz0 _ hx'ne
    have hx'z' : x' = z' := congrArg Subtype.val hxz0
    exact congrArg (fun t : ↥Q => (t : C)) hx'z'

theorem AschbacherHyp.exists_pow_two_pow_eq_one (hC : AschbacherHyp C Q) :
    ∀ x ∈ Q, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have hE : IsExtraspecialPGroup 2 ↥Q := hC.plus.isExtraspecialPGroup
  intro x hx
  obtain ⟨k, hk⟩ := hE.1 ⟨x, hx⟩
  exact ⟨k, by simpa [Subgroup.coe_pow] using congrArg Subtype.val hk⟩

end CFSG.EvenSporadicStandard.HNRecog
