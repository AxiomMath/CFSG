module

public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed

theorem involution_unique_fixed_point_card_odd
    {K Ω : Type*} [Group K] [MulAction K Ω] [Finite Ω]
    (s : K) (hs : orderOf s = 2) (a : Ω)
    (hunique : ∀ x : Ω, s • x = x ↔ x = a) : Odd (Nat.card Ω) := by
  let Z := Subgroup.zpowers s
  have hbase : a ∈ MulAction.fixedPoints Z Ω := by
    have hZle : Z ≤ MulAction.stabilizer K a :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr ((hunique a).mpr rfl))
    intro g
    exact MulAction.mem_stabilizer_iff.mp (hZle g.property)
  have hpoint : ∀ x ∈ MulAction.fixedPoints Z Ω, x = a := by
    intro x hx
    apply (hunique x).mp
    exact hx ⟨s, Subgroup.mem_zpowers s⟩
  have hfixedcard : Nat.card (MulAction.fixedPoints Z Ω) = 1 := by
    let : Nonempty (MulAction.fixedPoints Z Ω) := ⟨⟨a, hbase⟩⟩
    let : Subsingleton (MulAction.fixedPoints Z Ω) :=
      ⟨fun x y => Subtype.ext ((hpoint x x.property).trans (hpoint y y.property).symm)⟩
    exact Nat.card_unique
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hs, pow_one])
  have hmod := hZtwo.card_modEq_card_fixedPoints Ω
  rw [hfixedcard] at hmod
  exact Nat.odd_iff.mpr hmod

end CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalOddFixed
