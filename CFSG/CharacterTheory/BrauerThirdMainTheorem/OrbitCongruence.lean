module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalRing

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem invariant_sum_congr_fixed (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprime : prime.Prime) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    {actingGroup : Type*} [Group actingGroup] (hpGroup : IsPGroup prime actingGroup)
    {points : Type*} [MulAction actingGroup points] [Finite points]
    (values : points → ℂ) (hvalues : ∀ point, values point ∈ BlocksLocalRing m)
    (hinvariant : ∀ (actingElement : actingGroup) (point : points),
      values (actingElement • point) = values point) :
    (∑ᶠ point : points, values point) -
      (∑ᶠ point : points, (MulAction.fixedPoints actingGroup points).indicator values point) ∈
        BlocksLocalMaxIdeal m := by
  classical
  let : Fact prime.Prime := ⟨hprime⟩
  let : Fintype points := Fintype.ofFinite points
  let valueSet := Finset.univ.image values
  let fiber (coefficient : ℂ) := Finset.univ.filter (fun point : points => values point = coefficient)
  let fixedFiber (coefficient : ℂ) := Finset.univ.filter
    (fun point : points => values point = coefficient ∧
      point ∈ MulAction.fixedPoints actingGroup points)
  have hsum : (∑ point : points, values point) =
      ∑ coefficient ∈ valueSet, (fiber coefficient).card • coefficient := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := valueSet) (g := values)
      (fun point _ => Finset.mem_image.mpr ⟨point, Finset.mem_univ point, rfl⟩) values]
    apply Finset.sum_congr rfl
    intro coefficient _
    change (∑ point ∈ fiber coefficient, values point) = (fiber coefficient).card • coefficient
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro point hpoint
    exact (Finset.mem_filter.mp hpoint).2
  have hfixedSum :
      (∑ point : points, (MulAction.fixedPoints actingGroup points).indicator values point) =
        ∑ coefficient ∈ valueSet, (fixedFiber coefficient).card • coefficient := by
    let fixedPoints := Finset.univ.filter
      (fun point : points => point ∈ MulAction.fixedPoints actingGroup points)
    have hfilterSum :
        (∑ point : points, (MulAction.fixedPoints actingGroup points).indicator values point) =
          ∑ point ∈ fixedPoints, values point := by
      simp only [fixedPoints, Finset.sum_filter, Set.indicator_apply]
    rw [hfilterSum]
    rw [← Finset.sum_fiberwise_of_maps_to (s := fixedPoints) (t := valueSet) (g := values)
      (fun point _ => Finset.mem_image.mpr ⟨point, Finset.mem_univ point, rfl⟩) values]
    apply Finset.sum_congr rfl
    intro coefficient _
    have hfilters : fixedPoints.filter (fun point => values point = coefficient) =
        fixedFiber coefficient := by
      ext point
      simp only [fixedPoints, fixedFiber, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
    rw [hfilters, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro point hpoint
    exact (Finset.mem_filter.mp hpoint).2.1
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, hsum, hfixedSum,
    ← Finset.sum_sub_distrib]
  apply localMaxIdeal_sum m hm
  intro coefficient hcoefficient
  obtain ⟨representative, _, hrepresentative⟩ := Finset.mem_image.mp hcoefficient
  have hcoefficientRing : coefficient ∈ BlocksLocalRing m := hrepresentative ▸ hvalues representative
  let fiberType := {point : points // values point = coefficient}
  let fiberAction : MulAction actingGroup fiberType := {
    smul actingElement point := ⟨actingElement • point.val,
      (hinvariant actingElement point.val).trans point.property⟩
    one_smul point := Subtype.ext (one_smul actingGroup point.val)
    mul_smul left right point := Subtype.ext (mul_smul left right point.val)
  }
  let : MulAction actingGroup fiberType := fiberAction
  let fixedEquiv : (MulAction.fixedPoints actingGroup fiberType) ≃
      {point : points // values point = coefficient ∧
        point ∈ MulAction.fixedPoints actingGroup points} := {
    toFun point := ⟨point.val.val, point.val.property, MulAction.mem_fixedPoints.mpr
      (fun actingElement => congrArg Subtype.val (MulAction.mem_fixedPoints.mp point.property actingElement))⟩
    invFun point := ⟨⟨point.val, point.property.1⟩, MulAction.mem_fixedPoints.mpr
      (fun actingElement => Subtype.ext (MulAction.mem_fixedPoints.mp point.property.2 actingElement))⟩
    left_inv point := rfl
    right_inv point := rfl
  }
  have hcard : Nat.card fiberType = (fiber coefficient).card := by
    simp only [fiberType, fiber, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfixedCard : Nat.card (MulAction.fixedPoints actingGroup fiberType) =
      (fixedFiber coefficient).card := by
    rw [Nat.card_congr fixedEquiv]
    simp only [fixedFiber, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcongruent := hpGroup.card_modEq_card_fixedPoints fiberType
  rw [hcard, hfixedCard] at hcongruent
  have hdifference := localMaxIdeal_natCard_difference m hm prime hprimeMem hcongruent
  convert localMaxIdeal_mul_localRing m hm hdifference hcoefficientRing using 1
  simp only [nsmul_eq_mul, sub_mul]

end CFSG.BrauerThirdMainTheorem.Helpers
