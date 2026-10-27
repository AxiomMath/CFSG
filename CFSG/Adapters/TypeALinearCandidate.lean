module

public import CFSG.Adapters.SpecialLinearFrobenius
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.Adapters.ProjectiveSpecialLinear
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement

public section

noncomputable section

namespace CFSG.ClassicalModels

open Matrix TauCeti

theorem typeA_specialLinearSteinberg_eq_frobenius
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    (TypeALieIndex.ofA r q hv).specialLinearSteinberg =
      SpecialLinearGroup.map (n := Fin ((TypeALieIndex.ofA r q hv).1.rank + 1))
        (iterateFrobenius (TypeALieIndex.ofA r q hv).1.Closure
          (TypeALieIndex.ofA r q hv).1.characteristic
          (TypeALieIndex.ofA r q hv).1.fieldExponent) := by
  unfold TypeALieIndex.specialLinearSteinberg TypeALieIndex.specialLinearFrobenius
  rw [TypeALieIndex.specialLinearGraphAut_ofA]
  rfl

@[expose] def typeALinearEquivFixedPoints
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    SpecialLinearGroup (Fin ((TypeALieIndex.ofA r q hv).1.rank + 1))
      (GaloisField (TypeALieIndex.ofA r q hv).1.characteristic
        (TypeALieIndex.ofA r q hv).1.fieldExponent) ≃*
      (TypeALieIndex.ofA r q hv).FixedPoints := by
  let d := TypeALieIndex.ofA r q hv
  have hintertwine : d.carrierEquivSpecialLinear.toMonoidHom.comp d.steinberg =
      d.specialLinearSteinberg.comp d.carrierEquivSpecialLinear.toMonoidHom := by
    exact MonoidHom.ext fun g => d.carrierEquivSpecialLinear_steinberg g
  let e := TauCeti.fixedSubgroupCongr d.carrierEquivSpecialLinear hintertwine
  have hF := typeA_specialLinearSteinberg_eq_frobenius r q hv
  let eF : ↥(fixedSubgroup d.specialLinearSteinberg) ≃*
      fixedSubgroup (SpecialLinearGroup.map (n := Fin (d.1.rank + 1))
        (iterateFrobenius d.1.Closure d.1.characteristic d.1.fieldExponent)) :=
    MulEquiv.subgroupCongr (congrArg fixedSubgroup hF)
  exact (specialLinearEquivFrobeniusFixedPoints d.1 (Fin (d.1.rank + 1))).trans
    (eF.symm.trans e.symm)

theorem typeALinear_isPerfect
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    Group.IsPerfect (SpecialLinearGroup (Fin ((TypeALieIndex.ofA r q hv).1.rank + 1))
      (GaloisField (TypeALieIndex.ofA r q hv).1.characteristic
        (TypeALieIndex.ofA r q hv).1.fieldExponent)) := by
  have hrange := (LieTypeIndex.valid_iff _).mp hv |>.1
  rw [LieTypeIndex.inStandardRange_iff] at hrange
  have hrank : (TypeALieIndex.ofA r q hv).1.rank = r := by
    simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]
  rw [hrank]
  by_cases hr : r = 1
  · subst r
    apply specialLinear_isPerfect_two_of_four_le_card
    have hcard := GaloisField.card (TypeALieIndex.ofA 1 q hv).1.characteristic
      (TypeALieIndex.ofA 1 q hv).1.fieldExponent
      (TypeALieIndex.ofA 1 q hv).1.fieldExponent_pos.ne'
    rw [hcard, ← (TypeALieIndex.ofA 1 q hv).1.fieldOrder_eq_characteristic_pow]
    simpa only [ValidLieTypeIndex.fieldOrder, LieTypeIndex.fieldOrder_A] using hrange.2 rfl
  · exact specialLinear_isPerfect_of_three_le (by omega)

@[expose] def derivedCentralQuotientEquivCenterQuotient
    (G : Type*) [Group G] [Group.IsPerfect G] :
    TauCeti.DerivedCentralQuotient G ≃* (G ⧸ Subgroup.center G) := by
  let e : ↥(commutator G) ≃* G :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  exact QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

@[expose] def typeALinearCandidateEquivPSL
    (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    (TypeALieIndex.ofA r q hv).Group ≃*
      ProjectiveSpecialLinearGroup (Fin ((TypeALieIndex.ofA r q hv).1.rank + 1))
        (GaloisField (TypeALieIndex.ofA r q hv).1.characteristic
          (TypeALieIndex.ofA r q hv).1.fieldExponent) := by
  let _ := typeALinear_isPerfect r q hv
  exact (TauCeti.DerivedCentralQuotient.congr
    (typeALinearEquivFixedPoints r q hv).symm).trans
      (derivedCentralQuotientEquivCenterQuotient _)

end CFSG.ClassicalModels
