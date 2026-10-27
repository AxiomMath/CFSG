module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatEvenBenderOuter
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenInner
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace CatEvenBender

theorem isComponent_of_fixedRootDatumOf {T : StdType} {D : Type} [Group D] {n : ℕ}
    {α : MulAut D} {S : Subgroup D} (d : FixedRootDatumOf T D n α S) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) :
    IsComponent (S.subgroupOf (fixedSubgroup α)) ∧
      Nonempty (S.subgroupOf (fixedSubgroup α) ⧸ center (S.subgroupOf (fixedSubgroup α)) ≃* S) := by
  let eD : S.subgroupOf (fixedSubgroup α) ≃* S := subgroupOfEquivOfLe d.le_fixed
  have : IsSimpleGroup (S.subgroupOf (fixedSubgroup α)) := eD.isSimpleGroup
  have hnab : ∃ x y : S.subgroupOf (fixedSubgroup α), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hSnab
    refine ⟨eD.symm a, eD.symm b, fun h => hab ?_⟩
    have h1 := congrArg eD h
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  exact ⟨⟨hq, d.normal.isSubnormal⟩,
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eD⟩⟩

theorem not_mem_range_of_fixedRootDatumOf
    {T : StdType} {D : Type} [Group D] (hDs : IsSimpleGroup D) (heven : EvenLieType D) {n : ℕ}
    {α : MulAut D} {S : Subgroup D} (d : FixedRootDatumOf T D n α S) (hSs : IsSimpleGroup S)
    (hSnab : ∃ a b : S, a * b ≠ b * a) : α ∉ (MulAut.conj : D →* MulAut D).range := by
  intro hin
  have hnab : ∃ x y : D, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨a, b, fun h => hab (Subtype.ext h)⟩
  exact SeitzReduction.F4Pilot.false_of_isComponent_fixedSubgroup_inner hnab
    (ComponentClassification.CatLeaf.involutionCentralizersComponentFree_of_evenLieType heven)
    d.orderOf_eq hin (isComponent_of_fixedRootDatumOf d hSs hSnab).1

end CatEvenBender

open CatEvenBender

section Selector


theorem fixedRootSelectorOf_evenLieType_U3 :
    FixedRootSelectorOf T_U3 SurvU3 fun D _ => EvenLieType D := by
  intro D _ _ hDs heven n α S d
  have hS : LieModel S .PSU 3 2 n := d.type.2
  have hSs := isSimpleGroup_of_lieModel_PSU3 hS
  have hSnab := exists_mul_ne_of_lieModel_PSU3 hS
  have hout := not_mem_range_of_fixedRootDatumOf hDs heven d hSs hSnab
  obtain ⟨hD', ⟨eQ⟩⟩ := isComponent_of_fixedRootDatumOf d hSs hSnab
  obtain ⟨a, b, hab⟩ := hSnab
  exact ⟨catSU3EvenOuterList n D hDs ⟨a, b, fun h => hab (Subtype.ext h)⟩ heven α d.orderOf_eq
    hout _ hD' (LieType.CurtisTits.lieModel_of_mulEquiv eQ.symm hS), hout⟩

theorem fixedRootSelectorOf_evenLieType_Sz :
    FixedRootSelectorOf T_Sz SurvSz fun D _ => EvenLieType D := by
  intro D _ _ hDs heven n α S d
  have hS : LieModel S .twistedB2 0 2 n := d.type
  have hSs := isSimpleGroup_of_lieModel_twistedB2 hS
  have hSnab := exists_mul_ne_of_lieModel_twistedB2 hS
  have hout := not_mem_range_of_fixedRootDatumOf hDs heven d hSs hSnab
  obtain ⟨hD', ⟨eQ⟩⟩ := isComponent_of_fixedRootDatumOf d hSs hSnab
  obtain ⟨a, b, hab⟩ := hSnab
  exact ⟨catSzEvenOuterList n D hDs ⟨a, b, fun h => hab (Subtype.ext h)⟩ heven α d.orderOf_eq
    hout _ hD' (LieType.CurtisTits.lieModel_of_mulEquiv eQ.symm hS), hout⟩

end Selector

end CFSG.LocalAnalysis.EvenBN.GMSK
