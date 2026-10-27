module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Free
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterHolds
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transport

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic (IsU42Root)

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

noncomputable def quotientCenterEquivOfSimple {G : Type} [Group G] (hnab : ∃ x y : G, x * y ≠ y * x)
    [IsSimpleGroup G] : (G ⧸ center G) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2).trans
    QuotientGroup.quotientBot

theorem GomiU42Data.isComponent_fixed (h : GomiU42Data X J D E a) :
    haveI := h.normal
    CFSG.IsComponent ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))) :=
  h.isU42Root_conjNormal.isComponent

theorem GomiU42Data.subgroupOf_fixed_le (h : GomiU42Data X J D E a) :
    haveI := h.normal
    J.subgroupOf D ≤ fixedSubgroup (MulAut.conjNormal a : MulAut D) :=
  h.fixedRoot_conjNormal.2.1

noncomputable def GomiU42Data.fixedEquiv (h : GomiU42Data X J D E a) :
    haveI := h.normal
    ((J.subgroupOf D).subgroupOf (fixedSubgroup (MulAut.conjNormal a : MulAut D))) ≃* J :=
  haveI := h.normal
  (Subgroup.subgroupOfEquivOfLe h.subgroupOf_fixed_le).trans
    (Subgroup.subgroupOfEquivOfLe h.lt.le)

theorem GomiU42Data.lieModel_fixed (h : GomiU42Data X J D E a) :
    haveI := h.normal
    CFSG.Blueprint.LieModel ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))) .PSU 4 2 1 :=
  lieModel_of_mulEquiv_classical h.fixedEquiv (by decide) h.lieModel

theorem GomiU42Data.lieModel_fixed_quotient (h : GomiU42Data X J D E a) :
    haveI := h.normal
    CFSG.Blueprint.LieModel (((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))) ⧸ center ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D)))) .PSU 4 2 1 := by
  haveI := h.normal
  haveI := h.isSimpleGroup_J
  haveI : IsSimpleGroup ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))) :=
    h.fixedEquiv.isSimpleGroup
  have hnab : ∃ x y : ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := h.nonabelian_J
    refine ⟨h.fixedEquiv.symm x, h.fixedEquiv.symm y, fun h' => hxy ?_⟩
    have h'' := congrArg h.fixedEquiv h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  exact lieModel_of_mulEquiv_classical (quotientCenterEquivOfSimple hnab) (by decide)
    h.lieModel_fixed

theorem GomiU42Data.fixedCentralizerTwoFree (h : GomiU42Data X J D E a) (ha : a ∉ D) :
    haveI := h.normal
    FixedCentralizerTwoFree (MulAut.conjNormal a : MulAut D) ((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D))) := by
  haveI := h.normal
  intro U _ hUC hUF
  have hfix := h.eqLocus_eq ha
  haveI := h.isSimpleGroup_J
  have hJ' : IsSimpleGroup (J.subgroupOf D) :=
    (Subgroup.subgroupOfEquivOfLe h.lt.le).isSimpleGroup
  have hnab : ∃ x y : J.subgroupOf D, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := h.nonabelian_J
    refine ⟨(Subgroup.subgroupOfEquivOfLe h.lt.le).symm x, (Subgroup.subgroupOfEquivOfLe h.lt.le).symm y,
      fun h' => hxy ?_⟩
    have h'' := congrArg (Subgroup.subgroupOfEquivOfLe h.lt.le) h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  have hz := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  rw [eq_bot_iff]
  intro u hu
  have huJ : u ∈ J.subgroupOf D := by
    have := hUF hu
    rw [show fixedSubgroup (MulAut.conjNormal a : MulAut D) = J.subgroupOf D from hfix] at this
    exact this
  have hcomm : ∀ y ∈ J.subgroupOf D, y * u = u * y := by
    intro y hy
    have hy' : y ∈ ((((J.subgroupOf D).subgroupOf
      (fixedSubgroup (MulAut.conjNormal a : MulAut D)))).map
      (fixedSubgroup (MulAut.conjNormal a : MulAut D)).subtype : Subgroup D) := by
      have hyF : y ∈ fixedSubgroup (MulAut.conjNormal a : MulAut D) := h.subgroupOf_fixed_le hy
      exact ⟨⟨y, hyF⟩, hy, rfl⟩
    exact (mem_centralizer_iff.1 (hUC hu) y hy').symm ▸ rfl
  have hmem : (⟨u, huJ⟩ : J.subgroupOf D) ∈ center (J.subgroupOf D) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcomm y y.2)
  rw [hz, mem_bot] at hmem
  have : u = 1 := congrArg Subtype.val hmem
  rw [this]
  exact one_mem _

theorem gomiU42Selector_alternating :
    GomiU42Selector fun D _ => ∃ m : ℕ, 5 ≤ m ∧ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  intro X _ _ J D E a h halt
  haveI := h.normal
  exact (catSUmAlternating D h.simple h.nonabelian halt (MulAut.conjNormal a)
    h.fixedRoot_conjNormal.1 4 1 _ (by norm_num) h.isComponent_fixed
    h.lieModel_fixed_quotient).elim

theorem gomiU42Selector_even :
    GomiU42Selector fun D _ => CFSG.Blueprint.EvenLieType D := by
  intro X _ _ J D E a h hEven
  haveI := h.normal
  obtain ⟨hα, -, -, hinner⟩ := h.fixedRoot_conjNormal
  by_cases ha : a ∈ D
  · exact (catSUmEvenInner D h.simple h.nonabelian hEven (MulAut.conjNormal a) hα (hinner.1 ha)
      4 1 _ h.isComponent_fixed h.lieModel_fixed_quotient).elim
  · refine ⟨ha, ?_⟩
    have hout : (MulAut.conjNormal a : MulAut D) ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner D :=
      fun hin => ha (hinner.2 hin)
    exact catSUmEvenOuterAt (m := 4) (by norm_num) D h.simple h.nonabelian hEven
      (MulAut.conjNormal a) hα hout 1 _ h.isComponent_fixed h.lieModel_fixed_quotient
      (h.fixedCentralizerTwoFree ha)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
