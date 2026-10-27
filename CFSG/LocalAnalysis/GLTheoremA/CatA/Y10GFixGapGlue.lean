module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldExcGap
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import TauCeti.GroupTheory.DerivedCentralQuotient
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GField

open CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

variable {R : Type} [Group R]

theorem ggFixSub_eq_fixSub (f : MulAut R) : ggFixSub f = FP.fixSub f := by
  ext x
  exact Iff.rfl

theorem ggFixDer_eq_of_subfieldGrp {f : MulAut R} {D : Subgroup R} (h : FR.SubfieldGrp f D)
    (hD : ⁅D, D⁆ = D) : ggFixDer f = D := by
  unfold ggFixDer
  rw [ggFixSub_eq_fixSub]
  refine le_antisymm h.2.1 ?_
  calc D = ⁅D, D⁆ := hD.symm
    _ ≤ ⁅FP.fixSub f, FP.fixSub f⁆ := Subgroup.commutator_mono h.1 h.1

theorem commutator_eq_self_of_mulEquiv {D : Subgroup R} {R' : Type} [Group R'] [IsSimpleGroup R']
    (hna : ∃ a b : R', a * b ≠ b * a) (e : ↥D ≃* R') : ⁅D, D⁆ = D := by
  haveI : Group.IsPerfect R' :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => by
      obtain ⟨a, b, hab⟩ := hna
      exact hab (isMulCommutative_iff.mp hc a b)
  haveI : Group.IsPerfect ↥D := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.commutator_eq_self

theorem nonempty_ggFixDer_equiv {f : MulAut R} {D : Subgroup R} (h : FR.SubfieldGrp f D)
    {R' : Type} [Group R'] [IsSimpleGroup R'] (hna : ∃ a b : R', a * b ≠ b * a) (e : ↥D ≃* R') :
    Nonempty (↥(ggFixDer f) ≃* R') := by
  rw [ggFixDer_eq_of_subfieldGrp h (commutator_eq_self_of_mulEquiv hna e)]
  exact ⟨e⟩

theorem isSolvable_ggFixSub_of_subfieldGrp {f : MulAut R} {D : Subgroup R} (h : FR.SubfieldGrp f D)
    (hD : Group.IsSolvable ↥D) : Group.IsSolvable ↥(ggFixSub f) := by
  rw [ggFixSub_eq_fixSub]
  set F := FP.fixSub f
  have h1 : Group.IsSolvable ↥(⁅F, F⁆ : Subgroup R) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion h.2.1)
      (Subgroup.inclusion_injective _)
  have e1 : ↥(commutator ↥F) ≃* ↥(⁅F, F⁆ : Subgroup R) :=
    ((commutator ↥F).equivMapOfInjective F.subtype F.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator F))
  haveI : Group.IsSolvable ↥(commutator ↥F) :=
    Group.isSolvable_of_isSolvable_injective (f := e1.toMonoidHom) e1.injective
  exact Group.isSolvable_commutator_iff.mp this

theorem innFree_of_ggRawInnField {p : ℕ} {I F : Set (MulAut R)} (h : GGRawInnField p R I F)
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) : FQ.InnFree p F := by
  obtain ⟨-, -, hconj, hF⟩ := h hs hna
  rintro f hf hord ⟨r, rfl⟩
  exact hF _ hf hord (hconj r)

theorem exists_mul_ne_of_isPerfect (G : Type*) [Group G] [Nontrivial G] [Group.IsPerfect G] :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative G (isMulCommutative_iff.mpr h)

theorem exists_mul_ne_of_equiv_centerQuot {G H : Type*} [Group G] [Group H] [Nontrivial G]
    (hH : Group.IsPerfect H) (e : G ≃* H ⧸ Subgroup.center H) : ∃ a b : G, a * b ≠ b * a := by
  haveI := hH
  haveI : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact exists_mul_ne_of_isPerfect G

end CFSG.LocalAnalysis.GLTheoremA.Y10GField

end
