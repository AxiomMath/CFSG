module

public import CFSG.GF2Type.SmithTypeE.DMod.Act
public import CFSG.GF2Type.SmithTypeE.DMod.Clifford
public import Certificates.Data.Kernel.SmithD6.WtCheck
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Data.SmithD6Check
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6 CFSG.KD.SmithD6

theorem gensV_codes : ∀ g < 13,
    (gensV.getD g (0, 0)).1 < 4096 ∧ (gensV.getD g (0, 0)).2 < 4096 ∧
      (gensV.getD g (0, 0)).1 ≠ 0 ∧ (gensV.getD g (0, 0)).2 ≠ 0 ∧
        qf (gensV.getD g (0, 0)).1 = false ∧ qf (gensV.getD g (0, 0)).2 = false ∧
          (gensV.getD g (0, 0)).1 ≠ (gensV.getD g (0, 0)).2 ∧
            bf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2 = false := by
  decide +kernel

theorem lineOf_gensV {g : ℕ} (hg : g < 13) :
    lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2 < 365211 ∧
      lineSet (lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2) =
        lineOfPair (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2) := by
  obtain ⟨hx, hy, hx0, hy0, hqx, hqy, hxy, hb⟩ := gensV_codes g hg
  exact lineSet_lineIdx3 hx hy hx0 hy0 hqx hqy hxy hb

theorem tlift_lineOf_gensV {g : ℕ} (hg : g < 13) :
    tlift (dec12 (linePair (lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2)).1)
        (dec12 (linePair (lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2)).2) =
      tlift (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2) := by
  obtain ⟨hx, hy, -, -, hqx, hqy, hxy, hb⟩ := gensV_codes g hg
  obtain ⟨hk, e⟩ := lineOf_gensV hg
  exact tlift_eq_of_line_eq (tsPair_linePair hk) (tsPair_dec12 hqx hqy hb) (linePair_ne hk).2.2
    (fun h => hxy (eq_of_dec12_eq hx hy h)) e

theorem siegelK_lineOf_gensV {g : ℕ} (hg : g < 13) :
    siegelK (lineOf (gensV.getD g (0, 0)).1 (gensV.getD g (0, 0)).2) =
      siegelEquiv (dec12 (gensV.getD g (0, 0)).1) (dec12 (gensV.getD g (0, 0)).2) := by
  obtain ⟨hx, hy, hx0, hy0, hqx, hqy, hxy, hb⟩ := gensV_codes g hg
  obtain ⟨hk, e⟩ := lineOf_gensV hg
  obtain ⟨hu, hw, huw⟩ := linePair_ne hk
  exact siegelEquiv_eq_of_lineOfPair_eq (tsPair_linePair hk) (tsPair_dec12 hqx hqy hb) hu hw huw
    (dec12_ne_zero hx hx0) (dec12_ne_zero hy hy0) (fun h => hxy (eq_of_dec12_eq hx hy h)) e

end CFSG.GF2Type.SmithTypeE.DMod

end
