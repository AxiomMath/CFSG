module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.Y10GField

private theorem famExc_of_ggLabelIso {lab lab' : GLALabel} (h : GGLabelIso lab lab')
    (hE : FamExc lab') : FamExc lab := by
  unfold FamExc at hE
  rcases h with hEq | hBC | hDA | hAD | hD3A3 | hA3D3 | hD2A1 | hA1D2
  · rw [hEq]; exact hE
  · exfalso
    obtain ⟨-, hB', -, -⟩ := hBC
    rcases hB' with h | h <;> rw [h] at hE <;> simp at hE
  · exfalso
    obtain ⟨-, h2⟩ := hDA
    rw [h2] at hE
    simp at hE
  · exfalso
    obtain ⟨-, h2⟩ := hAD
    rw [h2] at hE
    simp at hE
  · exfalso
    obtain ⟨-, h2⟩ := hD3A3
    rw [h2] at hE
    simp at hE
  · exfalso
    obtain ⟨-, h2⟩ := hA3D3
    rw [h2] at hE
    simp at hE
  · exfalso
    obtain ⟨-, h2⟩ := hD2A1
    rw [h2] at hE
    simp at hE
  · exfalso
    obtain ⟨h1, -⟩ := hA1D2
    rw [h1] at hE
    simp at hE

theorem k1419ClsExcOut_of_rigid (hR : CFSG.StandardType.GGLabelRigidInput)
    (hC : K1419ClsClassLabelFact) : K1419ClsExcOutFact := by
  intro X _ labK hQ hlabK hcat
  obtain ⟨lab, hlab, hnexc⟩ := hC X hQ hcat
  obtain ⟨hlam, -, hGlab⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlab
  obtain ⟨hlamK, -, hGlabK⟩ := Y10GInnLin.ggHasLabel_of_hasLabel hlabK
  exact fun hE =>
    hnexc (famExc_of_ggLabelIso (hR lab labK (X ⧸ Subgroup.center X) hlam hlamK hGlab hGlabK) hE)

end CFSG.LocalAnalysis.GLTheoremA.K1419
