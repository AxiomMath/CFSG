module

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GTriPiece
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrth
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExc
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F
  (HasLabel hasLabel_centerQuot center_centerQuot_eq_bot centerQuotAut)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FieldKind TriPiece)

section OutHolds

theorem exists_label_of_hasLabel {X : Type} [Group X] {P : GLALabel → Prop} (h : HasLabel X P) :
    ∃ lab : GLALabel, P lab ∧ HasLabel X (fun l : GLALabel => l = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

theorem triPiece_holds : TriPiece :=
  CFSG.LocalAnalysis.GLTheoremA.Y10GField.triPiece_of_innDiag
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.innDiagOrth_holds
    CFSG.LocalAnalysis.GLTheoremA.Y10GField.innDiagExc_holds

end OutHolds

end CFSG.LocalAnalysis.GLTheoremA.K144
