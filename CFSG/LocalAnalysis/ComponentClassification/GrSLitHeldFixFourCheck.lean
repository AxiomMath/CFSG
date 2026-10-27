module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public import CFSG.Sporadic.HeldB.CertPFieldsData
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public meta import CFSG.Sporadic.HeldB.CertPFieldsData
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixFourCheckInputs
public import Certificates.Certificate2327

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem hfFour_check :
    lettersOK 2 hfKWord = true ∧ hfKTab.size = 8330 ∧
      isInvA 8330 hfKTab (invCand 8330 hfKTab) = true ∧ hfKTab[0]! = 7750 ∧
      (∀ i < 2, ∀ j ∈ hfB1Words.getD i [], j < 5) ∧ (∀ j ∈ hfE2Word, j < 5) ∧
      comp 8330 hfB1Tabs[0]! hfB1Tabs[0]! = idTab 8330 ∧
      comp 8330 hfB1Tabs[1]! hfB1Tabs[1]! = idTab 8330 ∧
      comp 8330 hfB1Tabs[0]! hfB1Tabs[1]! = comp 8330 hfB1Tabs[1]! hfB1Tabs[0]! ∧
      hfB1Tabs[0]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ idTab 8330 ∧ hfB1Tabs[1]! ≠ hfB1Tabs[0]! ∧
      (∀ j < 9, isInvA 8330 (heStrong j) (invCand 8330 (heStrong j)) = true) ∧
      (∀ j < 9, (heStrong j)[0]! = 0 → j ∈ heStabIdx) ∧
      (∀ j ∈ heStabIdx, j < 9 ∧ ∀ i < 2,
        comp 8330 (comp 8330 (hfConjK (heStrong j)) hfB1Tabs[i]!)
          (hfConjK (invCand 8330 (heStrong j))) ∈ hfB1Elems) ∧
      comp 8330 hfE2Tab hfE2Tab = idTab 8330 ∧ hfE2Tab ≠ idTab 8330 ∧ hfE2Tab ≠ heT1Arr ∧
      (∀ g < 5, isInvA 8330 hfTTabs[g]! (invCand 8330 hfTTabs[g]!) = true ∧
        comp 8330 (comp 8330 hfTTabs[g]! hfE2Tab) (invCand 8330 hfTTabs[g]!) ∈
          [hfE2Tab, comp 8330 hfE2Tab heT1Arr]) ∧
      hfPointTreeOK 8330 hfOrbGens 7750 hfOrbTree.1 hfOrbTree.2.1 hfOrbTree.2.2
        (hfPositions 8330 hfOrbTree.1) = true :=
  Certificates.certificate2327

end CFSG.ComponentClassification.GrSLit.HeldFix
