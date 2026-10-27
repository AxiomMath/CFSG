
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
public import Certificates.Certificate2329
public import Certificates.Certificate2329Base

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem hfSylow_check :
    (∀ j < 9, (hfC1Tabs[j]!).size = 8330) ∧ heT1Arr.size = 8330 ∧ hfXTab.size = 8330 ∧
      lettersOK 3 hfXWord = true ∧
      (∀ i < 4, ∀ j ∈ hfTauWords.getD i [], j < 9) ∧ (∀ j ∈ hfYWord, j < 10) ∧
      (∀ i < 6, ∀ j ∈ hfEWords.getD i [], j < 5) ∧
      siftA 8330 (rawLevels 8330 heStrongArrs heBase.toArray) heBase.toArray 0 hfYTab = false ∧
      enumOK 8330 hfT0Tabs hfT0Enum = true ∧ hfT0Enum.tabs.size = 2048 ∧
      (∀ j < 6, ∀ x ∈ hfDelta32, (hfT0Tabs[j]!)[x]! ∈ hfDelta32) ∧
      (List.range 8330).countP (fun i => hfEATab[i]! == i) = 346 :=
  Certificates.certificate2329.1

theorem hfDelta32_check :
    hfDelta32.length = 32 ∧ (∀ x ∈ hfDelta32, x < 8330) ∧ hfDelta32.Nodup :=
  Certificates.certificate2329.2.1

theorem hfSylow_check32 :
    enumOK 32 hfTTabs32 hfTEnum32 = true ∧ hfTEnum32.tabs.size = 1024 ∧
      enumOK 32 hfT0Tabs32 hfT0Enum32 = true ∧ hfT0Enum32.tabs.size = 2048 ∧
      (hfTEnum32.tabs.toList.filter (commAll 32 hfTTabs32)).length = 2 ∧
      enumOK 32 hfETabs32 hfEEnum32 = true ∧ hfEEnum32.tabs.size = 64 ∧
      (∀ i < 6, ∀ j < 6, comp 32 hfETabs32[i]! hfETabs32[j]! =
        comp 32 hfETabs32[j]! hfETabs32[i]!) ∧
      (∀ i < 6, comp 32 hfETabs32[i]! hfETabs32[i]! = idTab 32) ∧
      normalOK 32 hfEEnum32.tabs hfTTabs32 (hfTTabs32.map (invTab 32)) hfETabs32 = true ∧
      hfOuterE8Check 32 hfTEnum32.tabs hfT0Enum32.tabs = true :=
  Certificates.certificate2329.2.2

end CFSG.ComponentClassification.GrSLit.HeldFix
