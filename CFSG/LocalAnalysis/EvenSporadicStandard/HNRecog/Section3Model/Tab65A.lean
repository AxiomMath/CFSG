module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Spec
public import Certificates.Certificate441706

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Cert


theorem tab6_5A_b (hP : Nat.card ↥P1408 = 177408000) :
    ∃ s ∈ Gx (pA * pZ) ⊓ Gx (tab6C 5), IsConj pB s := by
  have h := Certificates.certificate441706
  simp only [tab65AOK, Bool.and_eq_true] at h
  obtain ⟨⟨hg, hw⟩, hc⟩ := h
  have hmem := (Certificates.certificate441694 hP).mem5A
  have hAZ : wordP wordAZ = pA * pZ := Subtype.ext elemW_wordAZ
  rw [hAZ] at hmem
  exact ⟨wordP tab65AWord, hmem, isConj_of_conjEqOK hg (rep_elemB) (rep_elemW_of_gensOK hg hw) hc⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
