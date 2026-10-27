module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10CorIII
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma1111_of (hX : Asc82Step1111X) (hK : Asc82Step1111K) : Asc82Lemma1111 := by
  intro G _ _ t L S z K1 K2 T R hctx
  exact hK G t L S z K1 K2 T R hctx (hX G t L S z K1 K2 T R hctx)

theorem asc82Lemma1112_of (hTR : Asc82Step111TR) (h1111 : Asc82Lemma1111)
    (hP : Asc82StepPocketOfNormal) (hCor : Asc82CorIII) (h1011 : Asc82Lemma1011) :
    Asc82Lemma1112 := by
  intro G _ _ t L S z K1 K2 hctx
  have hnot : ¬ Hyp111 t S L := by
    intro hyp
    obtain ⟨T, R, hTR'⟩ := hTR G t L S z K1 K2 hctx hyp
    exact hCor G t L hctx.toSec3SettingLB z
      (hP G t L S z K1 K2 hctx (h1111 G t L S z K1 K2 T R hTR'))
  refine ⟨hnot, ?_⟩
  rcases h1011 G t L S z K1 K2 hctx with h | h
  · exact h.2.1.symm
  · exact (hnot h.1).elim

end CFSG.OddStandard.SmallF3.Omega
