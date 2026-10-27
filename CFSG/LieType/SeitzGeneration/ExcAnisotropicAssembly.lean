module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicG2
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicTriality
public import CFSG.LieType.SeitzGeneration.ExcAnisotropicReeF4
public import CFSG.LieType.SeitzGeneration.ExcF4Two
public import CFSG.LieType.SeitzGeneration.ExcVacuousSuzuki
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.RankThree.PartOne.SEITZ6.G2MaxDone

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.RankThree.PartOne TauCeti

@[expose] def SeitzExcAnisotropicG2ThreeMinus : Prop :=
  SeitzExcAnisotropicForAt IsG2Index fun d p =>
    p = 3 ∧ ∃ q : PrimePower, d = .G2 q ∧ ¬ 3 ∣ q.card + 1

structure SeitzExcAnisotropicResiduals : Prop where
  g2NineFive : SeitzExcAnisotropicG2NineFive
  g2Three : SeitzExcAnisotropicG2ThreeMinus
  trialityOdd : SeitzExcAnisotropicTrialityOdd
  trialityThree : SeitzExcAnisotropicTrialityThree
  f4Big : SeitzExcAnisotropicF4Big
  f4Three : SeitzExcAnisotropicF4Three
  e6 : SeitzExcAnisotropicE6
  twistedE6 : SeitzExcAnisotropicTwistedE6
  e7 : SeitzExcAnisotropicE7
  e8 : SeitzExcAnisotropicE8
  reeG2 : SeitzExcAnisotropicReeG2
  reeF4Three : SeitzExcAnisotropicReeF4Three

section Assembly

theorem seitzExcAnisotropicG2_notThreePlus (h9 : SeitzExcAnisotropicG2NineFive)
    (h3 : SeitzExcAnisotropicG2ThreeMinus) :
    SeitzPlanes fun d p E =>
      (InnerPlane d p E ∧ IsG2Index d.1 ∧ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E) ∧
        ¬ (p = 3 ∧ ∃ q : PrimePower, d.1 = .G2 q ∧ 3 ∣ q.card + 1) := by
  intro d p hp hp2 hpd hex E hE hc ⟨⟨hin, hG, hr, hn⟩, hnot⟩
  rcases PrimeRange.eq_three_or_five_le hp hp2 with h3p | h5
  · obtain ⟨q, hq⟩ := hG
    exact h3 d p hp hp2 hpd hex E hE hc
      ⟨hin, ⟨q, hq⟩, ⟨h3p, q, hq, fun hdiv => hnot ⟨h3p, q, hq, hdiv⟩⟩, hr, hn⟩
  · exact seitzExcAnisotropicForAt_G2_geFive (SEITZ6.maxSL2SL2G2_of_top
      CFSG.Goldschmidt.topStatement) h9 d p hp hp2 hpd
      hex E hE hc ⟨hin, hG, h5, hr, hn⟩

theorem seitzExcAnisotropicNotG2ThreePlus_of_residuals (h : SeitzExcAnisotropicResiduals) :
    SeitzExcAnisotropicNotG2ThreePlus := by
  intro d p hp hp2 hpd hex E hE hc ⟨⟨hin, hnc, hr, hn⟩, hnot⟩
  rcases (not_isClassicalIndex_iff d.1).mp hnc with
    ((hd | hd | hd | hd | hd) | (hd | hd)) | (hd | hd | hd | hd)
  · exact seitzExcAnisotropicG2_notThreePlus h.g2NineFive h.g2Three d p hp hp2 hpd hex E hE hc
      ⟨⟨hin, hd, hr, hn⟩, hnot⟩
  · exact seitzExcAnisotropicFor_F4_of_residuals h.f4Big h.f4Three d p hp hp2 hpd hex E hE hc
      ⟨hin, hd, hr, hn⟩
  · exact h.e6 d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact h.e7 d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact h.e8 d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact seitzExcAnisotropicFor_triality_of_residuals CFSG.Goldschmidt.topStatement
      h.trialityOdd h.trialityThree d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact h.twistedE6 d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact seitzExcAnisotropicFor_suzuki d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact h.reeG2 d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩
  · exact seitzExcAnisotropicFor_reeF4_of_three h.reeF4Three d p hp hp2 hpd hex E hE hc
      ⟨hin, hd, hr, hn⟩
  · exact seitzExcAnisotropicFor_tits d p hp hp2 hpd hex E hE hc ⟨hin, hd, hr, hn⟩

end Assembly

end CFSG.LieType.SeitzGeneration
