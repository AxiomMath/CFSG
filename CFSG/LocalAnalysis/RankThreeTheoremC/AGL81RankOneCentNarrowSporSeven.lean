module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowPerm
public import Certificates.Certificate31003
public import CFSG.Sporadic.Bridge.HeSurj
public import CFSG.Sporadic.HeldB.CertPBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.HardMathSupport.Dickson.I271

open CFSG.Sporadic.HeldB in
theorem narrowGamma_eq_top_he
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .He).Group)) (T : Sylow 7 K) :
    narrowGamma 7 (T : Subgroup K) = ⊤ := by
  obtain ⟨eK⟩ := hK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  obtain ⟨e, f, s₁, s₂, hs, heH, hfH, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate31003
  have hP : Subgroup.closure {CFSG.Monster.B.Co2.permOfArr 8330 (heGen 0),
      CFSG.Monster.B.Co2.permOfArr 8330 (heGen 1)} = heP := by
    rw [heP]
    rfl
  rw [hP] at hs heH hfH
  exact narrowGamma_eq_top_of_permPlane (by norm_num : (7 : ℕ).Prime) hs heH hfH he hf hef he1
    hfe h₁ h₂ (heEquivP.symm.trans (b.trans eK.symm)) T

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
