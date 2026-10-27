module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowCentGen
public import CFSG.Sporadic.Bridge.M12
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import Certificates.Certificate31011
public import Certificates.Certificate31012

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.HardMathSupport.Dickson.I271

section M12

open CFSG.Blueprint CFSG.Sporadic.Bridge.M12

theorem narrowGamma_eq_top_m12 {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .M12).Group)) (T : Sylow 3 K) :
    narrowGamma 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨eK⟩ := hK
  obtain ⟨eB⟩ := nonempty_mulEquiv
  obtain ⟨e, f, s₁, s₂, hs, heH, hfH, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate31011
  exact narrowGamma_eq_top_of_permPlane Nat.prime_three hs heH hfH he hf hef he1 hfe h₁ h₂
    (eB.trans eK.symm) T

end M12

section Tits

open CFSG.Sporadic.Schreier.Tits

theorem narrowGamma_eq_top_tits
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits)
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (T : Sylow 3 K) : narrowGamma 3 (T : Subgroup K) = ⊤ := by
  obtain ⟨d1, hv⟩ := d
  change d1 = _ at hd
  subst hd
  obtain ⟨eK⟩ := hK
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.nonempty_mulEquiv_titsD_cat hv
  obtain ⟨x, y, s₁, s₂, hs, hxH, hyH, hx, hy, hzx, hzy, hzxk, hzyk, h₁, h₂⟩ :=
    Certificates.certificate31012
  exact narrowGamma_eq_top_of_permHPFacts Nat.prime_three (by decide) hs hxH hyH hx hy hzx hzy
    hzxk hzyk h₁ h₂ (eC.symm.trans eK.symm) T

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
