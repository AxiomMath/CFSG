module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentNarrowPerm
public import Certificates.Certificate31001
public import Certificates.Certificate31002
import CFSG.RankThree.Native.HSMcLSmall
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Schreier.RuIso

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.HardMathSupport.Dickson.I271

open CFSG.RankThree.Native in
theorem narrowGamma_eq_top_hs
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group)) (T : Sylow 5 K) :
    narrowGamma 5 (T : Subgroup K) = ⊤ := by
  obtain ⟨eK⟩ := hK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  obtain ⟨e, f, s₁, s₂, hs, heH, hfH, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate31001
  exact narrowGamma_eq_top_of_permPlane Nat.prime_five hs heH hfH he hf hef he1 hfe h₁ h₂
    (hs100Equiv.symm.trans (b.trans eK.symm)) T

open CFSG.Sporadic.RuSchreier in
theorem narrowGamma_eq_top_ru
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Ru).Group)) (T : Sylow 5 K) :
    narrowGamma 5 (T : Subgroup K) = ⊤ := by
  obtain ⟨eK⟩ := hK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  obtain ⟨e, f, s₁, s₂, hs, heH, hfH, he, hf, hef, he1, hfe, h₁, h₂⟩ :=
    Certificates.certificate31002
  exact narrowGamma_eq_top_of_permPlane Nat.prime_five hs heH hfH he hf hef he1 hfe h₁ h₂
    (ruEquivP.symm.trans (b.trans eK.symm)) T

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
