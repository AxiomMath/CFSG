module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.NotZ2A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest9
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma69Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma610
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Rest13
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CII2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI13
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64e
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E611Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Sound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Final4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HPi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem fin76bInnerRest₁₃_holds :
    Fin76bInnerRest₁₃ := by
  intro G _ _ L z t T₀ E Q x β B S hH hBD hWr _ _
  obtain ⟨α, hα⟩ := hH.exists_alpha
  have hF611 : EFacts611 E t := fin76bEFacts611 G L z t T₀ E Q x β B hH.conf
  have hF613 : EFacts613 E t := fin76bEFacts613 G L z t T₀ E Q x β B hH.conf
  let c : I13Ctx L z t T₀ E Q x β B S α := ⟨hH, hα, hF611, hWr, hBD⟩
  obtain ⟨π, hπ, c1, c2, c3⟩ := hF613.exists_pi
  rcases c.rho_range_dichotomy hπ with hI | hII
  · exact c.caseI_false hπ hI (fun φ hφ => (c1 φ hφ).1)
      (fun {b₁ b₂} hb₁ hb₂ h11 h22 h12 h1 h2 h3 {q b} hq hb hx2 =>
        c.exists_E64 hF613 hb₁ hb₂ h11 h22 h12 h1 h2 h3 hq hb hx2)
      (fun {u} hu {A} hA hA2 => rank_cent_conj_le hH hu hA hA2)
  · exact c.caseII_false ⟨hπ, fun φ₁ φ₂ h₁ h₂ h12 h12' hnin =>
      ⟨(c3 φ₁ φ₂ h₁ h₂ h12 h12' hnin).2.2.1, (c3 φ₁ φ₂ h₁ h₂ h12 h12' hnin).2.2.2⟩, hII⟩

end CFSG.EvenSporadicStandard.Fin76b
