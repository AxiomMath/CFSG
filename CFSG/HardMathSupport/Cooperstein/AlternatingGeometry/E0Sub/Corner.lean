module

public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Main
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClCaseI

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open CFSG.Quasithin


theorem e0NonShortNotCaseIStatement_holds
    : E0NonShortNotCaseIStatement := by
  intro G _ _ X S L hA hL hSL N hN θ hNS hθS _hEO _hJ Δ₀ hΔ₀ P hPc hPsq hPfix hPtrans ω hωω hωΔ
    hωfree hθ _hyc hshort _hc
  obtain ⟨L₁, -, -, -, hMS, hcomp, hprod, hcard, hnot⟩ :=
    e0SubConfigStatement_holds G X S L hA hL hSL N (by omega) θ hNS hθS Δ₀ hΔ₀ P hPc hPsq hPfix
      hPtrans ω hωω hωΔ hωfree hθ hshort
  rcases MS93.MRes.asC132NoSp4_holds.of_not_dvd hMS hcomp hprod (by rw [hcard]; decide) with
    h | h | h | h | h
  · exact hnot h.1
  · exact hnot h.1
  · exact hnot h.1
  · exact hnot h.1
  · exact notSL3Statement_holds G L₁ hcard h

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
