module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SeitzRest5

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5

open CFSG.LieType.SeitzGeneration

section Even


theorem twE6ThreeOpenDiagEven_holds : TwE6ThreeOpenDiagEven :=
  Inputs2311c.UniSeitzPlanes.mono (fun d p E h => by
    obtain ⟨⟨hp3, ⟨q, hq, -, hq2⟩, hout, hdiag, hnpar⟩, -⟩ := h
    obtain ⟨q', hq', hdiag'⟩ := hdiag
    rw [hq] at hq'
    cases hq'
    exact ⟨hout, hp3, ⟨q, hq, hq2, hdiag'⟩, hnpar⟩)
    Inputs2311g.uniSeitzPlanes_twE6_diag

end Even

section Cover


theorem twE6ThreeOpenDiag_holds : QuasiHigh5E6Cover.TwE6ThreeOpenDiag :=
  twE6ThreeOpenDiag_of_even twE6ThreeOpenDiagEven_holds

end Cover

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SeitzRest5

end
