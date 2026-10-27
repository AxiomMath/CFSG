module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionReeF4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionTriality

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open TauCeti InnerFusion

section Main


theorem innerFusionE9Exc_holds : InnerFusionE9Exc := by
  refine innerFusionE9Exc_of_at fun d hch hd => ?_
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | G2 q => exact innerFusionE9At_G2 q hv (by simpa [LieTypeIndex.characteristic_G2] using hch)
  | trialityD4 q =>
    exact innerFusionE9At_trialityD4 q hv
      (by simpa [LieTypeIndex.characteristic_trialityD4] using hch)
  | reeF4 m => exact innerFusionE9At_reeF4 m hv
  | A r q => exact hd.elim
  | twistedA r q => exact hd.elim
  | B r q => exact hd.elim
  | C r q => exact hd.elim
  | D r q => exact hd.elim
  | twistedD r q => exact hd.elim
  | E6 q => exact hd.elim
  | E7 q => exact hd.elim
  | E8 q => exact hd.elim
  | F4 q => exact hd.elim
  | twistedE6 q => exact hd.elim
  | suzuki k => exact hd.elim
  | reeG2 k => exact hd.elim
  | tits => exact hd.elim

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott
