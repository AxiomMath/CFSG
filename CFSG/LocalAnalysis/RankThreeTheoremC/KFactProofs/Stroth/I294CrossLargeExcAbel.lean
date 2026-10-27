module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcG2
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcF4
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcD4
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossTits
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossSuzuki
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (CrossSylowAbelianAt)

theorem i294CrossLargePrimeOn_of_crossSylowAbelianAt {φ : TauCeti.LieTypeIndex → Prop}
    (h : ∀ d : TauCeti.ValidLieTypeIndex, φ d.1 → CrossSylowAbelianAt d) :
    I294CrossLargePrimeOn φ := by
  intro p hp h5 L _ _ hs _ d hφ hd e _ ⟨S, hS⟩
  exact (hS (h d hφ p hp h5 hd L hs e S)).elim

@[expose] def I294CrossLargeIsReeG2 : TauCeti.LieTypeIndex → Prop
  | .reeG2 _ => True
  | _ => False

@[expose] def I294CrossLargeIsTriality : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def I294CrossLargeIsF4 : TauCeti.LieTypeIndex → Prop
  | .F4 _ => True
  | _ => False

@[expose] def I294CrossLargeIsSz : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | _ => False

section G2


theorem i294CrossLargePrimeOn_G2 : I294CrossLargePrimeOn I294CrossIsG2 := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | G2 q => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_G2 hv
  | _ => exact (hφ : False).elim

theorem i294CrossLargePrimeOn_reeG2 : I294CrossLargePrimeOn I294CrossLargeIsReeG2 := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | reeG2 m => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_reeG2 hv
  | _ => exact (hφ : False).elim

end G2

section F4


theorem i294CrossLargePrimeOn_F4 : I294CrossLargePrimeOn I294CrossLargeIsF4 := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | F4 q => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_F4 hv
  | _ => exact (hφ : False).elim

theorem i294CrossLargePrimeOn_reeF4 : I294CrossLargePrimeOn I294CrossIsReeF4 := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | reeF4 m => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_reeF4 hv
  | _ => exact (hφ : False).elim

end F4

section D4


theorem i294CrossLargePrimeOn_triality : I294CrossLargePrimeOn I294CrossLargeIsTriality := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | trialityD4 q => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_trialityD4 hv
  | _ => exact (hφ : False).elim

end D4

section Tits


theorem i294CrossLargePrimeOn_tits : I294CrossLargePrimeOn I294CrossIsTits := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | tits => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_tits hv
  | _ => exact (hφ : False).elim

end Tits

section Suzuki


theorem i294CrossLargePrimeOn_sz : I294CrossLargePrimeOn I294CrossLargeIsSz := by
  refine i294CrossLargePrimeOn_of_crossSylowAbelianAt ?_
  rintro ⟨i, hv⟩ hφ
  cases i with
  | suzuki m => exact CFSG.LocalAnalysis.RankFourTheoremC.crossSylowAbelianAt_suzuki hv
  | _ => exact (hφ : False).elim

end Suzuki

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
