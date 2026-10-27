module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossFamilies

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

@[expose] def I294CrossIsSz : TauCeti.LieTypeIndex → Prop
  | .suzuki _ => True
  | _ => False

@[expose] def I294CrossIsTriality : TauCeti.LieTypeIndex → Prop
  | .trialityD4 _ => True
  | _ => False

@[expose] def I294CrossIsReeG2 : TauCeti.LieTypeIndex → Prop
  | .reeG2 _ => True
  | _ => False

@[expose] def I294CrossIsExcBig : TauCeti.LieTypeIndex → Prop
  | .F4 _ => True
  | .E6 _ => True
  | .twistedE6 _ => True
  | .E7 _ => True
  | .E8 _ => True
  | _ => False

@[expose] def I294CrossThreeRankTwoSz : Prop := I294CrossThreeRankTwoOn I294CrossIsSz

@[expose] def I294CrossThreeRankTwoTriality : Prop := I294CrossThreeRankTwoOn I294CrossIsTriality

@[expose] def I294CrossThreeRankTwoExc : Prop := I294CrossThreeRankTwoOn I294CrossIsExcBig

@[expose] def I294CrossThreeRankTwoClassical : Prop :=
  I294CrossThreeRankTwoOn I294CrossIsClassical

theorem i294CrossThreeRankTwoOn_reeG2 : I294CrossThreeRankTwoOn I294CrossIsReeG2 := by
  intro L _ _ _ _ d hd hch
  obtain ⟨i, hv⟩ := d
  cases i with
  | reeG2 m => exact (hch (TauCeti.LieTypeIndex.characteristic_reeG2 m)).elim
  | _ => exact (hd : False).elim

theorem I294CrossThreeRankTwo.rest_of_families (hSz : I294CrossThreeRankTwoSz)
    (hTri : I294CrossThreeRankTwoTriality) (hExc : I294CrossThreeRankTwoExc)
    (hCl : I294CrossThreeRankTwoClassical) :
    I294CrossThreeRankTwoOn fun d =>
      ¬ I294CrossIsG2 d ∧ ¬ I294CrossIsReeF4 d ∧ ¬ I294CrossIsTits d := by
  intro L _ _ hs hn d hd
  obtain ⟨i, hv⟩ := d
  cases i with
  | A r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | twistedA r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | B r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | C r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | D r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | twistedD r q => exact hCl L hs hn ⟨_, hv⟩ trivial
  | E6 q => exact hExc L hs hn ⟨_, hv⟩ trivial
  | E7 q => exact hExc L hs hn ⟨_, hv⟩ trivial
  | E8 q => exact hExc L hs hn ⟨_, hv⟩ trivial
  | F4 q => exact hExc L hs hn ⟨_, hv⟩ trivial
  | twistedE6 q => exact hExc L hs hn ⟨_, hv⟩ trivial
  | trialityD4 q => exact hTri L hs hn ⟨_, hv⟩ trivial
  | suzuki m => exact hSz L hs hn ⟨_, hv⟩ trivial
  | reeG2 m => exact i294CrossThreeRankTwoOn_reeG2 L hs hn ⟨_, hv⟩ trivial
  | G2 q => exact (hd.1 trivial).elim
  | reeF4 m => exact (hd.2.1 trivial).elim
  | tits => exact (hd.2.2 trivial).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
