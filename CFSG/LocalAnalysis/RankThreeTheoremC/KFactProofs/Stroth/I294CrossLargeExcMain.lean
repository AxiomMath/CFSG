module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeExcAbel
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeExcE
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeExcTw

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open

theorem i294CrossLargePrimeOn_nonclassical :
    I294CrossLargePrimeOn fun d => ¬ I294CrossIsClassical d := by
  intro p hp h5 L _ _ hs hn d hd
  obtain ⟨i, hv⟩ := d
  cases i with
  | A r q => exact (hd trivial).elim
  | twistedA r q => exact (hd trivial).elim
  | B r q => exact (hd trivial).elim
  | C r q => exact (hd trivial).elim
  | D r q => exact (hd trivial).elim
  | twistedD r q => exact (hd trivial).elim
  | E6 q => exact i294CrossLargePrimeOn_E6 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | E7 q => exact i294CrossLargePrimeOn_E7 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | E8 q => exact i294CrossLargePrimeOn_E8 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | F4 q => exact i294CrossLargePrimeOn_F4 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | twistedE6 q => exact i294CrossLargePrimeOn_twistedE6 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | G2 q => exact i294CrossLargePrimeOn_G2 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | trialityD4 q => exact i294CrossLargePrimeOn_triality p hp h5 L hs hn ⟨_, hv⟩ trivial
  | suzuki m => exact i294CrossLargePrimeOn_sz p hp h5 L hs hn ⟨_, hv⟩ trivial
  | reeG2 m => exact i294CrossLargePrimeOn_reeG2 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | reeF4 m => exact i294CrossLargePrimeOn_reeF4 p hp h5 L hs hn ⟨_, hv⟩ trivial
  | tits => exact i294CrossLargePrimeOn_tits p hp h5 L hs hn ⟨_, hv⟩ trivial

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
