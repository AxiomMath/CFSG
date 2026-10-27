module

public import Certificates.Data.Kernel.M24Dc.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Inputs

@[expose] public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

noncomputable def m24LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := m24STabs
  mw := CFSG.KD.M24Dc.J.mw.toArray
  mt := CFSG.KD.M24Dc.J.mw.toArray.map fun ws =>
    ws.map (CFSG.KC.SLDc.wordTabL #[m24ta.toArray, m24tb.toArray] 24)
  Om := #[CFSG.KD.M24Dc.Om 0, CFSG.KD.M24Dc.Om 1, CFSG.KD.M24Dc.Om 2, CFSG.KD.M24Dc.Om 3,
    CFSG.KD.M24Dc.Om 4, CFSG.KD.M24Dc.Om 5, CFSG.KD.M24Dc.Om 6, CFSG.KD.M24Dc.Om 7,
    CFSG.KD.M24Dc.Om 8, CFSG.KD.M24Dc.Om 9, CFSG.KD.M24Dc.Om 10, CFSG.KD.M24Dc.Om 11,
    CFSG.KD.M24Dc.Om 12]
  atoms := #[]
  joins := []

noncomputable def m24OtK : Array (OmegaData (List (List ℕ))) :=
  #[CFSG.KD.M24Dc.Ot 0, CFSG.KD.M24Dc.Ot 1, CFSG.KD.M24Dc.Ot 2, CFSG.KD.M24Dc.Ot 3,
    CFSG.KD.M24Dc.Ot 4, CFSG.KD.M24Dc.Ot 5, CFSG.KD.M24Dc.Ot 6, CFSG.KD.M24Dc.Ot 7,
    CFSG.KD.M24Dc.Ot 8, CFSG.KD.M24Dc.Ot 9, CFSG.KD.M24Dc.Ot 10, CFSG.KD.M24Dc.Ot 11,
    CFSG.KD.M24Dc.Ot 12]

abbrev M24DcFacts : Prop :=
  CFSG.KC.SLDc.dcCheck CFSG.KD.M24Dc.C CFSG.KD.M24Dc.D = true ∧
    CFSG.KD.M24Dc.J.tabs = [m24ta, m24tb, (m24SLP[180]!).toList, (m24SLP[187]!).toList,
      (m24SLP[196]!).toList, (m24SLP[211]!).toList, (m24SLP[218]!).toList,
      (m24SLP[223]!).toList, (m24SLP[228]!).toList, (m24SLP[231]!).toList] ∧
    CFSG.KD.M24Dc.tabsOK = true ∧ CFSG.KD.M24Dc.invOK = true ∧
    CFSG.KD.M24Dc.J.sep = CFSG.KD.M24Dc.sepL ∧ CFSG.KD.M24Dc.mwOK = true ∧
    CFSG.KD.M24Dc.J.mw.getD 0 [] = [] ∧ CFSG.KD.M24Dc.J.mw.length = 13 ∧
    (List.range 13).all CFSG.KD.M24Dc.memOK = true ∧
    (List.range 13).all CFSG.KD.M24Dc.otOK = true ∧
    CFSG.KD.M24Dc.fixOK = true ∧ CFSG.KD.M24Dc.moveOK = true ∧ CFSG.KD.M24Dc.topOK = true ∧
    m24LatK.Om.map (fun o => o.lbl.size) = #[1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9] ∧
    m24OtK.map (fun o => o.lbl.size) = #[1, 64, 16, 16, 8, 4, 8, 2, 2, 2, 4, 2, 4]

end CFSG.QuasithinUnique.Ch1.SporLat.M24
