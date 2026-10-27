module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Free
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporA
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporB
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporC
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporD
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporE
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporF
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42SporEx

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

theorem gomiU42Free_sporadic :
    GomiU42Free fun D _ => NativeSporadic.SporadicRep D := by
  intro D _ _ hD hspor α S h
  obtain ⟨s, hs⟩ := hspor
  cases s with
  | J1 => exact j1_u42Free D hD hs α S h
  | M12 => exact m12_u42Free D hD hs α S h
  | M11 => exact m11_u42Free D hD hs α S h
  | M22 => exact m22_u42Free D hD hs α S h
  | M23 => exact m23_u42Free D hD hs α S h
  | M24 => exact m24_u42Free D hD hs α S h
  | J2 => exact j2_u42Free D hD hs α S h
  | J3 => exact j3_u42Free D hD hs α S h
  | J4 => exact j4_u42Free D hD hs α S h
  | HS => exact hs_u42Free D hD hs α S h
  | McL => exact mcl_u42Free D hD hs α S h
  | He => exact he_u42Free D hD hs α S h
  | Ru => exact ru_u42Free D hD hs α S h
  | Suz => exact suz_u42Free D hD hs α S h
  | ONan => exact on_u42Free D hD hs α S h
  | Co1 => exact co1_u42Free D hD hs α S h
  | Co2 => exact co2_u42Free D hD hs α S h
  | Co3 => exact co3_u42Free D hD hs α S h
  | Fi22 => exact fi22_u42Free D hD hs α S h
  | Fi23 => exact fi23_u42Free D hD hs α S h
  | Fi24Prime => exact fi24prime_u42Free D hD hs α S h
  | HN => exact hn_u42Free D hD hs α S h
  | Ly => exact ly_u42Free D hD hs α S h
  | Th => exact th_u42Free D hD hs α S h
  | B => exact b_u42Free D hD hs α S h
  | M => exact m_u42Free D hD hs α S h

theorem gomiU42Selector_sporadic :
    GomiU42Selector fun D _ => NativeSporadic.SporadicRep D :=
  GomiU42Selector.of_free gomiU42Free_sporadic

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
