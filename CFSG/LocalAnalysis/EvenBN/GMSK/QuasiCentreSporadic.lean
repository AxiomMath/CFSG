module

public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicBase
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicA
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicB
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreSporadicC

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint QSporadic

section Certified


theorem qFree_all (s : TauCeti.SporadicName) : QFree s := by
  cases s with
  | M11 => exact m11_qFree
  | M12 => exact m12_qFree
  | M22 => exact m22_qFree
  | M23 => exact m23_qFree
  | M24 => exact m24_qFree
  | J1 => exact j1_qFree
  | J2 => exact j2_qFree
  | J3 => exact j3_qFree
  | J4 => exact j4_qFree
  | HS => exact hs_qFree
  | McL => exact mcl_qFree
  | He => exact he_qFree
  | Ru => exact ru_qFree
  | Suz => exact suz_qFree
  | ONan => exact on_qFree
  | Co1 => exact co1_qFree
  | Co2 => exact co2_qFree
  | Co3 => exact co3_qFree
  | Fi22 => exact fi22_qFree
  | Fi23 => exact fi23_qFree
  | Fi24Prime => exact fi24prime_qFree
  | HN => exact hn_qFree
  | Ly => exact ly_qFree
  | Th => exact th_qFree
  | B => exact b_qFree
  | M => exact m_qFree

theorem qFixedRootSelector_sporadic :
    QFixedRootSelector fun D _ => NativeSporadic.SporadicRep D :=
  fun D _ _ hD ⟨s, hs⟩ n α J d => (qFree_all s D hD hs n α J d).elim

end Certified

end CFSG.LocalAnalysis.EvenBN.GMSK
