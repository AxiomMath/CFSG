module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Tits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3F4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3D4
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2197
public import Certificates.Certificate2262
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2270
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3157
public import Certificates.Certificate4047
public import Certificates.Certificate4065
public import Certificates.Certificate4074
public import Certificates.Certificate4078
public import Certificates.Certificate8033
public import Certificates.Certificate4119
public import Certificates.Certificate4139
public import Certificates.Certificate17029
public import Certificates.Certificate3950
public import Certificates.Certificate17030
public import Certificates.Certificate3951
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.QuasithinUnique.A5

structure Kc3Residual : Prop where
  j4 : Kc3For (Kc3Spor .J4)
  hs : Kc3For (Kc3Spor .HS)
  he : Kc3For (Kc3Spor .He)
  ru : Kc3For (Kc3Spor .Ru)

theorem kc3Inspection_of_residual
    (h : Kc3Residual) : Kc3Inspection :=
  kc3Inspection_of_families
    { psl3 := kc3For_psl3
      psp4 := kc3For_psp4
      g2 := kc3For_g2_of_even kc3For_g2_even
      d4 := kc3For_d4_of_even kc3For_d4_even
      f4 := kc3For_f4
      tits := kc3For_tits
      l4 := kc3For_L4
      l5 := kc3For_l5
      m22 := kc3For_of_localFor (isoInv_spor .M22) kc3LocalFor_m22
      m23 := kc3For_of_localFor (isoInv_spor .M23) kc3LocalFor_m23
      m24 := kc3For_of_localFor (isoInv_spor .M24) kc3LocalFor_m24
      j4 := h.j4
      hs := h.hs
      he := h.he
      ru := h.ru }

end CFSG.QuasithinUnique.A5
