module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Gen
public import Certificates.Certificate6125
public import Certificates.Certificate6119
public import Certificates.Certificate6122

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem normalizers_generate_eight_of_certificate
    {K : Type} [Group K] [Finite K]
    (hK : IsDoubleCoverOfAlt K 8) (S : Sylow 2 K) :
    (⨆ (E : Subgroup K) (_ : E ≤ SignalizerFunctorTheorem.Glauberman.thompsonJ 2 (S : Subgroup K))
      (_ : IsMulCommutative E) (_ : 2 ≤ Open.pRank 2 E), normalizer (E : Set K)) = ⊤ :=
  AhatData.normalizers_generate_of_genGood_J (by norm_num) (by norm_num) hK
    Certificates.certificate6119.1 Certificates.certificate6119.2.1
    Certificates.certificate6125.1 S

theorem normalizers_generate_eleven_of_certificate
    {K : Type} [Group K] [Finite K]
    (hK : IsDoubleCoverOfAlt K 11) (S : Sylow 2 K) :
    (⨆ (E : Subgroup K) (_ : E ≤ (S : Subgroup K)) (_ : IsMulCommutative E)
      (_ : 2 ≤ Open.pRank 2 E), normalizer (E : Set K)) = ⊤ :=
  AhatData.normalizers_generate_of_genGood_S (by norm_num) (by norm_num) hK
    Certificates.certificate6122.1 Certificates.certificate6122.2.1
    Certificates.certificate6125.2 S

end CFSG.OddStandard.Solomon75
