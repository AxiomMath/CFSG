module

public import CFSG.LocalAnalysis.OddStandard.GH71.Final
public import CFSG.LocalAnalysis.OddStandard.GH71.AhatMain
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Final
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyStarThm
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Core
public import CFSG.LocalAnalysis.OddStandard.Solomon75OddCoreCert

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

theorem oddCore_eq_bot_of_stage2 {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) (hcov : IsDoubleCoverOfAlt (CentralizerBar z) 11) :
    pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ :=
  oddCore_eq_bot_of_stage2_of_ivk ahatSpecAll_holds
    (ivk_8_12_ly_of_parts Ivk8.ivk812CoreA_thm
      (IVK812.lyInvariantThree_of_star IVK812.lyThreeInvStar_thm))
    coverSylowData_eleven_of_certificate alternatingBalanceData_eleven_of_certificate hctx hcov

theorem oddCore_eq_bot_of_stage2_ly {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥ := by
  have hd := hctx.data
  cases hd with
  | ly hs =>
    obtain ⟨n, hn, hs⟩ := hs
    rcases hn with rfl | rfl
    · have : IsSimpleGroup G := hctx.std.kps.1
      exact solomon44OddCore_ten_of_certificate G hctx.std.kps.2.1 z hctx.orderOf_z hs.cover
    · exact oddCore_eq_bot_of_stage2 hctx hs.cover

end CFSG.OddStandard.GH71
