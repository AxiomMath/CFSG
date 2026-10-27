module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomi6F
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2KP
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2Concl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx6Data
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiHypB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiHypC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YKPCat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YOutside

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gomi_apply_kp (h1R : Gomi1RKP) {A V C₀ C₁ : Subgroup G} {t u : G}
    (h : Gomi6Data A V C₀ C₁ t u)
    (hcat : ∀ H : Subgroup G, H ≤ centralizer (V : Set G) → CFSG.IsQuasisimple ↥H →
      CFSG.Blueprint.Catalog (↥H ⧸ center ↥H)) :
    ∃ Hh : Subgroup G, Hh ≤ centralizer (V : Set G) ∧
      (Hh.subgroupOf (centralizer (V : Set G))).Characteristic ∧ CFSG.IsQuasisimple ↥Hh ∧
      V ≤ Hh ∧ IsSU43 (↥Hh ⧸ CFSG.oddCore ↥Hh) := by
  obtain ⟨Hh, hle, hchar, hq, hVH, -, hSU⟩ :=
    h1R G (centralizer (V : Set G)) V (A ⊔ V) t hcat h.V_le_cent
      (fun x hx z hz => ((mem_centralizer_iff.1 hx) z hz).symm) h.hyp_Z4 le_sup_right
      h.AV_le_cent h.hyp_relIndex h.hyp_comm h.hyp_sq h.hyp_quot h.hyp_sylow h.hyp_even
      h.hyp_nonab h.t_order h.hyp_t_norm_Gh h.t_mem_normalizer_V h.hyp_AV_le h.hyp_cs_le
      h.hyp_quot6 h.hyp_seven h.hyp_comm_t
  exact ⟨Hh, hle, hchar, hq, hVH, hSU⟩

theorem y6F_of_inputs_kp (hZ : OddCentre) (h1R : Gomi1RKP) : Y6F := by
  intro G _ _ L hS hL c _ h6 h4
  have hdata := Ctx6.gomi6data c (lfactsA_of_setting hS (hZ G L hS hL) c.s) h6.1 h4
  obtain ⟨Hh, hle, hchar, hq, hVH, hSU⟩ := gomi_apply_kp h1R hdata
    (fun H hH hq => catalog_center_quotient_of_kProper hS.std.kProper
      (ne_top_of_gomi6data hdata hH) hq)
  exact ⟨(c.d * c.s.t) ^ 2, Hh,
    case3Core_of_gomiSU hdata.u_order hdata.V_eq hle hchar hq hVH hSU⟩

end CFSG.OddStandard.HigherRank.YamadaG23
