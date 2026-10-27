module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63Ext
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSec4S

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y63_secProp (c : Ctx6 G L) (hH : F33Hyp c.s c.e) (hY : Y63Hyps c) :
    SecProp (y63Q c) (S3 c.s) (fun Y _ _ _ => IsCyclic Y) := by
  have hcardS3 : Nat.card ↥(S3 c.s) = 512 := y6e_card_S3 c.toCtx5 hH
  have hmul := Subgroup.relIndex_mul_card (S3 c.s) (y63Q c)
  rw [inf_of_le_left hY.S3_le, hY.card, hcardS3] at hmul
  have hidx : (S3 c.s).relIndex (y63Q c) = 2 := by omega
  have hN : ((S3 c.s).subgroupOf (y63Q c)).Normal := Subgroup.normal_of_index_eq_two hidx
  refine ⟨hN, ?_⟩
  haveI := hN
  have hq : Nat.card (↥(y63Q c) ⧸ (S3 c.s).subgroupOf (y63Q c)) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  exact isCyclic_of_prime_card (p := 2) hq

theorem y63_fact63 (hHS : HSSylowFacts) (c : Ctx6 G L) (hS : HRSetting G L)
    (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) (h61 : c.Fact61) (h62 : c.Fact62) :
    c.Fact63 := by
  intro hRT
  have hY := y63_hyps c hH hF hRT
  have hC := y63_concl hHS c hH hF h62 hRT
  have hSyl := y63_sylow c hH hY h61 hC
  have hext := y63_ext c hH hF hY hRT h61 hC hSyl
  haveI : IsSimpleGroup G := hS.std.simple
  exact transfer_of_isSylowIn hS.std.nonab hSyl hY.S3_le (y63_secProp c hH hY) c.s.t_order hext

end CFSG.OddStandard.HigherRank.YamadaG23
