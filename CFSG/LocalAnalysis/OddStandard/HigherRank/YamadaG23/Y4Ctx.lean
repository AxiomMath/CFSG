module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YBundle
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Hyp
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Ctx4 (s : Setting3 G L) (e : Setting3.Ext s) : Prop where
  hS : HRSetting G L
  hZ : Odd (Nat.card ↥(center ↥L))
  hOut : (innerAut (L ⧸ center L)).index = 2
  h31 : s.Fact31
  hDef : e.FactDef
  h32 : e.Fact32
  h33 : e.Fact33
  hLF : LFacts s
  hA : LFactsA s
  hRel : SRel s.fr
  hBr : BranchA e

theorem Ctx4.toF33 {s : Setting3 G L} {e : Setting3.Ext s} (c : Ctx4 s e) : F33Hyp s e :=
  ⟨c.hS, c.hZ, c.hOut, c.h31, c.hDef, c.h32, c.hLF⟩

theorem ctx4_of (hB : Sec3Inputs) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    (s : Setting3 G L) (e : Setting3.Ext s) (hBr : BranchA e) : Ctx4 s e := by
  have hZ := hB.oddCentre G L hS hL
  exact ⟨hS, hZ, hB.outTwo _ hL, hB.f31 G L hS hL s, hB.fDef G L hS hL s e,
    hB.f32 G L hS hL s e, hB.f33 G L hS hL s e, hB.transport G L hS hL s,
    lfactsA_of_setting hS hZ s, s3_srel hS hZ s, hBr⟩

end CFSG.OddStandard.HigherRank.YamadaG23
