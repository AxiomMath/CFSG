module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBGlue
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAStruct
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CCOdd
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem sec77_strong (hB : Sec3Inputs) (hI31 : CFSG.ASVolI.I_3_1) (hN24 : Nar24)
    (hSM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2)
    (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L)) (c : Ctx7 G L) (h5 : c.toCtx5.Facts5)
    (h6 : c.Upto76) :
    IsSylowIn 2 (K7 c.s) (P7 c.e) ∧ ∃ L1 : Subgroup G, IsCompPre c.s L1 := by
  have hb : B7Std c := y7c_b7Std_of hB hS hL c h5 h6
  rcases y7c_struct hI31 hN24 hSM (y7c_k7abs c hb) with
    ⟨Y, hY, hd, hP⟩ | ⟨r, z, hr, hr2, hz, hzc, hzp, hzf⟩
  · exact ⟨y7c_sylow_pre c hb hP, y7cPre c.s Y, y7c_isCompPre_pre c hb hY hd⟩
  · exact (y7c_odd_false c hb r z hr hr2 hz hzc hzp hzf).elim

theorem sec77_holds (hB : Sec3Inputs) (hI31 : CFSG.ASVolI.I_3_1) (hN24 : Nar24)
    (hSM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    Sec77 := by
  intro G _ _ L hS hL c h5 h6
  obtain ⟨hP, L1, hL1⟩ := sec77_strong hB hI31 hN24 hSM hS hL c h5 h6
  exact ⟨hP, Or.inl ⟨L1, hL1⟩⟩

end CFSG.OddStandard.HigherRank.YamadaG23
