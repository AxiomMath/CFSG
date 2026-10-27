module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79m
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79y
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79x
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Final

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem sec79_holds (hB : Sec3Inputs)
    (hSM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    Sec79 := by
  intro G _ _ L hS hL c h5 h78 L1 hcomp
  obtain ⟨⟨h76, h77⟩, -⟩ := h78
  obtain ⟨⟨-, h75⟩, -⟩ := h76
  obtain ⟨hMle, -, hsup, hinf, hcomm, hsec⟩ := hcomp
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  have hP : IsSylowIn 2 (L1 ⊔ conjSub c.s.t L1) (P7 c.e) := by
    rw [hsup]
    exact h77.1
  have key := y7c_79_main (M := M3 c.s) (L1 := L1) (P := P7 c.e) (V := V1 c.e) (J := JF c.s)
    (t := c.s.t) (y7c_M3_elem c hH h5.2.2.2.2.2) (y7c_card_M3 c.toCtx5 hH) (y7c_t_sq c.s)
    (y7c_conjSub_t_M3 c.toCtx5 hH) ⟨hMle, hsec⟩ hinf hcomm hP inf_le_right
    (y7c_card_V1 c hH) (y7c_V1_comm_P c h5 h75) ((y7c_JF_le_K7 c.s).trans hsup.ge)
    (y7c_JF_comm_t c.s) (y7c_card_JF hH) (y7c_centIn_M3_JF c.toCtx5 hH) hSM
  rw [hsup] at key
  exact key

end CFSG.OddStandard.HigherRank.YamadaG23
