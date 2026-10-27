module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBGen2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAD
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B6
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBQ

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_k7abs (c : Ctx7 G L) (hb : B7Std c) :
    K7Abs (y7cRhoC c hb) (y7cTC c hb) (y7cJC c) (y7cQC c) (y7cPC c) (y7cM6C c) (y7cM7C c) where
  kgroup := y7c_B_kgroup c hb
  M_E := y7c_B_M3_isE c hb
  t_sq := y7c_B_t_sq c hb
  t_ne := y7c_B_t_ne c hb
  J_iso := y7c_B_J_iso c hb
  J_cent := y7c_B_J_cent c hb
  J_fpf := y7c_B_J_fpf c hb
  ρ_inj := y7c_B_rho_inj c hb
  Q_two := y7c_B_Q_two c hb
  Q_card := y7c_B_Q_card c hb
  Q_J := y7c_B_Q_J c hb
  t_mem_Q := y7c_B_t_mem_Q c hb
  cent := y7c_B_cent c hb
  P_two := y7c_B_P_two c hb
  P_card := y7c_B_P_card c hb
  P_sup := y7c_B_P_sup c hb
  M6_E := y7c_B_M6_E c hb
  M7_E := y7c_B_M7_E c hb
  M67 := y7c_B_M67 c hb
  P_norm_t := y7c_B_P_norm_t c hb
  P_cent_t := y7c_B_P_cent_t c hb
  M6_gen := y7c_B_M6_gen c hb
  M7_gen := y7c_B_M7_gen c hb
  comm_wit := y7c_B_comm_wit c hb

theorem y7c_b7Std_of (hB : Sec3Inputs) (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L))
    (c : Ctx7 G L) (h5 : c.toCtx5.Facts5) (h6 : c.Upto76) : B7Std c :=
  ⟨b6Std_of_upto75 (f33hyp_of hB hS hL c.s c.e) h5 h6.1, h6.2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
