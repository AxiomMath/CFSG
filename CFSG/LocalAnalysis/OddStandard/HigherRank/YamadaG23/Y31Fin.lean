module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Q
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Syl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31CH
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31NotL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Conj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem s3_fact31 (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (hOut : (innerAut (L ⧸ center L)).index = 2) : s.Fact31 := by
  have hQ := s3_Q_eq s hS hZ hOut
  have hSyl := s3_sylow_cent s hS hQ
  have hnot := s3_t_conj_not_mem_L s hS hZ hOut hQ
  exact ⟨hSyl, s3_centIn_H s hS hSyl, hnot, s3_conjClass_eq s hS hZ hOut hQ hnot⟩

theorem fusion31_of (hZ : OddCentre) (hOut : OutTwo) : Fusion31 := by
  intro G _ _ L hS hL s
  exact s3_fact31 s hS (hZ G L hS hL) (hOut _ hL)

end CFSG.OddStandard.HigherRank.YamadaG23
