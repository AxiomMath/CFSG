module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2eRank
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SL2RankC

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

theorem p47SL2e_thm : P47BranchSL2e := by
  intro G _ _ _ _ _ _ F4 Y _ _ b hY _ _ X _ _ hc _ _ _ _ E _ hE
  have hcard := P47SL2e.card_le_four_mul_card_cent_e hc hE
  have hC : Nat.card ↥(E ⊓ centralizer ((ncl X : Subgroup Y) : Set Y)) ≤ 2 := by
    obtain ⟨hmodel, -⟩ := hc
    have hnormal : (ncl X).Normal := Subgroup.normalClosure_normal
    have hcomp : IsComponent (ncl X) :=
      ⟨CFSG.GH74.Generic.S1.isQuasisimple_of_sl2 (by norm_num) hmodel, hnormal.isSubnormal⟩
    have hZ := SL2Rank.center_hat_ne_bot (by decide : Odd 5) hmodel
    apply SL2Rank.card_le_two_of_unique
    intro u hu v hv hu1 hv1
    have hu2 : u * u = 1 := by simpa [sq] using hE.2 u hu.1
    have hv2 : v * v = 1 := by simpa [sq] using hE.2 v hv.1
    have huv : u * v = v * u := hE.1.is_comm.comm ⟨u, hu.1⟩ ⟨v, hv.1⟩ |> congrArg Subtype.val
    exact F4.uinv Y b hY (ncl X) hcomp hZ u v hu2 hv2 hu1 hv1 hu.2 hv.2 huv
  omega

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
