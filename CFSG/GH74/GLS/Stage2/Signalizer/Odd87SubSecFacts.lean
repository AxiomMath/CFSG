module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecProp42
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31Two

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem E4Facts.of_leaves {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (h42 : Prop4_2) (hL : Lemma31Narrow) (hctx : Stage2Ctx G z k S) : E4Facts G z k where
  p42 _ _ _ _ hB _ _ hA hop hH := prop4_2_abs h42 hctx hB hA hop hH
  two _ _ _ _ hB _ _ _ h₁ h₂ h₃ h12 h13 h23 := sec31_two hL hctx hB h₁ h₂ h₃ h12 h13 h23
  f3 _ _ _ _ hB _ hJ _ _ hp hn hodd hL3 _ hc hcJ := sec31_f hL hctx hB hJ hp hn hodd hL3 hc hcJ
  uinv _ _ _ _ hB _ hJ hZ _ _ hu hv hu1 hv1 huJ hvJ huv :=
    sec31_unique_inv hL hctx hB hJ hZ hu hv hu1 hv1 huJ hvJ huv

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
