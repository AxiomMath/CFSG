module

public import CFSG.GH74.Generic.BProg.NS.Leaf
public import CFSG.GH74.Generic.S3.BFreeBasic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Th2Cent5
public import CFSG.GH74.GLS.C3.Layer1.Th2Sig10
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31s
public import CFSG.GH74.Generic.BProg.Assembly
public import CFSG.GH74.Generic.BProg.Frozen
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.GLS CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem liftCentralAt_of_onlyInvXNS (hL1 : B_Gen4_liftJ2NS) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hr : 3 ≤ Open.twoRank G) (hgen : Gen4 G)
    (hK : KGH G) (hsyl : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G))
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K) (hd0 : d2 ↥K ≠ 0) (hshape : QShapeNS ↥K)
    (hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L)
    (hAltD : ∀ (K' : Type) [Group K'], InG2Depth (d2 ↥K) K' → ¬ IsAltQuot K')
    (hOnly : OnlyInvX x K) (hthin : ¬ GLS.HasTwoThinConfiguration G) : LiftCentralAt x K := by
  obtain ⟨M, hJ2, himg⟩ := exists_isJ2_of_onlyInvX hs hn hr hK hx hKc hg2 hmin hOnly
  have hdepth := depthOfG_eq_of_mindepth hs hn hr hK hx hKc hg2 hmin
  have hNoAlt : ¬ ∃ (x' : G) (M' : Subgroup G), IsJ2Alt x' M' := by
    rintro ⟨x', M', hJ2', hAlt⟩
    have hd : d2 (↥M' ⧸ pPrimeCore 2 ↥M') = d2 ↥K := hJ2'.2.1.trans hdepth
    have hcl : InG2Depth (d2 ↥K) (↥M' ⧸ pPrimeCore 2 ↥M') := by
      rw [← hd]
      exact inG2Depth_d2_of_ne_zero (by rw [hd]; exact hd0)
    exact hAltD _ hcl hAlt
  obtain ⟨eM⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hJ2.1.1.2.2
  have hbar : C3.Layer1.PumpCalc.bar x M = K := himg
  have eMK : (↥M ⧸ pPrimeCore 2 ↥M) ≃* ↥K := eM.trans (MulEquiv.subgroupCongr hbar)
  obtain ⟨hq, -⟩ := hL1 G hs hn hr hgen hK hsyl ⟨x, hx, K, hKc, hg2⟩ hthin x M hJ2 hNoAlt
    (QShapeNS.of_mulEquiv eMK.symm hshape)
  exact liftCentralAt_of_quasisimple hx hKc hJ2.1.1.2.2 himg hq

end CFSG.GH74.Generic.BProg
