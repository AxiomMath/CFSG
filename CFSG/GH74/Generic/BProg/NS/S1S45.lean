module

public import CFSG.GH74.Generic.BProg.NS.Basic
public import CFSG.GH74.Generic.S3.BFreeBasic
public import CFSG.GH74.Generic.OnlyInvSources
public import CFSG.GH74.Generic.AltDepth
public import CFSG.GH74.Generic.S45.LLiftJ
public import CFSG.GH74.Generic.S1.NbrCompFinal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.ON.SimpleBase

public section

namespace CFSG.GH74.Generic.BProg

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.GLS CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

theorem QShapeNS.of_isJ1OrRee {K : Type} [Group K] (h : S45.IsJ1OrRee K) : QShapeNS K := by
  rcases h with h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl h))

theorem s1LiftCentralProp_of_liftJ2NS (hL1 : B_Gen4_liftJ2NS) : S1.S1LiftCentralProp := by
  intro G _ _ x K hset hfront
  have hg2 : GLS.InG2 ↥K := hset.jmax.1.2.2
  exact liftCentralAt_of_onlyInvXNS hL1 hset.simple hset.nonab hset.rank hset.gen4 hset.kgh
    hset.sylow hset.inv hset.comp hg2 (hd0_S1 hset.shape.1 hg2) (Or.inl hset.shape.1)
    (fun y L hL => (hset.jmax.2 y L hL).1) (hAltD_S1 hset.shape.1)
    (hfront.onlyInvX hset.inv) hset.nothin

theorem liftCentralAt_of_liftJ2NS (hKf : S45.B_S45_KFacts) (hL1 : B_Gen4_liftJ2NS)
    (hF : SporadicDepthFacts) {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hKGH : KGH G) {x : G} (hx : orderOf x = 2)
    {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K) (hj : S45.IsJ1OrRee ↥K)
    (hnot : xbar x ∉ K) (hr : 3 ≤ pRank 2 G)
    (hnab : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G)) (hmax : IsJMax x K)
    (hthin : ¬ GLS.HasTwoThinConfiguration G) : LiftCentralAt x K := by
  have hKB : S45.KBase ↥K := hKf ↥K hj
  have hg2 : GLS.InG2 ↥K := hmax.1.2.2
  have hr' : 3 ≤ Open.twoRank G := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hr
    exact hr
  exact liftCentralAt_of_onlyInvXNS hL1 hs hn hr' hgen hKGH hnab hx hKc hg2
    (hd0_S45 hKB hg2 hj) (QShapeNS.of_isJ1OrRee hj) (fun y L hL => (hmax.2 y L hL).1)
    (hAltD_S45 hF hKc.1 hKB.1 hj) (S45.onlyInvX hKf hs hn hgen hx hKc hj hnot) hthin

theorem b_S45_liftCentral_of_liftJ2NS (hKf : S45.B_S45_KFacts) (hL1 : B_Gen4_liftJ2NS)
    (hF : SporadicDepthFacts) : S45.B_S45_liftCentral :=
  S45.b_S45_liftCentral_of_core fun _ _ _ hs hn hgen hKGH _ hx _ hKc hj hnot hr hnab hmax hthin =>
    liftCentralAt_of_liftJ2NS hKf hL1 hF hs hn hgen hKGH hx hKc hj hnot hr hnab hmax hthin

end CFSG.GH74.Generic.BProg
