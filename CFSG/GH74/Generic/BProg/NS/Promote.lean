module

public import CFSG.GH74.Generic.BProg.NS.Leaf
public import CFSG.GH74.Generic.S3.BFreePromote
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
open CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.TwoThin

theorem qShapeNS_of_inG2Depth_seven (K : Type) [Group K] (h : InG2Depth 7 K) : QShapeNS K := by
  obtain ⟨-, hdisj⟩ := h
  have hL3 : IsL3OddGt3 K := by
    rcases hdisj with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h⟩ | ⟨h1, -⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h
    · omega
  exact Or.inr (Or.inl hL3)

theorem qShapeNS_of_d2_eq_seven {K : Type} [Group K] (h : d2 K = 7) : QShapeNS K := by
  have h1 : InG2Depth (d2 K) K := inG2Depth_d2_of_ne_zero (by rw [h]; norm_num)
  rw [h] at h1
  exact qShapeNS_of_inG2Depth_seven K h1

theorem exists_isJ2_of_isJMax_atNS (d : ℕ) (hd0 : d ≠ 0) (hL1 : B_Gen4_liftJ2NS)
    (hTab : B_pumpupStepAt d) (hAlt : ∀ (K : Type) [Group K], InG2Depth d K → ¬ IsAltQuot K)
    (hdShape : ∀ (K' : Type) [Group K'], InG2Depth d K' → QShapeNS K')
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a)
    (hr : 3 ≤ Open.twoRank G) (hgen : Gen4 G) (hK : KGH G)
    (hsyl : ∀ S : Sylow 2 G, ¬ IsMulCommutative (S : Subgroup G))
    {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)} (hKc : IsComponent K)
    (hg2 : GLS.InG2 ↥K) (hd : d2 ↥K = d) (hmax : IsJMax x K)
    (hthin : ¬ GLS.HasTwoThinConfiguration G) :
    ∃ M : Subgroup G, IsJ2 x M ∧ imgBar x M = K := by
  classical
  have hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L :=
    fun y L hp => (hmax.2 y L hp).1
  obtain ⟨M₀, hILo₀, himg₀, ⟨e₀⟩⟩ := exists_ilo_over hs hn hr hx hKc
  have hM₀ : GLS.IsPCompIn 2 (centralizer ({x} : Set G)) M₀ := hILo₀.2.2
  have hdepth : depthOfG G = d := by
    have := depthOfG_eq_of_mindepth hs hn hr hK hx hKc hg2 hmin
    rw [this, hd]
  have hbase : PumpGood K M₀ x M₀ := by
    refine ⟨hILo₀, ?_, ?_, ?_, ⟨MulEquiv.refl _⟩⟩
    · rw [himg₀]; exact hmax.1
    · rw [himg₀]
    · rw [himg₀]
  have hlong' : ∀ p : G × Subgroup G,
      Relation.ReflTransGen (fun a b : G × Subgroup G => GLS.PumpUpLT 2 a.1 a.2 b.1 b.2) (x, M₀) p →
        PumpGood K M₀ p.1 p.2 := by
    intro p hp
    induction hp with
    | refl => exact hbase
    | tail _ hstep ih =>
      exact pumpGood_step hd0 hTab hs hn hgen hK hd hmax ih hstep
  have hlong : ∀ (y : G) (N : Subgroup G), LongPumpUp 2 x M₀ y N → PumpGood K M₀ y N :=
    fun y N h => hlong' (y, N) h.2
  have hrig : IsPRigid 2 x M₀ := ⟨hILo₀, fun y N h => (hlong y N h).2.2.2.2⟩
  obtain ⟨z, M, hzM, hrigM, hgmM, hrank⟩ := exists_rigid_gilman_rank hrig
  have h3 : 3 ≤ pRank 2 G := by
    rw [pRank_two_eq_twoRank]
    exact hr
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) :=
    fun y hy => TwoThin.rankThreeCentralizers G hs hn h3 y hy
  have hTz : IsTwoTerminal z M :=
    isTwoTerminal_of_noDiag hrigM hgmM (noDiag_of_rigid_gilman hR hrigM hgmM)
  obtain ⟨hILoz, hG2z, hdz, -, -⟩ := hlong z M hzM
  have hMpc : GLS.IsPCompIn 2 (centralizer ({z} : Set G)) M := hILoz.2.2
  obtain ⟨ezb⟩ := C3.Layer1.PumpCalc.kBar_equiv_bar hMpc
  have hdM : d2 (↥M ⧸ pPrimeCore 2 ↥M) = d := by
    rw [d2_congr ezb]
    exact hdz.trans hd
  have hJ2z : IsJ2 z M :=
    ⟨⟨hILoz, inG2_of_mulEquiv ezb.symm hG2z.2.2⟩, hdM.trans hdepth.symm, hTz⟩
  have hMdepth : InG2Depth d (↥M ⧸ pPrimeCore 2 ↥M) := by
    have h1 : d2 (↥M ⧸ pPrimeCore 2 ↥M) ≠ 0 := by rw [hdM]; exact hd0
    have := inG2Depth_d2_of_ne_zero h1
    rwa [hdM] at this
  obtain ⟨-, h1⟩ := hL1 G hs hn hr hgen hK hsyl ⟨x, hx, K, hKc, hg2⟩ hthin z M hJ2z
    (noIsJ2Alt_of_depth hd0 hAlt hdepth) (hdShape _ hMdepth)
  have h1' : pRank 2 ↥(CxK x M₀) ≤ 1 := by omega
  have hOnly : OnlyInvX x K := onlyInvX_of_pRank_CxK hx hM₀ himg₀ h1'
  exact exists_isJ2_of_onlyInvX hs hn hr hK hx hKc hg2 hmin hOnly

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}

theorem exists_isJ2_of_isJMaxNS (hL1 : B_Gen4_liftJ2NS) (hTab : B_pumpupStepAt 7)
    (hset : S3Setup G x K) (hmax : IsJMax x K) (hthin : ¬ GLS.HasTwoThinConfiguration G) :
    ∃ M : Subgroup G, IsJ2 x M ∧ imgBar x M = K :=
  exists_isJ2_of_isJMax_atNS 7 (by norm_num) hL1 hTab not_isAltQuot_of_inG2Depth_seven
    qShapeNS_of_inG2Depth_seven hset.simple hset.nonab hset.rank hset.gen4 hset.kgh hset.sylow
    hset.inv hset.comp hset.g2 (d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape) hmax hthin

theorem liftCentralAt_of_isJMaxNS (hL1 : B_Gen4_liftJ2NS) (hTab : B_S3_pumpupStep)
    (hset : S3Setup G x K) (hmax : IsJMax x K) (hthin : ¬ GLS.HasTwoThinConfiguration G) :
    LiftCentralAt x K := by
  obtain ⟨M, hJ2, himg⟩ := exists_isJ2_of_isJMaxNS hL1 hTab hset hmax hthin
  have hdepth : depthOfG G = 7 := by
    have hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L :=
      fun y L hp => (hmax.2 y L hp).1
    have := depthOfG_eq_of_mindepth hset.simple hset.nonab hset.rank hset.kgh hset.inv hset.comp
      hset.g2 hmin
    rw [this]
    exact d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  obtain ⟨hq, -⟩ := hL1 G hset.simple hset.nonab hset.rank hset.gen4 hset.kgh hset.sylow
    ⟨x, hset.inv, K, hset.comp, hset.g2⟩ hthin x M hJ2
    (noIsJ2Alt_of_depth (by norm_num) not_isAltQuot_of_inG2Depth_seven hdepth)
    (qShapeNS_of_d2_eq_seven (hJ2.2.1.trans hdepth))
  exact liftCentralAt_of_quasisimple hset.inv hset.comp hJ2.1.1.2.2 himg hq

theorem b_S3_onlyInvJNT_of_liftJ2NS (hL1 : B_Gen4_liftJ2NS) (hTab : B_S3_pumpupStep) :
    B_S3_onlyInvJNT := by
  intro G _ _ x K hset hmax hthin
  obtain ⟨M, hJ2, himg⟩ := exists_isJ2_of_isJMaxNS hL1 hTab hset hmax hthin
  have hdepth : depthOfG G = 7 := by
    have hmin : ∀ (y : G) (L : Subgroup (CentralizerBar y)), G2Pair y L → d2 ↥K ≤ d2 ↥L :=
      fun y L hp => (hmax.2 y L hp).1
    have := depthOfG_eq_of_mindepth hset.simple hset.nonab hset.rank hset.kgh hset.inv hset.comp
      hset.g2 hmin
    rw [this]
    exact d2_eq_seven_of_shapeS3 hset.comp hset.g2 hset.shape
  obtain ⟨-, h1⟩ := hL1 G hset.simple hset.nonab hset.rank hset.gen4 hset.kgh hset.sylow
    ⟨x, hset.inv, K, hset.comp, hset.g2⟩ hthin x M hJ2
    (noIsJ2Alt_of_depth (by norm_num) not_isAltQuot_of_inG2Depth_seven hdepth)
    (qShapeNS_of_d2_eq_seven (hJ2.2.1.trans hdepth))
  exact onlyInvX_of_pRank_CxK hset.inv hJ2.1.1.2.2 himg h1.le

end CFSG.GH74.Generic.BProg
