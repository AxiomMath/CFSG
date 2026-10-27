module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6MainStd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FrameSimple

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Uniform

section Stmt


structure Branch3Core {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  member : IsClassicalMemberU (.sl2 3 1) K z
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass K)
  gen : (⨆ J ∈ CoreAssembly.conjClass K, J) = ⊤

structure Branch3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop
    extends Branch3Core K z where
  intrinsic : IsIntrinsicU (.sl2 3 1) K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem Branch3.of_dBranchU [IsSimpleGroup G] (h : DBranchU 3 1 K z) :
    Branch3 (satU (.sl2 3 1) K z) z where
  nonabelian := h.nonabelian
  member := h.member_satU
  intrinsic := isIntrinsicU_satU _ K z
  below := h.below
  rank := h.rank
  notFourGenerated := h.notFourGenerated
  dDisconnected := h.dDisconnected
  gen := gen_conjClass _ h.member_satU.mem h.member_satU.ne_one

theorem hypGen_of_modU {Ω : Set (Subgroup G)} (h : HypOmegaModU (.sl2 3 1) Ω) : HypOmegaGen Ω :=
  hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) h

@[expose] def T3Core3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch3 K z → HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K) →
      ∀ (J : Subgroup G) (zK zJ a g : G), AViol (CoreAssembly.conjClass K) K J zK zJ →
        a ∈ pairNormalizers K J zK zJ → a * zJ * a⁻¹ = zK → conjSub a J ≠ K →
          conjSub g K = conjSub a J → g * zK * g⁻¹ = zK → False

@[expose] def CaseI3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch3 K z → HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K) →
      ∀ (J : Subgroup G) (t : G), AViol (CoreAssembly.conjClass K) K J z t →
        aStar (CoreAssembly.conjClass K) K ≠ CoreAssembly.conjClass K → False

structure CaseIIHyp3 {G : Type} [Group G] [Finite G] (K J : Subgroup G) (z t a g : G) : Prop where
  branch : Branch3Core K z
  ih : IH8T 3 1 (Nat.card G)
  hyp : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ha : a ∈ pairNormalizers K J z t
  haz : a * t * a⁻¹ = z
  hne : conjSub a J ≠ K
  hg : conjSub g K = conjSub a J
  hgz : g * z * g⁻¹ = z
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K

@[expose] def T3CaseII3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K J : Subgroup G) (z t a g : G),
    CaseIIHyp3 K J z t a g → False

structure Std20Three {G : Type} [Group G] [Finite G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G) : Prop where
  branch : Branch3Core K z
  hyp : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)
  ih : IH8T 3 1 (Nat.card G)
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ne : K' ≠ K
  twins : twinSet (CoreAssembly.conjClass K) K = {K, K'}
  swap : ∃ g ∈ Subgroup.centralizer ({z} : Set G), conjSub g K = K'
  htKK : t ∈ K ⊔ K'
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hR : IsSylow2In R K
  hRS : R ≤ (S : Subgroup G)
  hR' : IsSylow2In R' K'
  hR'S : R' ≤ (S : Subgroup G)
  hRG : ∀ T ∈ RSet (CoreAssembly.conjClass K), T ≤ (S : Subgroup G) → T = R ∨ T = R'
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)
  hWN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G)
  hV : V ∈ USet (CoreAssembly.conjClass K)
  hVS : V ≤ (S : Subgroup G)
  hVW : V ≤ W
  htV : t ∈ V

@[expose] def Sec20Setup3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K J : Subgroup G) (z t a g : G),
    CaseIIHyp3 K J z t a g →
      ∃ (K' : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G),
        Std20Three K K' J S R R' W V z t

@[expose] def C20_3Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t → Concl20_3 K K' V z

@[expose] def C20_4Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z

@[expose] def C20_5Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z

@[expose] def C20_7Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z

@[expose] def C20_8Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R

@[expose] def C20_10bThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Nat.card R = 8 → False

namespace CaseIIHyp3

variable {J : Subgroup G} {t a g : G}

theorem hypGen (h : CaseIIHyp3 K J z t a g) : HypOmegaGen (CoreAssembly.conjClass K) :=
  hypGen_of_modU h.hyp

end CaseIIHyp3

namespace Std20Three

variable {K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {t : G}

theorem hypGen (d : Std20Three K K' J S R R' W V z t) : HypOmegaGen (CoreAssembly.conjClass K) :=
  hypGen_of_modU d.hyp

theorem below (d : Std20Three K K' J S R R' W V z t) :
    CITBelowT (.sl2 3 1) (Nat.card G) :=
  d.branch.below

end Std20Three

theorem t3CaseII3_of_steps (hs : Sec20Setup3) (h3 : C20_3Three) (h4 : C20_4Three)
    (h5 : C20_5Three) (h7 : C20_7Three) (h8 : C20_8Three) (h10b : C20_10bThree) : T3CaseII3 := by
  intro G _ _ _ K J z t a g h
  obtain ⟨K', S, R, R', W, V, d⟩ := hs G K J z t a g h
  have c3 := h3 G K K' J S R R' W V z t d
  have c4 := h4 G K K' J S R R' W V z t d c3
  have c5 := h5 G K K' J S R R' W V z t d c3 c4
  have c7 := h7 G K K' J S R R' W V z t d c3 c4 c5
  have c8 := h8 G K K' J S R R' W V z t d c3 c4 c5 c7
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hRmem : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
  have hR8 : Nat.card R = 8 :=
    Q3T6.natCard_rSet_of_classical (fun J hJ => by
      obtain ⟨w, hw⟩ := d.hyp.classical J hJ
      exact ⟨w, hw⟩) hRmem
  exact h10b G K K' J S R R' W V z t d c3 c4 c5 c7 c8 hR8

end Stmt

end CFSG.ClassicalInvolution.Q3.Q3T6D
