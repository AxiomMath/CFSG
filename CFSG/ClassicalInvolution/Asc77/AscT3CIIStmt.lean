module

public import CFSG.ClassicalInvolution.Asc77.WP2Interface
public import CFSG.ClassicalInvolution.SmallCases.DSplitBranch

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

@[expose] def sec20O2 (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ Odd (orderOf x)}

@[expose] def sec20X (Ω : Set (Subgroup G)) (z : G) (K K' : Subgroup G) : Subgroup G :=
  (⨆ U ∈ {U : Subgroup G | U ∈ USet Ω ∧ U ≤ Subgroup.centralizer ({z} : Set G)}, U) ⊔ K ⊔ K'

@[expose] def InducesFAut (K R : Subgroup G) (a : G) : Prop :=
  a ∈ Subgroup.normalizer (K : Set G) ∧ a * a ∈ centralizerModOdd ⊤ K ∧
    ∃ P : Subgroup G, IsSylow2In P (K ⊓ Subgroup.centralizer ({a} : Set G)) ∧ IsQuatSub P ∧
      2 * Nat.card P = Nat.card R

end Vocabulary

variable (p f : ℕ) [Fact p.Prime]

structure CaseIIHyp {G : Type} [Group G] [Finite G] (K J : Subgroup G) (z t a g : G) : Prop where
  branch : DBranchD p f K z
  below : CITBelowAll p (Nat.card G)
  ih : IH8All p (Nat.card G)
  hyp : HypOmegaMod p f (CoreAssembly.conjClass K)
  viol : AViol (CoreAssembly.conjClass K) K J z t
  ha : a ∈ pairNormalizers K J z t
  haz : a * t * a⁻¹ = z
  hne : conjSub a J ≠ K
  hg : conjSub g K = conjSub a J
  hgz : g * z * g⁻¹ = z
  star : aStar (CoreAssembly.conjClass K) K = CoreAssembly.conjClass K

structure Std20 {G : Type} [Group G] [Finite G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G) : Prop where
  branch : DBranchD p f K z
  hyp : HypOmegaMod p f (CoreAssembly.conjClass K)
  below : CITBelowAll p (Nat.card G)
  ih : IH8All p (Nat.card G)
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

@[expose] def Sec20Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K J : Subgroup G) (z t a g : G),
    CaseIIHyp p f K J z t a g →
      ∃ (K' : Subgroup G) (S : Sylow 2 G) (R R' W V : Subgroup G), Std20 p f K K' J S R R' W V z t

section Steps

variable {p f}

@[expose] def Concl20_3 {G : Type} [Group G] (K K' V : Subgroup G) (z : G) : Prop :=
  sec20X (CoreAssembly.conjClass K) z K K' =
    oddCoreOf (sec20X (CoreAssembly.conjClass K) z K K') ⊔ (V ⊔ (K ⊔ K'))

@[expose] def Concl20_4 {G : Type} [Group G] (S : Sylow 2 G) (K K' J : Subgroup G) (z : G) : Prop :=
  centralizerModOdd (S : Subgroup G) (K ⊔ K') =
      centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J ⊔ Subgroup.zpowers z ∧
    Disjoint (centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J)
      (Subgroup.zpowers z)

@[expose] def Concl20_5 {G : Type} [Group G] (S : Sylow 2 G) (K K' : Subgroup G) (z : G) : Prop :=
  centralizerModOdd (S : Subgroup G)
      (K ⊔ K' ⊔ sec20O2 (sec20X (CoreAssembly.conjClass K) z K K')) = Subgroup.zpowers z

@[expose] def Concl20_7 {G : Type} [Group G] (S : Sylow 2 G) (K K' : Subgroup G) (z : G) : Prop :=
  centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z

@[expose] def Concl20_8 {G : Type} [Group G] (S : Sylow 2 G) (K' R : Subgroup G) : Prop :=
  centralizerModOdd (S : Subgroup G) K' = R

@[expose] def Concl20_9 {G : Type} [Group G] (S : Sylow 2 G) (K K' R R' : Subgroup G) (z : G) :
    Prop :=
  8 < Nat.card R →
    ((∃ s ∈ (S : Subgroup G), s ∉ sec20X (CoreAssembly.conjClass K) z K K') ∧
      ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G),
        x * x ∈ sec20X (CoreAssembly.conjClass K) z K K' →
        y * y ∈ sec20X (CoreAssembly.conjClass K) z K K' →
        ⁅x, y⁆ ∈ sec20X (CoreAssembly.conjClass K) z K K' →
          x ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
          y ∈ sec20X (CoreAssembly.conjClass K) z K K' ∨
          x * y ∈ sec20X (CoreAssembly.conjClass K) z K K') ∧
    (∃ a ∈ (S : Subgroup G), InducesFAut K R a ∧ InducesFAut K' R' a) ∧
    (∀ u ∈ (S : Subgroup G), u * u ∈ sec20X (CoreAssembly.conjClass K) z K K' →
      u ∈ Subgroup.normalizer (K : Set G))

variable (p f)

@[expose] def C20_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t → Concl20_3 K K' V z

@[expose] def C20_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z

@[expose] def C20_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z

@[expose] def C20_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z

@[expose] def C20_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R

@[expose] def C20_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z

@[expose] def C20_10a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Concl20_9 S K K' R R' z → 8 < Nat.card R → False

@[expose] def C20_10b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_5 S K K' z → Concl20_7 S K K' z →
        Concl20_8 S K' R → Nat.card R = 8 → False

end Steps

@[expose] def T3CaseII : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K J : Subgroup G) (z t a g : G),
    CaseIIHyp p f K J z t a g → False

variable {p f}

theorem t3CaseII_of_steps (hs : Sec20Setup p f) (h3 : C20_3 p f) (h4 : C20_4 p f)
    (h5 : C20_5 p f) (h7 : C20_7 p f) (h8 : C20_8 p f) (h9 : C20_9 p f)
    (h10a : C20_10a p f) (h10b : C20_10b p f) : T3CaseII p f := by
  intro G _ _ _ K J z t a g h
  obtain ⟨K', S, R, R', W, V, d⟩ := hs G K J z t a g h
  have c3 := h3 G K K' J S R R' W V z t d
  have c4 := h4 G K K' J S R R' W V z t d c3
  have c5 := h5 G K K' J S R R' W V z t d c3 c4
  have c7 := h7 G K K' J S R R' W V z t d c3 c4 c5
  have c8 := h8 G K K' J S R R' W V z t d c3 c4 c5 c7
  have hKΩ : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hRmem : R ∈ RSet (CoreAssembly.conjClass K) := mem_RSet_of_isSylow2In hKΩ d.hR
  have h8le : 8 ≤ Nat.card R := d.hyp.eight_le_of_mem_RSet d.branch.odd hRmem
  rcases Nat.lt_or_ge 8 (Nat.card R) with hlt | hge
  · have c9 := h9 G K K' J S R R' W V z t d c3 c4 c5 c7 c8
    exact h10a G K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 hlt
  · exact h10b G K K' J S R R' W V z t d c3 c4 c5 c7 c8 (by omega)

end CFSG.ClassicalInvolution.Asc77.T3CII
