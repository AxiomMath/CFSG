module

public import CFSG.ClassicalInvolution.Q3.Q3DStand

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups

section Data


structure TightStd3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  member : IsClassicalMemberU (.sl2 3 1) K z
  hyp : HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass K)
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  dDisconnected : ¬ DConnected (CoreAssembly.conjClass K)
  normEq : Subgroup.normalizer (K : Set G) = Subgroup.centralizer ({z} : Set G)
  edgeless : DEdgeless (CoreAssembly.conjClass K)

structure Sec19Data3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G) : Prop where
  tight : TightStd3 K z
  mu : ¬ AllTypeTwo K z
  cex : ¬ ConcOrTF4 G
  sylow : ∃ Q₀ : Sylow 2 K, (Q₀ : Subgroup K).map K.subtype ≤ (S : Subgroup G)
  hSz : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G)
  hW : W ∈ WSet (CoreAssembly.conjClass K)
  hWS : W ≤ (S : Subgroup G)

structure Sec19DataT3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G) : Prop extends Sec19Data3 K z S W where
  memL : L ∈ CoreAssembly.conjClass K
  invL : IsUniqueInvolution L t
  ne : t ≠ z
  memV : V ∈ USet (CoreAssembly.conjClass K)
  leW : V ≤ W
  memT : t ∈ V

end Data

section Statements


structure Std6Three {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G) : Prop where
  stand : AscStand3 Ω K
  edgeless : DEdgeless Ω
  hz : IsUniqueInvolution K z
  hR : R ∈ RSet Ω
  hRK : R ≤ K
  hRS : R ≤ (S : Subgroup G)
  cex : ¬ ConcOrTF4 G
  rank : 3 ≤ CFSG.Open.twoRank G

@[expose] def C19_11b3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W L : Subgroup G) (t : G) (V : Subgroup G), Sec19DataT3 K z S W L t V →
      (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L = ⊥

@[expose] def C19_E2Prime3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G) (S : Sylow 2 G)
    (W : Subgroup G), Sec19Data3 K z S W →
      ∃ C : Subgroup G, IsCyclic ↥C ∧
        C ≤ (S : Subgroup G) ⊓ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ∧
        ∀ x ∈ (S : Subgroup G) ⊓
            Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
          ∀ y ∈ (S : Subgroup G) ⊓
              Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G),
            x ∉ C → y ∉ C → x⁻¹ * y ∈ C

@[expose] def C19_2Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand3 Ω K → DEdgeless Ω → ∀ W ∈ WSet Ω, MuIsoZ2 Ω W ∨ MuIsoS3 Ω W

@[expose] def C19_4Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6Three Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) → MuIsoZ2 Ω W → ConcOrTF4 G

@[expose] def C19_mainThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6Three Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) → MuIsoS3 Ω W → ConcOrTF4 G

@[expose] def DataOfStd6Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G)
    (S : Sylow 2 G) (R : Subgroup G) (z : G), Std6Three Ω K S R z →
      ∀ W ∈ WSet Ω, W ≤ (S : Subgroup G) → MuIsoS3 Ω W → Sec19Data3 K z S W

end Statements

end CFSG.ClassicalInvolution.Q3.Q3T6
