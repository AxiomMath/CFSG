module

public import CFSG.GH74.GLS.Stage1.Main.Out

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8

structure Cen2 (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  std : Std0 G
  central : IsCentralInvolution z
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))

@[expose] def TermCtx (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  G2Term G z S ∨ (∃ (q : ℕ) (w : G), Term7Out G z S q w) ∨ ∃ ε : Bool, L4U4TermTypeE ε G z S

@[expose] def RigidData (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop :=
  (∃ K₁ K₂ : Subgroup G, Std4 G z S K₁ K₂) ∨ ∃ K : Subgroup G, Std6r1 G z S K ∧ G2Concl G z S K

@[expose] def BaseBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Cen2 G z S → TermCtx G z S →
    (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
    (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      U ≤ LC z)

@[expose] def BaseBridge7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G), Cen2 G z S →
    Term7Out G z S q w →
    (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
    (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      U ≤ LC z)

@[expose] def BaseBridgeRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Cen2 G z S →
    (G2Term G z S ∨ ∃ ε : Bool, L4U4TermTypeE ε G z S) →
    (RC S z ≠ S → ∃ s ∈ S, s ∉ RC S z ∧ orderOf s = 2) ∧
    (∀ U : Subgroup G, U ≤ S → IVK.IsFourSubgroup U → (∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      U ≤ LC z)

theorem BaseBridge.of_parts (h7 : BaseBridge7) (hr : BaseBridgeRest) : BaseBridge := by
  intro G _ _ z S hcen hT
  rcases hT with hg | ⟨q, w, hT7⟩ | ⟨ε, hF⟩
  · exact hr G z S hcen (Or.inl hg)
  · exact h7 G z S q w hcen hT7
  · exact hr G z S hcen (Or.inr ⟨ε, hF⟩)

@[expose] def G2ShapeBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Cen2 G z S → G2Term G z S →
    (∃ (r₁ r₂ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), G2Shape z S r₁ r₂ L₁ L₂) ∧ PerfInner z

@[expose] def PairBridge7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G), Cen2 G z S →
    Term7Out G z S q w → Stage1Base G z S →
      ∃ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂

@[expose] def PSp4Extra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ), Cen2 G z S →
    Term7Out G z S q 1 → ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
      (RC S z).relIndex S = 2 ∧ ∃ x : G, TwoClassData G z S L₁ L₂ q x

@[expose] def PSp4TwoClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ), Cen2 G z S →
    Term7Out G z S q 1 → ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
      ∃ x : G, TwoClassData G z S L₁ L₂ q x

@[expose] def L4NFExtra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) (ε : Bool), Cen2 G z S →
    Term7Out G z S q w → w ≠ 1 → q % 4 = (if ε then 3 else 1) →
      ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
        (RC S z).relIndex S ≤ 4 ∧
        (InducedPGL2 L₁ (SBar (S1 S z) z) q ∧ InducedPGL2 L₂ (SBar (S1 S z) z) q) ∧
        ∃ x : G, TwoClassData G z S L₁ L₂ q x ∧
          (∃ y : G, GoodInvolution z S L₁ L₂ q y ∧ y ∈ centralizer ({x} : Set G)) ∧
          ∀ y : G, GoodInvolution z S L₁ L₂ q y → IsConj z y

@[expose] def L4NFRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (q : ℕ) (w : G) (ε : Bool), Cen2 G z S →
    Term7Out G z S q w → w ≠ 1 → q % 4 = (if ε then 3 else 1) →
      ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
        (InducedPGL2 L₁ (SBar (S1 S z) z) q ∧ InducedPGL2 L₂ (SBar (S1 S z) z) q) ∧
        ∃ x : G, TwoClassData G z S L₁ L₂ q x ∧
          (∃ y : G, GoodInvolution z S L₁ L₂ q y ∧ y ∈ centralizer ({x} : Set G)) ∧
          ∀ y : G, GoodInvolution z S L₁ L₂ q y → IsConj z y

@[expose] def PairBridgeF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool), Cen2 G z S →
    L4U4TermTypeE ε G z S → Stage1Base G z S →
      ∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ ∧
        L4U4TermTypeQ ε G z S q

@[expose] def L4FExtra : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ), Cen2 G z S →
    L4U4TermTypeE ε G z S → ∀ L₁ L₂ : Subgroup (CentralizerBar z), Stage1Pair G z S q L₁ L₂ →
      q % 8 = (if ε then 5 else 3) ∧ (RC S z).relIndex S ≤ 4 ∧
      (InducedPGL2 L₁ (SBar (S1 S z) z) q ∧ InducedPGL2 L₂ (SBar (S1 S z) z) q)

@[expose] def NoFAutBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (k : Kind), Cen2 G z S →
    Stage1Data G z S k → (k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) →
    ∀ K₁ K₂ : Subgroup G, Std4 G z S K₁ K₂ →
    (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) →
      ∀ s ∈ S, ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 →
        InducesFAut s K → s ∈ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def NoFAutBridgeR1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (k : Kind), Cen2 G z S →
    Stage1Data G z S k → (k = Kind.g2 ∨ k = Kind.psp4 ∨ ∃ ε : Bool, k = Kind.l4 ε) →
    ∀ K₀ : Subgroup G, Std6r1 G z S K₀ → G2Concl G z S K₀ →
    (∀ K : Subgroup G, IsRigidRankOneComp z K → Cond6a S K) →
      ∀ s ∈ S, ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K = 1 →
        InducesFAut s K → s ∈ centralizerSection K (pPrimeCoreOf 2 K)

@[expose] def SporadicNoRank1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (n : ℕ), Cen2 G z S → 8 ≤ n →
    Stage1Sporadic G z S n →
      ∀ K : Subgroup G, IsPCompIn 2 (centralizer ({z} : Set G)) K → pRank 2 ↥K ≠ 1

end CFSG.GH74.GLS.Stage1.Main
