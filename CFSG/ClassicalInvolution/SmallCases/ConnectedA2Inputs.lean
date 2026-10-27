module

public import CFSG.ClassicalInvolution.SmallCases.LocalDatum
public import CFSG.ClassicalInvolution.SmallCases.LocalDatumUnitary
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureDefs

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable (p f : ℕ) [Fact p.Prime]

structure Branch {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonabelian : ∃ x y : G, x * y ≠ y * x
  odd : p ≠ 2
  five : 5 ≤ p ^ f
  below : CITBelowU p f (Nat.card G)
  member : IsClassicalMember p f K z
  rank : 3 ≤ CFSG.Open.twoRank G
  notFourGenerated : ¬ TwoSubgroupsFourGenerated G
  connected : CFSG.ClassicalInvolution.DeltaConnected K
  noBoot : ¬ BootData p f (conjClass K)
  a2 : A2Configuration z K

omit [Fact p.Prime] in
theorem smallConnectedA2_iff [Fact p.Prime] :
    SmallConnectedA2 p f ↔ ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
      (K : Subgroup G) (z : G), Branch p f K z →
      CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  constructor
  · intro h G _ _ _ K z hb
    exact h G hb.nonabelian hb.odd hb.five hb.below K z hb.member hb.rank hb.notFourGenerated
      hb.connected hb.noBoot hb.a2
  · intro h G _ _ _ hnab hp2 hq hBelow K z hz h3 h4 hΔ hB hA2
    exact h G K z ⟨hnab, hp2, hq, hBelow, hz, h3, h4, hΔ, hB, hA2⟩

@[expose] def HasDatum {G : Type} [Group G] [Finite G] (K : Subgroup G) : Prop :=
  ∃ (L₁ L₂ : Subgroup G) (t : G), L₁ ∈ conjClass K ∧ L₂ ∈ conjClass K ∧
    (LocalDatum (GaloisField p f) L₁ L₂ t ∨ LocalDatumU (GaloisField p (2 * f)) p f L₁ L₂ t)

structure RankThreeFrameFacts {G : Type} [Group G] (F : Type) [Field F] (Ω : Set (Subgroup G))
    (A : Subgroup G) (S : Set (Subgroup G)) : Prop where
  single : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
    SingleClassComponents p f D
  fibre : FibreLE2 S
  injective : ∀ K ∈ S, ∀ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) →
    axisSub A K = axisSub A L → K = L
  pairs : (∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K) ∨
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀) (_ : CharP K₀ p), Nat.card K₀ = (p ^ f) ^ 2 ∧
      ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
        Commutes P Q ∨ UnitaryA2Pair K₀ p f A P Q ∨ UnitaryA2Pair K₀ p f A Q P

@[expose] def A2Datum : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K

@[expose] def FrameP1 {G : Type} [Group G] (Ω : Set (Subgroup G)) (A : Subgroup G) : Prop :=
  ∀ x ∈ A, x ≠ 1 → LocalOddCentral Ω {x}

@[expose] def A2P1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A

@[expose] def A2FrameFacts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A → RankThreeFrameFacts p f F (conjClass K) A S

@[expose] def A2OrthEndpoint : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    Branch p f K z → HasDatum p f K →
      ∀ (F : Type) [Field F], Nat.card F = p ^ f →
        ∀ (A : Subgroup G) (S : Set (Subgroup G)), RankFrame F (conjClass K) A S →
          Nat.card A = 8 → (∃ K' ∈ S, ∃ L' ∈ S, K' ≠ L' ∧ ¬ Commutes K' L') →
          FrameP1 (conjClass K) A → RankThreeFrameFacts p f F (conjClass K) A S →
          ¬ (∀ a ∈ A, IsFrameInvolution p f S a → FrameGenerationModO (conjClass K) S a) →
          CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11

structure ConnectedA2Inputs : Prop where
  datum : A2Datum p f
  p1 : A2P1 p f
  frame : A2FrameFacts p f
  orth : A2OrthEndpoint p f

end CFSG.ClassicalInvolution.ConnectedA2
