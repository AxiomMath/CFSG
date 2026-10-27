module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Thm24OneUse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeUse
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rec36
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78LitHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Lemma15Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FS79Thm13Guarded

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def Sol78JunctionAt (H : Type) [Group H] [Finite H] : Prop :=
  CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H), FStarSimple N → ∀ K M : Subgroup H,
    InL K → InL M → Lt K M → K ≠ M →
      ¬ Nonempty ((↥K ⧸ center ↥K) ≃* alternatingGroup (Fin 7)) →
      (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (↥K ⧸ center ↥K) .PSL 2 p f) →
        ∃ (m : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H), 1 ≤ m ∧ Sol78Chain23 H M m L T s ∧
          L 0 = K ∧ (∀ i, 1 ≤ i → i ≤ m → T i ≠ ⊥) ∧ (K ≤ M → ∀ i, 1 ≤ i → i ≤ m → L i ≤ M)

@[expose] def Sol78Remark11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.oddCore G = ⊥ → ∀ A : Subgroup G, SolStd A →
    Even (Nat.card ↥(center ↥A)) →
      (IsSporadic (↥A ⧸ center ↥A) .Suz ∨ IsSporadic (↥A ⧸ center ↥A) .ONan ∨
        IsSporadic (↥A ⧸ center ↥A) .HN ∨ IsSporadic (↥A ⧸ center ↥A) .Ru ∨
        IsSporadic (↥A ⧸ center ↥A) .Co1) → A.Normal

structure Sol78LitCore : Prop where
  bthm : Sol78BThmHered
  fs79lemma15 : FS79Lemma15Hered
  thm24_1 : Sol78Thm24_1Use
  lemma25 : Finkelstein77.Asc76Lemma25
  thm24_3 : ∀ s' ∈ Sol78Rows, Hyp.Thm24ThreeUse s'
  thm24_3Simple : Hyp.Thm24ThreeSimpleInputs
  thm46 : Sol78Thm46FSHered
  thm412 : Sol78Thm412FSHered
  hyp12Lie : Sol78Hyp12LieHered
  fs79thm13 : FS79Thm13UseHered

structure Sol78Lit : Prop extends Sol78LitCore where
  thm21 : Sol78Thm21Hered
  cor23 : Sol78Cor23SHered
  thm22 : Sol78Thm22Hered

structure Hyp31FourA (H : Type) [Group H] [Finite H] (N : Subgroup H) (IsK : GroupClass) :
    Prop where
  four_a : ∀ K₁ L₁ : Subgroup H, InL K₁ → Maximal L₁ → Lt K₁ L₁ → K₁ ≤ L₁ →
    IsK (↥K₁ ⧸ CFSG.oddCore ↥K₁) → ∀ N₀ : Subgroup H, CanLoc K₁ N₀ →
      ¬ IsSectionOf ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ↥(lam L₁ N₀) ∧
      ∀ (K₂ : Type) [Group K₂] [Finite K₂], Group.IsPerfect K₂ →
        Nonempty ((K₂ ⧸ center K₂) ≃* (↥K₁ ⧸ center ↥K₁)) → NoFixedEmbeds K₂ ↥(lam L₁ N₀)

@[expose] def Lemma33Two (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H] : Prop :=
  Sol78Lit → Balance.UHered H → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    ∀ (N : Subgroup H) (n : ℕ) (L T : ℕ → Subgroup H) (s : ℕ → H),
      Hyp31 H N IsK IsL → Hyp31FourA H N IsK → Sol78Chain23 H N n L T s → IsK ↥(L 0) → 2 ≤ n →
        (∀ m, IsKChain IsK N m → m ≤ n) →
          ∀ M : Subgroup H, InL M → Lt (L (n - 2)) M → M ≠ L (n - 2) → IsL ↥M

@[expose] def TwoSylowStd (S : List TauCeti.SporadicName) : Prop :=
  ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (N M : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover s M → SolStd M →
      (∃ P : Sylow 2 (centralizer (M : Set H)), IsCyclic ↥P) →
        ∀ P : Sylow 2 (centralizer (M : Set H)), Nat.card P = 2

structure Stage3Row (S : List TauCeti.SporadicName) (Q : TauCeti.SporadicName → PairClass) :
    Type 1 where
  IsK : GroupClass
  m : TauCeti.SporadicName → ℕ
  rec36 : ∀ s ∈ S, Rec36 S s (Q s) (m s)
  outTwo : OutTwoCovers S
  hyp31Row : Hyp31Row IsK (IsLS S)
  rowIsK : ∀ s ∈ S, ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L →
    Q s H L K u → IsK ↥K
  rowExists : ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (L : Subgroup H), OddCover s L →
    ∃ (K : Subgroup H) (u : H), Q s H L K u
  rowFit : ∀ s ∈ S, ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H), OddCover s L → K ≤ L →
    CFSG.IsQuasisimple ↥K → IsK (↥K ⧸ CFSG.oddCore ↥K) → SolStd (K.subgroupOf L) →
      twoAdic (autCentralizer L K) ≤ 2 → ∃ u : H, Q s H L K u
  inOrTwoSylow :
    (∀ s ∈ S, ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), OddCover s L → Q s H L K u →
      u ∈ K) ∨
    TwoSylowStd S

end CFSG.EvenSporadicStandard.Induction
