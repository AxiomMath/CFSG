module

public import CFSG.CGT.PushingUpLit.CGT6.Embedding
public import CFSG.CGT.PushingUpLit.CGT6.Props

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open CFSG.CGT.PushingUpLit.BHS
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement

abbrev HolOf {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAbelian 2 V) : Type :=
  @Hol ↥V (commGroupOfElemAbelian hV)

instance {G : Type} [Group G] [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Finite (HolOf hV) :=
  @instFiniteHol ↥V (commGroupOfElemAbelian hV) inferInstance

@[expose] noncomputable def yuHolOf {G : Type} [Group G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (Y : Subgroup (MulAut ↥V)) : Subgroup (HolOf hV) :=
  @yuHol ↥V (commGroupOfElemAbelian hV) Y

@[expose] def EmbDictPlus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G) [V.Normal] (hV : IsElemAbelian 2 V),
    InClassX ↥A → V ≤ Subgroup.normalizer (A : Set G) → ⁅V, A⁆ = ⁅oTwoIn A, A⁆ →
      InClassX ↥(yuHolOf hV (autOn A V))

@[expose] def EmbDictMinus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G) [V.Normal] (hV : IsElemAbelian 2 V),
    V ≤ Subgroup.normalizer (A : Set G) →
    IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G)) → oResidualTwo ↥A = ⊤ →
    generalizedFitting ↥A = pCore 2 ↥A →
    ⁅A ⊓ Subgroup.centralizer (V : Set G), A⁆ ≤ ⁅V, A⁆ →
    InClassX ↥(yuHolOf hV (autOn A V)) → InClassX ↥A ∧ ⁅oTwoIn A, A⁆ = ⁅V, A⁆

@[expose] def EmbDictArrow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V Y X : Subgroup G) [V.Normal] (hV : IsElemAbelian 2 V),
    Y ≤ X → InClassX ↥Y → InClassX ↥X →
    V ≤ Subgroup.normalizer (Y : Set G) → ⁅V, Y⁆ = ⁅oTwoIn Y, Y⁆ →
    V ≤ Subgroup.normalizer (X : Set G) → ⁅V, X⁆ = ⁅oTwoIn X, X⁆ →
    IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) →
    yuHolOf hV (autOn Y V) ≠ yuHolOf hV (autOn X V) →
    ArrowNat (yuHolOf hV (autOn Y V)) (yuHolOf hV (autOn X V)) → ArrowNat Y X

@[expose] def EmbOmega : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X Y : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n →
      (IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥ ∨
        IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥) →
      Y ≤ X → Y ≠ X → Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) →
      Nat.card ↥(commV Y) = 2 ^ (3 * n) →
        (∀ N : Subgroup (MulAut V), Y ≤ N → N ≤ X → (N.subgroupOf X).Normal → N = X) ∧
          ¬ (Y.subgroupOf X).IsSubnormal

end CFSG.CGT.PushingUpLit.CGT6
