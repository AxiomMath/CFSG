module

public import CFSG.ClassicalInvolution.Asc77.WP2Stand
public import CFSG.ClassicalInvolution.Asc77.Lemma310

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

@[expose] def PartIHyp {G : Type} [Group G] (Ω : Set (Subgroup G)) : Prop :=
  p ≠ 2 ∧ 5 ≤ p ^ f ∧ HypOmegaMod p f Ω ∧ ∀ J ∈ Ω, AEmpty Ω J

variable {p f}

@[expose] def DbarAdj {G : Type} [Group G] (Ω : Set (Subgroup G)) (W R T : Subgroup G) : Prop :=
  T ∈ DSet Ω W ∧ (DComm W R T ∨ (T ≤ R ⊔ W ⊔ OCW W ∧ R ≤ T ⊔ W ⊔ OCW W))

@[expose] def DbarConnected {G : Type} [Group G] (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop :=
  ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, Relation.ReflTransGen (DbarAdj Ω W) R T

variable (p f)

@[expose] def L7_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W

@[expose] def L7_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → ∀ a ∈ Subgroup.normalizer (W : Set G), a * a = 1 →
      ∃ R ∈ DSet Ω W, conjSub a R = R

@[expose] def L7_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ K ∈ Ω, dComp Ω K = dstarComp Ω K ∨
      ∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W

@[expose] def L9_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ U ∈ USet Ω, U ≤ K → ¬ U ≤ oTwoCore (Subgroup.centralizer ({z} : Set G))

@[expose] def L9_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      ∀ S : Subgroup G, IsSylow2In S (Subgroup.centralizer ({z} : Set G)) →
        ∀ U : Subgroup G, U ≤ S → IsElemAbelian2 U 2 → ∀ d ∈ U, d ≠ 1 →
          gamma1 U (S ⊓ ⨆ L ∈ twinSet Ω K, L) ≤ Subgroup.centralizer ({d} : Set G) →
            ∃ x ∈ K, orderOf x = 4 ∧ x * d = d * x

@[expose] def L17_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand p f Ω K → ∀ S : Sylow 2 G, ∀ A : Subgroup G, A ≤ (S : Subgroup G) → A ≠ ⊥ →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → ¬ StronglyClosedIn A (S : Subgroup G)

end CFSG.ClassicalInvolution.Asc77
