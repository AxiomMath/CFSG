module

public import CFSG.Open.FusionDefs
public import CFSG.Assembly.Defs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

open scoped MatrixGroups

variable {G : Type*} [Group G]

@[expose] def CharTwo (H : Subgroup G) : Prop :=
  H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H

@[expose] def IsSylowTwoOf (S H : Subgroup G) : Prop :=
  S ≤ H ∧ IsPGroup 2 S ∧ ¬ 2 ∣ (S.subgroupOf H).index

@[expose] def oddCoreIn (H : Subgroup G) : Subgroup G :=
  (fusionOddCore H).map H.subtype

@[expose] def IsAGMember (T D : Subgroup G) : Prop :=
  D ≤ T ∧ D ≠ ⊥ ∧
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (D : Set G)) (Subgroup.normalizer (D : Set G)) ∧
    let N := Subgroup.normalizer (D : Set G)
    let R := oddCoreIn N
    (∀ Q : Subgroup G, R ≤ Q → Q ≤ N → (Q.subgroupOf N).Normal →
        (∀ x ∈ Q, ∃ k : ℕ, x ^ 2 ^ k ∈ R) → Q ≤ R ⊔ D) ∧
      Subgroup.centralizer (D : Set G) ≤ R ⊔ D ∧
      R ≤ Subgroup.centralizer (D : Set G) ∧ R ⊓ D = ⊥

@[expose] def IsEscaping (M D : Subgroup G) : Prop :=
  D ≤ M ∧ D ≠ ⊥ ∧ IsPGroup 2 D ∧ CharTwo (Subgroup.normalizer (D : Set G)) ∧
    ¬ Subgroup.normalizer (D : Set G) ≤ M

@[expose] def IsConfining (M U : Subgroup G) : Prop :=
  U ≤ M ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
    (∀ V : Subgroup G, IsPGroup 2 V → U ≤ V → V ≤ M → Subgroup.normalizer (V : Set G) ≤ M) ∧
    pCoreOf 2 M ⊓ Subgroup.centralizer (U : Set G) ≤ U

@[expose] def IsWitnessPair (M U HU : Subgroup G) : Prop :=
  IsConfining M U ∧ U ≤ HU ∧ pCoreOf 2 HU ≠ ⊥ ∧ CharTwo HU ∧ ¬ HU ≤ M

@[expose] def IsWitness (M U : Subgroup G) : Prop :=
  ∃ HU : Subgroup G, IsWitnessPair M U HU

@[expose] def IsGamma (M H : Subgroup G) : Prop :=
  pCoreOf 2 H ≠ ⊥ ∧ ∃ U HU : Subgroup G, IsWitnessPair M U HU ∧ HU ≤ H

@[expose] def IsGammaTop (M H : Subgroup G) : Prop :=
  pCoreOf 2 H ≠ ⊥ ∧ ∃ U HU : Subgroup G, IsWitnessPair M U HU ∧ HU ≤ H ∧
    ∀ V : Subgroup G, IsWitness M V → Nat.card V ≤ Nat.card U

@[expose] noncomputable def twoPart (X : Subgroup G) : ℕ :=
  2 ^ (Nat.card X).factorization 2

@[expose] def IsGammaU (M H : Subgroup G) : Prop :=
  IsGammaTop M H ∧ ∀ K : Subgroup G, IsGammaTop M K → twoPart K ≤ twoPart H

@[expose] def IsGamma2 (M H : Subgroup G) : Prop :=
  IsGamma M H ∧ ∀ K : Subgroup G, IsGamma M K → twoPart K ≤ twoPart H

@[expose] def IsGamma0 (M H : Subgroup G) : Prop :=
  IsGammaU M H ∨ IsGamma2 M H

@[expose] def UniqueSmallModel (X : Type*) [Group X] : Prop :=
  (∃ p : ℕ, p.Prime ∧ 7 < p ∧
      ((∃ k : ℕ, p = 2 ^ 2 ^ k + 1) ∨ (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k - 1)) ∧
      Nonempty (X ≃* PSL(2, ZMod p))) ∨
    Nonempty (X ≃* PSL(3, ZMod 3)) ∨
    Nonempty (X ≃* M11)

end CFSG.QuasithinUnique
