module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools Subgroup

@[expose] def IsGomiAtom {G : Type} [Group G] (L U A : Subgroup G) : Prop :=
  L ⊓ normalizer (U : Set G) < A ∧ A ≤ L ∧
    ∀ Q : Subgroup G, L ⊓ normalizer (U : Set G) < Q → Q ≤ A → Q = A

@[expose] def GomiChevBorelTits : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsGomiChevTwo L → CFSG.LieType.BorelTits.Holds L 2

@[expose] def GomiChevAtomGeneration : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U Q : Subgroup G), IsGomiChevTwo ↥L → IsSylowOf 2 U L →
    L ⊓ normalizer (U : Set G) ≤ Q → Q ≤ L →
    Q ≤ L ⊓ normalizer (U : Set G) ⊔ sSup {A | IsGomiAtom L U A ∧ A ≤ Q}

@[expose] def GomiChevAtomOrbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U T A : Subgroup G), IsGomiChevTwo ↥L → IsSylowOf 2 U L →
    IsPGroup 2 T → T ≤ normalizer (L : Set G) → T ≤ normalizer (U : Set G) → IsGomiAtom L U A →
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, A.map (MulAut.conj t₁).toMonoidHom = A ∨
      A.map (MulAut.conj t₂).toMonoidHom = A ∨
      A.map (MulAut.conj t₁).toMonoidHom = A.map (MulAut.conj t₂).toMonoidHom

@[expose] def GomiChevRadical : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U P : Subgroup G), IsGomiChevTwo ↥L → IsSylowOf 2 U L →
    L ⊓ normalizer (U : Set G) ≤ P → P < L →
    pCoreOf 2 P ≠ ⊥ ∧
      twoResidual (L ⊓ centralizer (pCoreOf 2 P : Set G)) ≤ L ⊓ centralizer (L : Set G)

@[expose] def GomiChevSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U A : Subgroup G), IsGomiChevTwo ↥L → IsSylowOf 2 U L →
    IsGomiAtom L U A → ∀ g ∈ normalizer (L : Set G) ⊓ normalizer (U : Set G),
    A.map (MulAut.conj g).toMonoidHom ≠ A → A ⊔ A.map (MulAut.conj g).toMonoidHom = L →
    IsGomiL3 (↥L ⧸ center ↥L) ∨ IsGomiSp4 (↥L ⧸ center ↥L)

@[expose] def GomiChevLevi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U H : Subgroup G), IsGomiChevTwo ↥L → IsSylowOf 2 U L →
    IsPGroup 2 H → H ≤ normalizer (L : Set G) → H ≤ normalizer (U : Set G) →
    L ⊓ normalizer (U : Set G) < L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
    L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) < L →
    pCoreOf 2 (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) = H ⊓ L →
    IsPIsolatedOver 2 (L ⊓ normalizer (H : Set G)) (H ⊓ L) →
    IsGomiAtom L U (L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G)) ∨
      ∀ A : Subgroup G, IsGomiAtom L U A → A ≤ L ⊓ normalizer ((H ⊓ L : Subgroup G) : Set G) →
        ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≠ A

end CFSG.GroupTheory
