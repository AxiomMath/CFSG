module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Defs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open Matrix
open scoped MatrixGroups

section Vocabulary

variable {G : Type} [Group G]

@[expose] def InducesSym (N : Subgroup G) (P : Set (Subgroup G)) : Prop :=
  ∀ σ : Equiv.Perm P, ∃ n ∈ N, ∀ Q : P, rightConjugate (Q : Subgroup G) n = (σ Q : Subgroup G)

@[expose] def iX (z : G) (X : Subgroup G) : Subgroup G :=
  AS76b.oUpperTwoPrime (centralizer ({z} : Set G) ⊓ normalizer (X : Set G))

end Vocabulary

structure Sec4Setting (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F : Subgroup G) : Prop where
  frame : Frame G A A R g E F
  type : TypeL34 (rankTwoQuot A)
  even : Even (Nat.card (center A))
  below : L34GeneralBelow (Nat.card G)
  top : rankTwoX A ⊔ R = ⊤

structure Sec4Q (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G)
    (z : G) : Prop where
  setting : Sec4Setting G A R g E F
  sylowN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))
  sylow : IsSylowOf 2 S₁ ⊤
  le : Q ≤ S₁
  extraspecial : CFSG.IsExtraspecialPGroup 2 Q
  card : Nat.card Q = 2 ^ 7
  order_z : orderOf z = 2
  center_Q : centerIn Q = zpowers z
  center_S₁ : centerIn S₁ = zpowers z
  unique : ∀ Q' : Subgroup G, Q' ≤ S₁ → CFSG.IsExtraspecialPGroup 2 Q' → Nat.card Q' = 2 ^ 7 →
    centerIn Q' = centerIn S₁ → Q' = Q
  normE : Q ≤ normalizer (E : Set G)
  normF : Q ≤ normalizer (F : Set G)
  quot : (∃ φ : ↥S₁ →* DihedralGroup 4, Function.Surjective φ ∧ φ.ker = Q.subgroupOf S₁) ∨
    ∃ φ : ↥S₁ →* DihedralGroup 8, Function.Surjective φ ∧ φ.ker = Q.subgroupOf S₁
  plus : ∃ U : Subgroup G, U ≤ Q ∧ IsElemAbelian 2 U ∧ Nat.card U = 16

@[expose] def Step43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4Setting G A R g E F →
    ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)) →
      IsSylowOf 2 S₁ ⊤

@[expose] def Step44ii : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4Setting G A R g E F →
      ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)) →
        (Nat.card S₁ = 2 ^ 10 ∧ ∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) ∨
        (Nat.card S₁ = 2 ^ 11 ∧
          ∃ (H : Type) (_ : Group H) (_ : Finite H) (K : Subgroup H), K.Normal ∧
            IsSporadic K .He ∧ K.index = 2 ∧ centralizer (K : Set H) = ⊥ ∧
            ∃ P : Sylow 2 H, Nonempty (S₁ ≃* P))

@[expose] def Step45 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F : Subgroup G),
    Sec4Setting G A R g E F →
    ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G)) →
      ((∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) ∨
        ∃ (H : Type) (_ : Group H) (_ : Finite H) (K : Subgroup H), K.Normal ∧
          IsSporadic K .He ∧ K.index = 2 ∧ centralizer (K : Set H) = ⊥ ∧
          ∃ P : Sylow 2 H, Nonempty (S₁ ≃* P)) ∧
      ∃ (Q : Subgroup G) (z : G), Sec4Q G A R g E F S₁ Q z

@[expose] def Step46 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      (∀ X ∈ ({E, F} : Set (Subgroup G)),
        X ≤ iX z X ∧
        (∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
          Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X)) ∧
        ¬ iX z X ≤ normalizer (R : Set G) ∧
        Nat.card (Q ⊓ X : Subgroup G) = 16) ∧
      iX z E ⊔ iX z F ≤ normalizer (Q : Set G)

@[expose] def Step47 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      (Q ≤ iX z E ⊔ iX z F ∧
        ∃ φ : ↥(iX z E ⊔ iX z F) →* GL (Fin 3) (ZMod 2),
          Function.Surjective φ ∧
          φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf (iX z E ⊔ iX z F)) ∧
      (∃ V₁ V₂ : Subgroup G, V₁ ≤ Q ∧ V₂ ≤ Q ∧ IsElemAbelian 2 V₁ ∧ IsElemAbelian 2 V₂ ∧
        Nat.card V₁ = 16 ∧ Nat.card V₂ = 16 ∧ V₁ ⊓ V₂ = zpowers z ∧ V₁ ⊔ V₂ = Q ∧
        iX z E ⊔ iX z F ≤ normalizer (V₁ : Set G) ∧ iX z E ⊔ iX z F ≤ normalizer (V₂ : Set G) ∧
        ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)), ∀ W : Subgroup G, zpowers z ≤ W → W ≤ V →
          iX z E ⊔ iX z F ≤ normalizer (W : Set G) → W = zpowers z ∨ W = V) ∧
      ((∃ φ : ↥(normalizer (Q : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
          φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf
            (normalizer (Q : Set G))) ∨
        ∃ φ : ↥(normalizer (Q : Set G)) →* ProjGenLinGroup (Fin 2) (ZMod 7),
          Function.Surjective φ ∧
          φ.ker = (Q ⊔ AS76b.oddCoreIn (normalizer (Q : Set G))).subgroupOf
            (normalizer (Q : Set G)))

@[expose] def Step48 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      ∀ x ∈ Q, ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * x * h ∈ S₁ → h⁻¹ * x * h ∈ Q

@[expose] def Step49 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      (CFSG.generalizedFitting ↥(centralizer ({z} : Set G))).map
          (centralizer ({z} : Set G)).subtype = Q ∧
      ((∃ φ : ↥(centralizer ({z} : Set G)) →* ProjGenLinGroup (Fin 2) (ZMod 7),
          Function.Surjective φ ∧ φ.ker = Q.subgroupOf (centralizer ({z} : Set G))) ∨
        IsSporadic (rankTwoX A) .He)

@[expose] def Step410 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4Q G A R g E F S₁ Q z →
      (∃ φ : ↥(centralizer ({z} : Set G)) →* ProjGenLinGroup (Fin 2) (ZMod 7),
          Function.Surjective φ ∧ φ.ker = Q.subgroupOf (centralizer ({z} : Set G))) →
      ∃ N : Subgroup G, N.Normal ∧ N.index = 2

end CFSG.ComponentClassification.AS81
