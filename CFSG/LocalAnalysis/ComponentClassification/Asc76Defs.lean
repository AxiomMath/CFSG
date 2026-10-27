module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.Open.FusionDefs
public import CFSG.Fischer.Uniq.Graph
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.Asc76

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def SylowNormalizes (J K : Subgroup G) : Prop :=
  ∃ S : Subgroup G, IsSylowOf 2 S J ∧ S ≤ normalizer (K : Set G)

@[expose] def IsSzOrU3 (X : Type*) [Group X] : Prop :=
  (∃ a : ℕ, 1 ≤ a ∧ Nonempty (X ≃* Sz a)) ∨ ∃ f : ℕ, 2 ≤ f ∧ Nonempty (X ≃* PSU3 2 f)

@[expose] def Asc76Theorem1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), TightlyEmbedded K →
    normalClosure (K : Set G) = ⊤ → oUpperTwoPrime K = K → standardComponentOddCore G = ⊥ →
    (∀ g : G, Even (Nat.card (rightConjugate K g ⊓ normalizer (K : Set G) : Subgroup G)) →
      SylowNormalizes (rightConjugate K g) K) →
    ∀ R : Subgroup G, IsSylowOf 2 R K → 1 < Open.pRank 2 R →
      K = ⊤ ∨ IsElemAbelian 2 R ∨ (IsSzOrU3 G ∧ fusionStronglyEmbedded (normalizer (K : Set G)))

@[expose] def Asc76Theorem3Conclusion (K R : Subgroup G) : Prop :=
  K.Normal ∨
    ((Nonempty (G ≃* PSU3 2 2) ∨ Nonempty (G ≃* PSL(2, ZMod 7)) ∨
        Nonempty (G ≃* alternatingGroup (Fin 5)) ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (G ≃* alternatingGroup (Fin 7))) ∧
      Nat.card R = 4 ∧ (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set G))) ∨
    ∃ U : Subgroup G, U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2 ∧
      IsMulCommutative (normalClosure (U : Set G))

@[expose] def Asc76Theorem3Large : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), TightlyEmbedded K →
    normalClosure (K : Set G) = ⊤ → standardComponentOddCore G = ⊥ →
    ∀ R : Subgroup G, IsSylowOf 2 R K → IsDihedralTwoGroup R → 4 < Nat.card R →
      Asc76Theorem3Conclusion K R

@[expose] def Asc76Theorem3Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), TightlyEmbedded K →
    normalClosure (K : Set G) = ⊤ → standardComponentOddCore G = ⊥ →
    ∀ R : Subgroup G, IsSylowOf 2 R K → IsDihedralTwoGroup R → Nat.card R = 4 →
      (∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ R ≤ S ∧
        ∀ g : G, rightConjugate R g ≤ S → rightConjugate R g = R) →
      Asc76Theorem3Conclusion K R

structure Sec3Setting [Finite G] (Ω : Set (Subgroup G)) : Prop where
  oddCore : standardComponentOddCore G = ⊥
  conj_mem : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω
  generates : sSup Ω = ⊤
  sylow : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    Even (Nat.card (J ⊓ normalizer (K : Set G) : Subgroup G)) → SylowNormalizes J K
  rank : ∀ K ∈ Ω, ∀ R : Subgroup G, IsSylowOf 2 R K → 1 < Open.pRank 2 R ∧ ¬ IsElemAbelian 2 R
  twoPart : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    (Nat.card K).factorization 2 = (Nat.card J).factorization 2 ∧
      Odd (Nat.card (K ⊓ J : Subgroup G))
  perfect : ∀ K ∈ Ω, oUpperTwoPrime K = K

@[expose] def Asc76Theorem4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Sec3Setting Ω → ∀ K ∈ Ω,
    (∀ J ∈ Ω, (∀ g : G, J ≠ rightConjugate K g) → ⁅K, J⁆ = ⊥) ∧
      (K.Normal ∨ (IsSzOrU3 (normalClosure (K : Set G)) ∧
        ∀ R : Subgroup G, IsSylowOf 2 R K → IsSylowOf 2 R (normalClosure (K : Set G))))

structure Assumption41 (Ω : Set (Subgroup G)) : Prop where
  oddCore : standardComponentOddCore G = ⊥
  conj_mem : ∀ K ∈ Ω, ∀ g : G, rightConjugate K g ∈ Ω
  generates : sSup Ω = ⊤
  twoPart : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J →
    (Nat.card K).factorization 2 = (Nat.card J).factorization 2
  inter : ∀ K ∈ Ω, ∀ J ∈ Ω, K ≠ J → Odd (Nat.card (K ⊓ J : Subgroup G))
  perfect : ∀ K ∈ Ω, oUpperTwoPrime K = K
  dihedral : ∀ K ∈ Ω, ∀ R : Subgroup G, IsSylowOf 2 R K →
    IsDihedralTwoGroup R ∧ ¬ IsMulCommutative R

@[expose] def sec4W (Ω : Set (Subgroup G)) (S : Subgroup G) : Subgroup G :=
  ⨆ (U : Subgroup G) (_ : U ≤ S)
    (_ : ∃ K ∈ Ω, ∃ R : Subgroup G, IsSylowOf 2 R K ∧ U ≤ R ∧ IsCyclic U ∧ U.relIndex R = 2), U

@[expose] def Asc76Theorem5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Assumption41 Ω →
    ∀ S : Subgroup G, IsSylowOf 2 S ⊤ →
      (∃ K ∈ Ω, K.Normal) ∨
        ((sec4W Ω S).Normal ∧
          (∀ K ∈ Ω, (centralizer (sec4W Ω S : Set G)).relIndex K = 2) ∧
          ∀ K ∈ Ω, ∀ J ∈ Ω, ∀ k ∈ K, ∀ j ∈ J, k ∉ centralizer (sec4W Ω S : Set G) →
            j ∉ centralizer (sec4W Ω S : Set G) →
            (k * j) ^ 2 ∈ centralizer (sec4W Ω S : Set G) ∨
              (k * j) ^ 3 ∈ centralizer (sec4W Ω S : Set G))

@[expose] def Asc76Theorem5Printed : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Assumption41 Ω →
    ∀ S : Subgroup G, IsSylowOf 2 S ⊤ →
      (∃ K ∈ Ω, ¬ Group.IsSolvable K ∧ K.Normal) ∨
        ((sec4W Ω S).Normal ∧
          (∀ K ∈ Ω, (centralizer (sec4W Ω S : Set G)).relIndex K = 2) ∧
          ∀ K ∈ Ω, ∀ J ∈ Ω, ∀ k ∈ K, ∀ j ∈ J, k ∉ centralizer (sec4W Ω S : Set G) →
            j ∉ centralizer (sec4W Ω S : Set G) →
            (k * j) ^ 2 ∈ centralizer (sec4W Ω S : Set G) ∨
              (k * j) ^ 3 ∈ centralizer (sec4W Ω S : Set G))

@[expose] def Asc76Lemma22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K J T R : Subgroup G), TightlyEmbedded K →
    TightlyEmbedded J → Odd (Nat.card (K ⊓ J : Subgroup G)) →
    (Nat.card K).factorization 2 = (Nat.card J).factorization 2 →
    IsSylowOf 2 T (J ⊓ normalizer (K : Set G)) → T ≠ ⊥ → IsSylowOf 2 R K →
    T ≤ normalizer (R : Set G) → 1 < Open.pRank 2 K → 1 < Open.pRank 2 J →
    let W : Subgroup G := ⨆ (k : G) (_ : k ∈ K) (_ : rightConjugate T k ≤ R ⊔ T),
      rightConjugate T k
    let NRT : Subgroup G := R ⊓ normalizer (T : Set G)
    (Nat.card NRT = Nat.card T ∧ (Nat.card T < Nat.card R → Nonempty (NRT ≃* T))) ∧
    (T ≠ W → IsCyclic T → IsDihedralTwoGroup R ∧
      (IsDihedralTwoGroup (R ⊔ T) ∨ IsWreathedTwoGroup (R ⊔ T))) ∧
    (NormalIn (W ⊔ oddCoreIn K) (K ⊔ T) ∨
      (∃ n : ℕ, 2 ≤ n ∧ ∃ φ : oUpperTwoPrime (K ⊔ T) →*
          Multiplicative (Fin n → ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n),
        Function.Surjective φ ∧ φ.ker = (oddCoreIn K).subgroupOf (oUpperTwoPrime (K ⊔ T))) ∨
      IsCyclic T) ∧
    (IsSylowOf 2 T J → ⁅T, oUpperTwoPrime K⁆ ≤ oddCoreIn K ∨ IsElemAbelian 2 T) ∧
    (¬ IsSylowOf 2 T J → IsMulCommutative T) ∧
    (¬ IsElemAbelian 2 T → T ≠ W →
      W = T ⊔ NRT ∧
      (∀ E : Subgroup G, NRT ≤ E → E ≤ R → (∀ x ∈ E, x ^ 2 ∈ NRT) →
        (∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ NRT) → NRT.relIndex E ≤ 2) ∧
      ∀ r ∈ R, r ∉ NRT → r ^ 2 ∈ NRT → ∀ x ∈ NRT, r * x * r⁻¹ = x⁻¹) ∧
    (NRT.subgroupOf R).Normal

@[expose] def Asc76Lemma28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K₀ : Subgroup G),
    let Ω : Set (Subgroup G) := Set.range (rightConjugate K₀)
    let adj : Subgroup G → Subgroup G → Prop := fun K J => J ∈ Ω ∧ J ≠ K ∧
      J ≤ normalizer (K : Set G)
    sSup Ω = ⊤ → (∀ K ∈ Ω, ∀ J, adj K J → adj J K) →
    (∀ K ∈ Ω, ∀ J ∈ Ω, Relation.ReflTransGen adj K J) →
    (∀ K ∈ Ω, ∀ J L, adj K J → adj K L →
      adj L J ∨ ∃ x ∈ J ⊔ L, L = rightConjugate J x) →
    ∀ K ∈ Ω, ∀ π : Set (Subgroup G),
      let X : Subgroup G := ⨆ (J : Subgroup G) (_ : adj K J), J
      (∃ P, adj K P ∧ π = {Q | ∃ x ∈ X, Q = rightConjugate P x}) →
      (∀ P, adj K P → Set.ncard {Q | ∃ x ∈ X, Q = rightConjugate P x} ≤ π.ncard) →
      let α : Set (Subgroup G) := {M | M ∈ Ω ∧ ∀ P ∈ π, adj P M}
      (∀ P ∈ π, ∀ Q ∈ π, ∃ x ∈ (⨆ (P' : Subgroup G) (_ : P' ∈ π), P'),
        Q = rightConjugate P x) ∧
      (∀ g : G, (rightConjugate · g) '' α = α ∨ Disjoint ((rightConjugate · g) '' α) α) ∧
      ∀ P ∈ π, ∃ g : G, P ∈ (rightConjugate · g) '' α ∧ (rightConjugate · g) '' α ⊆ π

@[expose] def HallFusionThm32 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S T : Subgroup G), IsSylowOf 2 S ⊤ → T ≤ S →
    Nat.card T = 4 → IsElemAbelian 2 T →
    (∀ g : G, rightConjugate T g ≤ S → rightConjugate T g = T) →
    IsSylowOf 2 T (normalClosure (T : Set G)) ∨
      Nonempty (↥(normalClosure (T : Set G)) ⧸
          CFSG.Assembly.oddCore ↥(normalClosure (T : Set G)) ≃* PSU3 2 2) ∨
      ∀ P : Subgroup G, IsSylowOf 2 P (normalClosure (T : Set G)) →
        Nonempty (P ≃* DihedralGroup 4)

@[expose] def FischerDisconnectedPrinted : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D : Set X), (∀ d ∈ D, orderOf d = 2) →
    (∀ d ∈ D, ∀ x : X, x * d * x⁻¹ ∈ D) → (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3) →
    closure D = ⊤ → ¬ (CFSG.Fischer.commGraph D).Connected →
    (∀ d ∈ D, ∀ e ∈ D, IsConj d e) ∧
      ∃ (Y : Subgroup X) (_ : Y.Normal), Nonempty (X ⧸ Y ≃* Equiv.Perm (Fin 3)) ∧
        ∀ d ∈ D, (∀ e ∈ D, d⁻¹ * e ∈ Y → d * e = e * d) → Y = pCore 2 X

end CFSG.ComponentClassification.Asc76
