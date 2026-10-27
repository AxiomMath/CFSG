module

public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow
public import CFSG.LocalAnalysis.SignalizerFunctor.RelativeWeakClosure

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped MatrixGroups

variable {X : Type} [Group X]

@[expose] def oTwoPrime (H : Subgroup X) : Subgroup X :=
  Subgroup.closure {x | x ∈ H ∧ ∃ k : ℕ, x ^ (2 ^ k) = 1}

@[expose] def centerOf (P : Subgroup X) : Subgroup X :=
  P ⊓ Subgroup.centralizer (P : Set X)

@[expose] def frattiniOf (P : Subgroup X) : Subgroup X :=
  (frattini P).map P.subtype

@[expose] def IsDihedralTwoGroup (P : Subgroup X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))

@[expose] def IsQuaternionTwoGroup (P : Subgroup X) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))

@[expose] def IsSemidihedralTwoGroup (P : Subgroup X) : Prop :=
  ∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)

@[expose] def IsWreathedTwoGroup (P : Subgroup X) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* WreathedTwoGroup n)

structure Hyp3 (Q T P S : Subgroup X) : Prop where
  ne_bot : T ≠ ⊥
  sylowFrame : SylowFrame Q T S
  sylow_P : IsSylowOf 2 T P
  le_sup : P ≤ Q ⊔ T
  tightlyEmbedded : TightlyEmbedded (P.subgroupOf (Q ⊔ T))
  index_le : T.relIndex (S ⊓ Subgroup.normalizer (T : Set X)) ≤ Nat.card T
  oddCore_eq_bot : CFSG.oddCore Q = ⊥

@[expose] def Thm3Conclusion (Q T S : Subgroup X) : Prop :=
  (IsCyclic T ∧
      (IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
        IsDihedralTwoGroup (S ⊓ Q)) ∧
      (IsDihedralTwoGroup S ∨ IsSemidihedralTwoGroup S ∨ IsWreathedTwoGroup S)) ∨
  Q ⊔ T ≤ Subgroup.normalizer (T : Set X) ∨
  (∃ n : ℕ, 2 ≤ n ∧
      oTwoPrime (Q ⊔ T) = pCoreOf 2 (Q ⊔ T) ⊔ oTwoPrime Q ∧
      pCoreOf 2 (Q ⊔ T) ⊓ oTwoPrime Q = ⊥ ∧ ⁅pCoreOf 2 (Q ⊔ T), oTwoPrime Q⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (Q ⊔ T)) ∧ Nat.card (pCoreOf 2 (Q ⊔ T)) = 2 ^ n ∧
      Nonempty (oTwoPrime Q ≃* PSL(2, GaloisField 2 n))) ∨
  (∃ x ∈ Q, relativeWeakClosure Q T S = T ⊔ rightConjugate T x ∧
      T ⊓ rightConjugate T x = ⊥ ∧ ⁅T, rightConjugate T x⁆ = ⊥ ∧
      relativeWeakClosure Q T S = S ⊓ Subgroup.normalizer (T : Set X) ∧
      Q ⊔ T ≤ Subgroup.normalizer (relativeWeakClosure Q T S : Set X) ∧
      IsMulCommutative T ∧
      (QuotientRankTwo S (relativeWeakClosure Q T S) → omegaOne T = T)) ∨
  (Q ⊔ T ≤ Subgroup.normalizer (relativeWeakClosure Q T S : Set X) ∧
      Nat.card (relativeWeakClosure Q T S) = Nat.card T ^ 3 ∧
      centerOf (relativeWeakClosure Q T S) =
        ⁅relativeWeakClosure Q T S, relativeWeakClosure Q T S⁆ ∧
      centerOf (relativeWeakClosure Q T S) = frattiniOf (relativeWeakClosure Q T S) ∧
      Nonempty (centerOf (relativeWeakClosure Q T S) ≃* T) ∧
      omegaOne T = T ∧
      (relativeWeakClosure Q T S).relIndex S = 2)

@[expose] def Theorem3Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Q T P S : Subgroup X), Hyp3 Q T P S → Thm3Conclusion Q T S

@[expose] def conjugateClosure (G T : Subgroup X) : Subgroup X :=
  ⨆ g : G, rightConjugate T g

@[expose] def IsBenderType (B : Subgroup X) (n : ℕ) : Prop :=
  (2 ≤ n ∧ Nonempty (B ≃* PSL(2, GaloisField 2 n))) ∨
  (∃ m : ℕ, 1 ≤ m ∧ n = 2 * m + 1 ∧ Nonempty (B ≃* Sz m)) ∨
  (2 ≤ n ∧ Nonempty (B ≃* PSU3 2 n))

@[expose] def Lemma46Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X) (g : X),
    SylowFrame G T S → Hyp43 G T Q H → T ≠ ⊥ → CFSG.oddCore G = ⊥ → g ∈ G →
    relativeWeakClosure G T S = T ⊔ rightConjugate T g →
    rightConjugate T g ≤ Subgroup.normalizer (T : Set X) →
    pRank 2 T = 1 ∨
    G ⊔ T ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) ∨
    (∃ n : ℕ,
      conjugateClosure G T = pCoreOf 2 (conjugateClosure G T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (conjugateClosure G T) ⊓ ⁅T, G⁆ = ⊥ ∧
      ⁅pCoreOf 2 (conjugateClosure G T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (conjugateClosure G T)) ∧
      Nat.card (pCoreOf 2 (conjugateClosure G T)) = 2 ^ n ∧
      IsBenderType ⁅T, G⁆ n)

@[expose] def Lemma47Conclusion (G T S : Subgroup X) : Prop :=
  relativeWeakClosure G T S = T ∨
  (IsCyclic T ∧ (IsWreathedTwoGroup S ∨ IsDihedralTwoGroup S ∨ IsSemidihedralTwoGroup S)) ∨
  (∃ g ∈ G, relativeWeakClosure G T S = T ⊔ rightConjugate T g ∧
      T ⊓ rightConjugate T g = ⊥ ∧ ⁅T, rightConjugate T g⁆ = ⊥ ∧
      IsMulCommutative (relativeWeakClosure G T S)) ∨
  (IsElemAbelian 2 T ∧ Nat.card (relativeWeakClosure G T S) = Nat.card T ^ 3 ∧
      centerOf (relativeWeakClosure G T S) =
        ⁅relativeWeakClosure G T S, relativeWeakClosure G T S⁆ ∧
      centerOf (relativeWeakClosure G T S) = frattiniOf (relativeWeakClosure G T S) ∧
      (relativeWeakClosure G T S).relIndex S = 2)

@[expose] def Theorem48Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (G T S Q H : Subgroup X),
    SylowFrame G T S → Hyp43 G T Q H → T.relIndex (S ⊓ H) ≤ Nat.card T →
    CFSG.oddCore G = ⊥ → 1 < pRank 2 T →
    G ≤ Subgroup.normalizer (relativeWeakClosure G T S : Set X) ∨
    (∃ n : ℕ, 2 ≤ n ∧
      oTwoPrime (G ⊔ T) = pCoreOf 2 (G ⊔ T) ⊔ ⁅T, G⁆ ∧
      pCoreOf 2 (G ⊔ T) ⊓ ⁅T, G⁆ = ⊥ ∧ ⁅pCoreOf 2 (G ⊔ T), ⁅T, G⁆⁆ = ⊥ ∧
      IsElemAbelian 2 (pCoreOf 2 (G ⊔ T)) ∧ Nat.card (pCoreOf 2 (G ⊔ T)) = 2 ^ n ∧
      Nonempty ((⁅T, G⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n)))

@[expose] def Lemma49Statement : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (G T S Q H A : Subgroup X),
    SylowFrame G T S → Hyp43 G T Q H → T ≠ ⊥ → Group.IsSolvable Q →
    Layer.subgroup G = ⊤ → IsComponentOf A G → T ≤ Subgroup.normalizer (A : Set X) →
    1 < pRank 2 Q → ¬ A ≤ H →
    pRank 2 (centerOf A ⊓ Subgroup.centralizer (T : Set X)) ≤ pRank 2 T →
    ∃ a ∈ A, (∃ k : ℕ, a ^ (2 ^ k) = 1) ∧ a ∈ Subgroup.centralizer (T : Set X) ∧
      a ∉ centerOf A

end CFSG.ComponentClassification.AschbacherTheorem3
