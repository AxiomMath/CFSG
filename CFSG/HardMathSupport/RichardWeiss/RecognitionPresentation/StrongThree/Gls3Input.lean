module

public import CFSG.Open.Defs
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti

@[expose] def gammaCore (p k : ℕ) {X : Type*} [Group X] [Finite X] (A P : Subgroup X) :
    Subgroup X :=
  Subgroup.closure {x | x ∈ A ∧ ∃ R : Subgroup X, R ≤ P ∧ k ≤ CFSG.Open.pRank p R ∧
    x ∈ Subgroup.normalizer (R : Set X)}

@[expose] def Gls3Conclusion (X : Type) [Group X] [Finite X] (K Q : Subgroup X) : Prop :=
  gammaCore 3 1 K Q < K ∧
  (∀ H : Subgroup X, gammaCore 3 1 K Q < H → H ≤ K → H = K) ∧
  (
  (((∃ q : PrimePower, q.p = 3 ∧ (IsoLie ↥K (.A 1 q) ∨ IsoLie ↥K (.twistedA 2 q))) ∨
      ∃ m : ℕ, IsoLie ↥K (.reeG2 m)) ∧
    gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) ∧
    ∃ J : Subgroup X, IsCyclic ↥J ∧ gammaCore 3 1 K Q = Q ⊔ J) ∨
  (IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) ∧ IsCyclic ↥Q ∧ Nat.card ↥Q = 9 ∧
    gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) ∧
    Nonempty (↥(gammaCore 3 1 K Q) ≃* DihedralGroup 9)) ∨
  (∃ φ : ↥K ≃* alternatingGroup (Fin 6), ∃ A : Finset (Fin 6), A.card = 3 ∧
    ∀ k : ↥K, (k : X) ∈ gammaCore 3 1 K Q ↔
      (A.image (φ k : Equiv.Perm (Fin 6)) = A ∨ A.image (φ k : Equiv.Perm (Fin 6)) = Aᶜ)) ∨
  (IsoLie ↥K (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩) ∧ IsElemAbelian 3 Q ∧ Nat.card ↥Q = 9 ∧
    gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) ∧
    ∃ S : Subgroup X, S ≤ gammaCore 3 1 K Q ∧ Q ⊓ S = ⊥ ∧ Q ⊔ S = gammaCore 3 1 K Q ∧
      Nonempty (↥S ≃* QuaternionGroup 2)) ∨
  (Nonempty (↥K ≃* (CFSGIndex.sporadic SporadicName.M11).Group) ∧
    gammaCore 3 1 K Q = K ⊓ Subgroup.normalizer (Q : Set X) ∧
    ∃ S : Subgroup X, S ≤ gammaCore 3 1 K Q ∧ Q ⊔ S = gammaCore 3 1 K Q ∧
      Nat.card ↥S = 16 ∧ (∃ a ∈ S, ∃ b ∈ S, orderOf a = 8 ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ 3 ∧ S = Subgroup.closure {a, b}) ∧
      S ⊓ Subgroup.centralizer (Q : Set X) = ⊥))

@[expose] def Gls3StronglyThreeEmbedded : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ K : Subgroup X, K.Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
      Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ P : Sylow 3 X, 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) →
        gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ →
          Gls3Conclusion X K ((P : Subgroup X) ⊓ K)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
