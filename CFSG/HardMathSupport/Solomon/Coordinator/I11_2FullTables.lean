module

public import CFSG.HardMathSupport.Solomon.LocalBalance.PartIInputs2
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Families

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def IsSLThreeWith (P : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), P (Nat.card K) ∧ Nonempty (X ≃* ↥(StatedSL 3 K))

@[expose] def IsSUThreeWith (P : ℕ → Prop) (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ P q ∧
    Nonempty (X ≃* ↥(StatedSU 3 q K))

@[expose] def IsHatGTwoThree (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    ∃ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.card = 3 ∧
      d.1 = TauCeti.LieTypeIndex.G2 q ∧
      Nonempty ((X ⧸ Subgroup.center X) ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsTenElevenOne (X : Type*) [Group X] : Prop :=
  IsHatSix X ∨ IsHatSeven X ∨ IsHatMTwentyTwo X ∨ IsSLThreeWith (fun q => q % 3 = 1) X ∨
    IsSUThreeWith (fun q => q % 3 = 2) X

@[expose] def IsThreeNine (X : Type*) [Group X] : Prop :=
  IsSLThreeWith (fun q => q % 9 = 1) X ∨ IsSUThreeWith (fun q => q % 9 = 8) X

structure Tables112Types : Prop where
  T10_11_2 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 →
      IsTenElevenOne K ∨ IsHatON K
  T10_11_3 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 → LieCentralQuotient K →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 →
      IsTenElevenOne K ∨ IsHatGTwoThree K
  T10_6_8 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → Nat.card (Subgroup.center K) = 3 →
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 4 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) = CFSG.Open.pRank 3 (⊤ : Subgroup K) + 1 →
      IsHatON K ∨ LieCentralQuotient K
  TON : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsHatON K →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K) ∧ 3 ≤ GLATwoLocalRank 3 K
  TG23 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsHatGTwoThree K →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≠ CFSG.Open.pRank 3 (⊤ : Subgroup K) + 1
  T10_6_1 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsThreeNine K → CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2
  T11_9 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsThreeNine K →
      ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧ P ≤ Subgroup.normalizer (T : Set K) ∧
        Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
        Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9))
  T11_9F : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsThreeNine K → ∀ H : Subgroup (MulAut K),
    CFSG.Open.IsElemAbelian 3 H → Nat.card H = 27 →
      ∃ ψ ∈ H, ¬ IsInnerAut ψ ∧ ∃ T P Q : Subgroup K, T ≠ ⊥ ∧ IsPGroup 2 T ∧
        P ≤ Subgroup.normalizer (T : Set K) ∧ Nonempty (P ≃* Multiplicative (ZMod 9)) ∧
        Nonempty (Q ≃* Multiplicative (ZMod 9 × ZMod 9)) ∧ P ≤ Q ∧
        T.map ψ.toMonoidHom = T ∧ ∃ k : ℕ, ∀ x ∈ Q, ψ x = x ^ k
  T10_10 : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K →
    IsHatMTwentyTwo K ∨ IsSLThreeWith (fun q => (q % 9 = 4 ∨ q % 9 = 7) ∧ q ≠ 4) K ∨
      IsSUThreeExc K →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≤ 2

end CFSG.HardMathSupport.Solomon.Coordinator
