module

public import CFSG.Open.GLADefs
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def IsL2TwoPowOdd (L : Type*) [Group L] : Prop :=
  ∃ n : ℕ, Odd n ∧ 1 < n ∧
    Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))

@[expose] def I112 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsElemAbelian p B → GLATwoLocalRank p X ≤ pRank p B →
      ∀ L : Subgroup X, GLAPComponent p ⊤ L → ¬ B ≤ Subgroup.normalizer (L : Set X) →
        p = 3 ∧ (Subgroup.normalizer (L : Set X)).relIndex B = 3 ∧
          (Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) ≠ ⊥ ∨
            IsL2TwoPowOdd (↥L ⧸ GLAPPrimeCore p ↥L))

@[expose] def Kernel11_3a : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ B : Subgroup X, GLAIsBmax 3 B →
    ∀ L : Subgroup X, GLAPComponent 3 ⊤ L → ¬ B ≤ Subgroup.normalizer (L : Set X) →
      (Subgroup.normalizer (L : Set X)).relIndex B = 3 →
        ¬ IsL2TwoPowOdd (↥L ⧸ GLAPPrimeCore 3 ↥L)

@[expose] def innerAut113 (L : Type*) [Group L] : Subgroup (MulAut L) :=
  (MulAut.conj : L →* MulAut L).range

structure Tables113 : Prop where
  T0 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L →
    2 ∣ Nat.card L ∧ 3 ∣ Nat.card L ∧ Subgroup.center L = ⊥
  T2 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ H : Subgroup (MulAut L),
    IsElemAbelian 3 H → Nat.card H ≤ 9 ∧ Nat.card ↥(H ⊓ innerAut113 L) ≤ 3
  T3 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ H S : Subgroup (MulAut L),
    IsElemAbelian 3 H → IsPGroup 2 S → S ≠ ⊥ → H ≤ Subgroup.normalizer (S : Set (MulAut L)) →
      Nat.card H ≤ 3 ∧ H ⊓ innerAut113 L = ⊥
  T4 : ∀ (L : Type) [Group L] [Finite L], IsL2TwoPowOdd L → ∀ α : MulAut L, orderOf α = 3 →
    α ∉ innerAut113 L → (∃ y : L, orderOf y = 3 ∧ α y = y) ∧
      ∃ S : Subgroup L, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S.map α.toMonoidHom = S

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
