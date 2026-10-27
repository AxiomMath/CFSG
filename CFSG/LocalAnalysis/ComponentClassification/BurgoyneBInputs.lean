module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.UnbalancingLocal CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

@[expose] def PropBHypII (L : Type) [Group L] [Finite L] (c : L) : Prop :=
  ∃ s : MulAut L, orderOf s = 2 ∧ ∃ Q : Subgroup L, Q ≤ autFixed s ∧
    IsPComponent 2 (Q.subgroupOf (autFixed s)) ∧
    (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
      Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p n))) ∧
    c ∈ center L ∧ c ∈ Q ∧ orderOf c = 2

@[expose] def PropBHyp (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal] (t : J)
    (Y : Subgroup J) (c : K ⧸ pPrimeCore 2 K) : Prop :=
  IsQuasisimple (K ⧸ pPrimeCore 2 K) ∧
    IsM4 (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range ∧
    orderOf (conjQuotAction K (pPrimeCore 2 K) t) = 2 ∧
    Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≠ ⊥ ∧
    Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≤
      oddCentralizerCore
        ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict t) ∧
    ∃ s : MulAut (K ⧸ pPrimeCore 2 K), orderOf s = 2 ∧
      s * conjQuotAction K (pPrimeCore 2 K) t = conjQuotAction K (pPrimeCore 2 K) t * s ∧
      (∀ y ∈ Y, s * conjQuotAction K (pPrimeCore 2 K) y = conjQuotAction K (pPrimeCore 2 K) y * s) ∧
      ∃ Q : Subgroup (K ⧸ pPrimeCore 2 K), Q ≤ autFixed s ∧
        IsPComponent 2 (Q.subgroupOf (autFixed s)) ∧
        (∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
          Nonempty (Q ⧸ pPrimeCore 2 Q ≃* SL(2, GaloisField p n))) ∧
        c ∈ center (K ⧸ pPrimeCore 2 K) ∧ c ∈ Q ∧ orderOf c = 2 ∧
        ActsProperlyVia (conjQuotAction K (pPrimeCore 2 K)) t Y Q ((pPrimeCore 2 Q).map Q.subtype)

@[expose] def BurgoynePropBSL4CoverInput : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ (L : Type) [Group L] [Finite L] (α : SL(4, F) →* L), Function.Surjective α →
      ∀ c : L, PropBHypII L c →
        ∀ g : SL(4, F), (g : Matrix (Fin 4) (Fin 4) F) = -1 → c = α g

@[expose] def BurgoynePropBSL4ExcInput : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (K : Subgroup J) [K.Normal] (t : J) (Y : Subgroup J)
    (c : K ⧸ pPrimeCore 2 K), PropBHyp J K t Y c →
    ∀ (F : Type) [Field F] [Finite F], ringChar F ≠ 2 →
    ∀ θ : GeneralizedFitting.subgroup (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range
      ≃* projectiveSL 4 F,
    ∀ A : GL (Fin 4) F,
      socleAction θ ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict t) =
        conjAut 4 F A →
    ∀ (H : GL (Fin 4) F) (J₀ : Finset (Fin 4)) (μ : Fˣ), Odd J₀.card →
      H * A * H⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 4) μ * PSL.signGL F J₀ → False

end CFSG.ComponentClassification.Burgoyne
