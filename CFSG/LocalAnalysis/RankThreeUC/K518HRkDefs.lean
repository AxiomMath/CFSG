module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

@[expose] def K518RkSL2 : Prop :=
  ∀ (F : Type) [Field F] [Finite F], ringChar F = 2 → ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
    ℓ ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) →
    ∀ ψ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F), (∃ k : ℕ, orderOf ψ = ℓ ^ k) →
      ψ ∉ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) F →*
        MulAut (Matrix.SpecialLinearGroup (Fin 2) F)).range →
      2 ≤ CFSG.Open.pRank ℓ ((MulAut.conj : Matrix.SpecialLinearGroup (Fin 2) F →*
        MulAut (Matrix.SpecialLinearGroup (Fin 2) F)).range ⊔ Subgroup.zpowers ψ)

@[expose] def K518RkSU3 : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f : ℕ), 1 ≤ f → Nat.card F = (2 ^ f) ^ 2 →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 →
    ℓ ∣ Nat.card ↥(CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 3) →
    ∀ ψ : MulAut ↥(CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 3),
      (∃ k : ℕ, orderOf ψ = ℓ ^ k) →
      ψ ∉ (MulAut.conj : ↥(CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 3)
        →* MulAut _).range →
      2 ≤ CFSG.Open.pRank ℓ ((MulAut.conj :
        ↥(CFSG.LieType.Universal.Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) 3) →* MulAut _).range ⊔
          Subgroup.zpowers ψ)

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H

end
