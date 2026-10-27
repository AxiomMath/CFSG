module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveCore
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Four
public import CFSG.LieType.SeitzGeneration.HeisSmallModel

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree


@[expose] def E8FiveOneClosing : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K - 1 →
    ∀ E₀ : Subgroup (adjointGroup Tag.E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
      ∀ D : LangPlaneData Tag.E8 K E₀, (∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) → D.w ≠ 1 →
        planeCl E₀ = ⊤

@[expose] def E8FiveTwoClosing : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup Tag.E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
      ∀ D : LangPlaneData Tag.E8 K E₀, (∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) →
        (∃ u : Fin Tag.E8.rank → ℤ, D.w • u ≠ -u) → planeCl E₀ = ⊤

@[expose] def E8FiveTwoFrameDatum : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      ∀ w : WeylGroup Tag.E8, (∀ u : Fin Tag.E8.rank → ℤ, w • u = -u) →
        E8FrameDatumAt K (e8FrameGroup K) Fr w

@[expose] def E8FiveFourSquare : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 →
    ∀ E₀ : Subgroup (adjointGroup Tag.E8 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
      ∀ D : LangPlaneData Tag.E8 K E₀, (∀ α, IsRoot Tag.E8 α → ¬ D.Kills α) →
        ∀ u : Fin Tag.E8.rank → ℤ, D.w • (D.w • u) = -u

@[expose] def E8FiveFourFrameDatum : Prop :=
  ∀ (K : Type) [Field K] [Finite K], orderOf ((Nat.card K : ℕ) : ZMod 5) = 4 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      ∀ w : WeylGroup Tag.E8, (∀ u : Fin Tag.E8.rank → ℤ, w • (w • u) = -u) →
        E8FrameDatumAt K (e8D4Group K) Fr w

end CFSG.LieType.SeitzGeneration.ExcHigh
