module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Nar24 : Prop :=
  ∀ (M : Type) [Group M] [Finite M], IsE 6 M →
    ∀ (H D : Subgroup (MulAut M)) (τ : MulAut M),
      IsSimpleGroup ↥H → (¬ ∀ x y : ↥H, x * y = y * x) → 2 ^ 6 ∣ Nat.card ↥H →
      D ≤ H → Nonempty (↥D ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) →
      (∀ x ∈ D, x ^ 7 = 1 → x ≠ 1 → ∀ m : M, x m = m → m = 1) →
      τ ^ 2 = 1 → (∀ d ∈ D, τ * d = d * τ) → (∀ h ∈ H, τ * h * τ⁻¹ ∈ H) →
      (∀ c ∈ H, c * τ = τ * c → ∀ d ∈ D, c * d * c⁻¹ ∈ D) → False

end CFSG.OddStandard.HigherRank.YamadaG23
