module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def P47FieldCase : Prop :=
  ∀ (G : Type) [Group G] (z : G) (k : Kind), E4Facts G z k →
    ∀ (Y : Type) [Group Y] [Finite Y] (b : Y), SecOfG G z Y b →
    ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ (K : Subgroup Y) [K.Normal], ⁅K, K⁆ = K →
    ∀ (F : Type) [Field F] [Finite F], (∃ n : ℕ, 1 ≤ n ∧ Nat.card F = p ^ n) →
    ∀ (φ : ↥K →* projectiveSL 3 F), Function.Surjective φ → φ.ker = Subgroup.center ↥K →
      Odd (Nat.card ↥(Subgroup.center ↥K)) → b ∈ K →
    ∀ (e : Y), e * e = 1 → e ≠ 1 → (∀ x : ↥K, e * (x : Y) * e⁻¹ ∈ K) → e * b = b * e →
    ∀ (α : MulAut (projectiveSL 3 F)),
      (∀ (x : ↥K) (hx : e * (x : Y) * e⁻¹ ∈ K), α (φ x) = φ ⟨e * (x : Y) * e⁻¹, hx⟩) →
    ∀ (A : GL (Fin 3) F) (σ : F ≃+* F), σ ≠ 1 → α = conjAut 3 F A * fieldAut 3 F σ → False

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
