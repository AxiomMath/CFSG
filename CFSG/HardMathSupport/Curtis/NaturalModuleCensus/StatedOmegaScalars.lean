module

public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg CFSG.LieType.BorelTits Matrix

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem eq_one_of_mem_statedScalars_statedQuadMinus_omega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 2 ≤ n) {A : StatedOmega (StatedQuadMinus n F b c)}
    (hA : (A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) ∈
      StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) : A = 1 := by
  obtain ⟨u, hu⟩ := hA
  have hQ := preserves_of_mem_statedOmega (Q₀ := StatedQuadMinus n F b c) A.2
  have h0 : 0 < n - 1 := by omega
  set v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F :=
    Pi.single (.inl ⟨0, h0⟩) 1 + Pi.single (.inr (.inl ⟨0, h0⟩)) 1 with hvdef
  have hv : StatedQuadMinus n F b c v = 1 := by
    simp [hvdef, StatedQuadMinus, Pi.single_apply]
  have hAv : ((A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :
      Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) *ᵥ v =
      (u : F) • v := by
    rw [← hu]
    funext i
    simp [Matrix.mulVec_diagonal, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hu2 : (u : F) * u = 1 := by
    have h1 := hQ v
    have hs := (quadMinusForm n F b c hirr).Q_smul (u : F) v
    change StatedQuadMinus n F b c ((u : F) • v) = (u : F) ^ 2 * StatedQuadMinus n F b c v at hs
    rw [hAv, hs, hv] at h1
    linear_combination h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hu1 : (u : F) = 1 := by
    have : ((u : F) - 1) * ((u : F) - 1) = 0 := by linear_combination hu2 + (1 - (u : F)) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  apply Subtype.ext
  rw [OneMemClass.coe_one, ← hu, show u = 1 from Units.ext hu1, map_one]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
