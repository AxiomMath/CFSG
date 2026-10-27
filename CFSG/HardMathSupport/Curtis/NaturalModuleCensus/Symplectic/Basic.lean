module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {r : ℕ} {K : Type} [Field K]

abbrev spMat (g : StatedSp r K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem spMat_mul (g h : StatedSp r K) : spMat (g * h) = spMat g * spMat h := rfl

theorem spMat_one : spMat (1 : StatedSp r K) = 1 := rfl

theorem spMat_mul_inv (g : StatedSp r K) : spMat g * spMat g⁻¹ = 1 := by
  rw [← spMat_mul, mul_inv_cancel]; rfl

theorem spMat_inv_mul (g : StatedSp r K) : spMat g⁻¹ * spMat g = 1 := by
  rw [← spMat_mul, inv_mul_cancel]; rfl

theorem spMat_pow (g : StatedSp r K) (n : ℕ) : spMat (g ^ n) = spMat g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, spMat_mul, ih, pow_succ]

theorem spMat_injective : Function.Injective (spMat (r := r) (K := K)) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem pairedSympForm_spMat_mulVec (g : StatedSp r K) (u v : Fin r ⊕ Fin r → K) :
    pairedSympForm K r (spMat g *ᵥ u) (spMat g *ᵥ v) = pairedSympForm K r u v :=
  SymplecticHigher.pairedSympForm_mulVec g u v

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
