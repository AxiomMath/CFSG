module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusField
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotRoots

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.TwistedE6Pilot
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)
open CFSG.ClassicalInvolution.Upgrade (map_statedOmega map_statedOmega_conj fieldIsoOfCard
  irreducible_map statedQuadMinus_comp)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Transport

variable {k₁ k₂ : Type} [Field k₁] [Field k₂]

theorem minusShearMat_map' (ε : k₁ ≃+* k₂) (s : k₁) :
    (minusShearMat s).map ε = minusShearMat (ε s) := by
  ext i j
  simp only [minusShearMat, minusShearE, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp

variable [CharP k₁ 2] [CharP k₂ 2]

theorem glCongr_minusShear (ε : k₁ ≃+* k₂) (s : k₁) :
    glCongr ε (minusShear s) = minusShear (ε s) :=
  Units.ext (minusShearMat_map' ε s)

end Transport

section Scale

variable {k : Type} [Field k]

@[expose] def minusScaleMat (d : k) :
    Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  Matrix.diagonal fun i => if i = Sum.inr (Sum.inr 1) then d else 1

theorem minusScaleMat_mul (d e : k) :
    minusScaleMat d * minusScaleMat e = minusScaleMat (d * e) := by
  rw [minusScaleMat, minusScaleMat, minusScaleMat, diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem minusScaleMat_one : minusScaleMat (1 : k) = 1 := by
  rw [minusScaleMat]
  simp

@[expose] def minusScale {d : k} (hd : d ≠ 0) : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k :=
  ⟨minusScaleMat d, minusScaleMat d⁻¹, by rw [minusScaleMat_mul, mul_inv_cancel₀ hd,
    minusScaleMat_one], by rw [minusScaleMat_mul, inv_mul_cancel₀ hd, minusScaleMat_one]⟩

theorem statedQuadMinus_minusScale {b c : k} (hb : b ≠ 0)
    (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → k) :
    StatedQuadMinus 4 k 1 (c / b ^ 2)
        (((minusScale hb : GL (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) :
          Matrix (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) k) *ᵥ v) =
      StatedQuadMinus 4 k b c v := by
  change StatedQuadMinus 4 k 1 (c / b ^ 2) (minusScaleMat b *ᵥ v) = _
  have e : ∀ i, (minusScaleMat b *ᵥ v) i = (if i = Sum.inr (Sum.inr 1) then b else 1) * v i :=
    fun i => by rw [minusScaleMat, mulVec_diagonal]
  simp only [StatedQuadMinus, e]
  simp
  field_simp

theorem minusScaleMat_mul_minusShearMat (b : k) :
    minusScaleMat b * minusShearMat b = minusShearMat 1 * minusScaleMat b := by
  ext i j
  rw [minusScaleMat, Matrix.diagonal_mul, Matrix.mul_diagonal, minusShearMat, minusShearMat,
    minusShearE, minusShearE, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst hij
    have : ¬(Sum.inr (Sum.inr 0) = i ∧ Sum.inr (Sum.inr 1) = i) := fun ⟨h1, h2⟩ => by
      rw [← h2] at h1
      simp at h1
    simp [this]
  · by_cases hu : Sum.inr (Sum.inr 0) = i ∧ Sum.inr (Sum.inr 1) = j
    · obtain ⟨rfl, rfl⟩ := hu
      simp
    · simp [hij, hu]

end Scale

end CFSG.SeitzReduction.F4Pilot
