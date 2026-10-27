module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.Adapters.SpecialLinearPerfect

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K]

theorem exists_perfect_conj_escape [Finite K] (hK : 4 ≤ Nat.card K) (v g : StatedSp 2 K) (ζ : K)
    (hconj : spMat v * spMat g =
      spMat g * diagonal (Sum.elim (fun _ : Fin 2 => ζ) fun _ => ζ⁻¹)) :
    ∃ W : Subgroup (StatedSp 2 K), W ≤ Subgroup.centralizer ({v} : Set (StatedSp 2 K)) ∧
      ⁅W, W⁆ = W ∧ ∃ w ∈ W, spMat w *ᵥ (spMat g *ᵥ Pi.single (Sum.inl 0) 1) =
        spMat g *ᵥ Pi.single (Sum.inl 0) 1 + spMat g *ᵥ Pi.single (Sum.inl 1) 1 := by
  set ρ := SymplecticTorusWeyl.rho (r := 2) (k := K) 0 1 (by decide) with hρ
  set φ : Matrix.SpecialLinearGroup (Fin 2) K →* StatedSp 2 K :=
    (MulAut.conj g).toMonoidHom.comp ρ with hφ
  set D : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    diagonal (Sum.elim (fun _ : Fin 2 => ζ) fun _ => ζ⁻¹) with hD
  have hφmat : ∀ s, spMat (φ s) = spMat g * spMat (ρ s) * spMat g⁻¹ := by
    intro s
    simp [hφ, spMat_mul]
  have hRD : ∀ s, spMat (ρ s) * D = D * spMat (ρ s) := by
    intro s
    rw [hD, ← fromBlocks_diagonal]
    simp only [hρ, spMat, SymplecticTorusWeyl.coe_rho', fromBlocks_multiply]
    simp [← Matrix.smul_one_eq_diagonal]
  refine ⟨Subgroup.map φ ⊤, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply spMat_injective
    have hM : spMat h = spMat g * D * spMat g⁻¹ := by
      calc spMat h = spMat h * (spMat g * spMat g⁻¹) := by rw [spMat_mul_inv, mul_one]
        _ = (spMat h * spMat g) * spMat g⁻¹ := by rw [mul_assoc]
        _ = _ := by rw [hconj]
    rw [spMat_mul, spMat_mul, hφmat, hM]
    calc spMat g * D * spMat g⁻¹ * (spMat g * spMat (ρ s) * spMat g⁻¹)
        = spMat g * D * (spMat g⁻¹ * spMat g) * spMat (ρ s) * spMat g⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = spMat g * (spMat (ρ s) * D) * spMat g⁻¹ := by
          rw [spMat_inv_mul, hRD s]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = spMat g * spMat (ρ s) * (spMat g⁻¹ * spMat g) * D * spMat g⁻¹ := by
          rw [spMat_inv_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
    have htop : ⁅(⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)), ⊤⁆ = ⊤ :=
      Group.IsPerfect.commutator_eq_top
    rw [← Subgroup.map_commutator, htop]
  · let t : Matrix.SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    refine ⟨φ t, ⟨t, trivial, rfl⟩, ?_⟩
    have hR : spMat (ρ t) *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) =
        Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1 := by
      have hRm : spMat (ρ t) = fromBlocks (SymplecticTorusWeyl.pairMat (0 : Fin 2) 1
          (t : Matrix (Fin 2) (Fin 2) K)) 0 0 (SymplecticTorusWeyl.pairMat (0 : Fin 2) 1
          (((t⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))ᵀ) :=
        SymplecticTorusWeyl.coe_rho' _ t
      rw [mulVec_single_one, hRm]
      ext x
      rcases x with i | i <;> fin_cases i <;>
        simp [SymplecticTorusWeyl.pairMat, t]
    have hinv : spMat g⁻¹ *ᵥ (spMat g *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K)) =
        Pi.single (Sum.inl 0) 1 := by
      rw [mulVec_mulVec, spMat_inv_mul, one_mulVec]
    rw [hφmat, ← mulVec_mulVec, ← mulVec_mulVec, hinv, hR, mulVec_add]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
