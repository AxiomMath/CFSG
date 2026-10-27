module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData

public noncomputable section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (flagStabilizer)

variable {K : Type} [Field K]

theorem psf_eq_zero_of_inr_eq_zero {x y : Fin 2 ⊕ Fin 2 → K} (hx : ∀ j, x (Sum.inr j) = 0)
    (hy : ∀ j, y (Sum.inr j) = 0) : pairedSympForm K 2 x y = 0 := by
  rw [pairedSympForm_apply]
  have h1 : (x ∘ Sum.inr : Fin 2 → K) = 0 := funext hx
  have h2 : (y ∘ Sum.inr : Fin 2 → K) = 0 := funext hy
  rw [h1, h2]; simp

theorem mulVec_inr_eq_zero_of_mem {g : StatedSp 2 K} (hg : g ∈ flagStabilizer 2 K {2})
    {x : Fin 2 ⊕ Fin 2 → K} (hx : ∀ j, x (Sum.inr j) = 0) (j : Fin 2) :
    (spMat g *ᵥ x) (Sum.inr j) = 0 := by
  have hg := SymplecticHigher.mem_flagStabilizer.1 hg 2 (Set.mem_singleton 2)
  have hx' : x ∈ SymplecticFlag.flag 2 K 2 :=
    (SymplecticFlag.mem_flag_of_le le_rfl).2
      (SymplecticFlag.mem_isoFlag.2 ⟨hx, fun j hj => absurd j.2 (by omega)⟩)
  have h : spMat g *ᵥ x ∈ (SymplecticFlag.flag 2 K 2).map
      (mulVecLin ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :=
    ⟨x, hx', rfl⟩
  rw [SymplecticFlag.mem_stabilizer.1 hg] at h
  exact (SymplecticFlag.mem_isoFlag.1 ((SymplecticFlag.mem_flag_of_le le_rfl).1 h)).1 j

theorem toBlocks₂₁_eq_zero_of_mem {g : StatedSp 2 K} (hg : g ∈ flagStabilizer 2 K {2}) :
    (spMat g).toBlocks₂₁ = 0 := by
  ext i j
  have h := mulVec_inr_eq_zero_of_mem hg (x := Pi.single (Sum.inl j) 1)
    (fun j' => by simp) i
  rw [mulVec_single_one, col_apply] at h
  simpa [toBlocks₂₁] using h

theorem spMat_eq_fromBlocks_of_mem {g : StatedSp 2 K} (hg : g ∈ flagStabilizer 2 K {2}) :
    spMat g = fromBlocks (spMat g).toBlocks₁₁ (spMat g).toBlocks₁₂ 0 (spMat g).toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks (spMat g), toBlocks₂₁_eq_zero_of_mem hg]

@[expose] def blockA : ↥(flagStabilizer 2 K {2}) →* Matrix (Fin 2) (Fin 2) K where
  toFun g := (spMat g.1).toBlocks₁₁
  map_one' := by
    simp only [Subgroup.coe_one, spMat_one]
    ext i j; simp [toBlocks₁₁, Matrix.one_apply]
  map_mul' g h := by
    have hg := spMat_eq_fromBlocks_of_mem g.2
    have hh := spMat_eq_fromBlocks_of_mem h.2
    have : spMat (g.1 * h.1) = spMat g.1 * spMat h.1 := spMat_mul _ _
    rw [Subgroup.coe_mul, this, hg, hh, fromBlocks_multiply]
    simp

theorem blockA_apply (g : ↥(flagStabilizer 2 K {2})) :
    blockA g = (spMat g.1).toBlocks₁₁ := rfl

theorem spMat_mulVec_elim_zero (g : ↥(flagStabilizer 2 K {2})) (u : Fin 2 → K) :
    spMat g.1 *ᵥ (Sum.elim u 0 : Fin 2 ⊕ Fin 2 → K) = Sum.elim (blockA g *ᵥ u) 0 := by
  rw [spMat_eq_fromBlocks_of_mem g.2, fromBlocks_mulVec]
  simp [blockA_apply]

@[expose] def blockDet : ↥(flagStabilizer 2 K {2}) →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp (blockA (K := K)).toHomUnits

theorem blockDet_apply (g : ↥(flagStabilizer 2 K {2})) :
    ((blockDet g : Kˣ) : K) = (blockA g).det := by
  simp [blockDet]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic
