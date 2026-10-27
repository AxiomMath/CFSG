module

public import CFSG.ClassicalInvolution.Asc77.AscCX9X6
public import CFSG.ClassicalInvolution.Asc77.AscCX9Z1
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4
public import CFSG.ClassicalInvolution.Phan.Frames.BlockStab

public noncomputable section

namespace CFSG.ClassicalInvolution.Asc77.CX.MF2U

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.CX.MF2L (spForm spM mem_spM d0GL coe_d0GL coe_d0GL_inv
  d0_mem_spM)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem d0_mul_d0 : (diagonal ![-1, 1, 1, 1] : Matrix (Fin 4) (Fin 4) K) *
    diagonal ![-1, 1, 1, 1] = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  fin_cases k <;> simp

theorem conjTr_d0 : conjTr σ (diagonal ![-1, 1, 1, 1] : Matrix (Fin 4) (Fin 4) K) =
    diagonal ![-1, 1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, diagonal]

theorem d0_conj_mem (x : SUid σ 4) : d0GL * (x : GL (Fin 4) K) * d0GL⁻¹ ∈ SUid σ 4 := by
  have hval : ((d0GL * (x : GL (Fin 4) K) * d0GL⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      diagonal ![-1, 1, 1, 1] * suMat x * diagonal ![-1, 1, 1, 1] := by
    rw [Units.val_mul, Units.val_mul, coe_d0GL_inv, coe_d0GL]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hval, det_mul, det_mul, det_suMat, mul_one, ← det_mul, d0_mul_d0, det_one]
  · rw [hval, conjTr_mul, conjTr_mul, conjTr_d0]
    have hx : conjTr σ (suMat x) * suMat x = 1 := x.2.2
    calc diagonal ![-1, 1, 1, 1] * (conjTr σ (suMat x) * diagonal ![-1, 1, 1, 1]) *
          (diagonal ![-1, 1, 1, 1] * suMat x * diagonal ![-1, 1, 1, 1])
        = diagonal ![-1, 1, 1, 1] * (conjTr σ (suMat x) *
            (diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1]) * suMat x) *
              diagonal ![-1, 1, 1, 1] := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [d0_mul_d0, Matrix.mul_one, hx, Matrix.mul_one, d0_mul_d0]

@[expose] def d0Hom : SUid σ 4 →* SUid σ 4 :=
  ((MulAut.conj (d0GL : GL (Fin 4) K)).toMonoidHom.comp (SUid σ 4).subtype).codRestrict _
    d0_conj_mem

theorem suMat_d0Hom (x : SUid σ 4) :
    suMat (d0Hom x) = diagonal ![-1, 1, 1, 1] * suMat x * diagonal ![-1, 1, 1, 1] := by
  show ((d0GL * (x : GL (Fin 4) K) * d0GL⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = _
  rw [Units.val_mul, Units.val_mul, coe_d0GL_inv, coe_d0GL]
  rfl

theorem d0Hom_d0Hom (x : SUid σ 4) : d0Hom (d0Hom x) = x :=
  suMat_injective (by
    rw [suMat_d0Hom, suMat_d0Hom]
    calc diagonal ![-1, 1, 1, 1] * (diagonal ![-1, 1, 1, 1] * suMat x * diagonal ![-1, 1, 1, 1]) *
          diagonal ![-1, 1, 1, 1]
        = (diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1]) * suMat x *
            (diagonal ![-1, 1, 1, 1] * diagonal ![-1, 1, 1, 1]) := by simp only [Matrix.mul_assoc]
      _ = suMat x := by rw [d0_mul_d0, Matrix.one_mul, Matrix.mul_one])

@[expose] def d0SU : MulAut (SUid σ 4) :=
  MonoidHom.toMulEquiv d0Hom d0Hom (MonoidHom.ext d0Hom_d0Hom) (MonoidHom.ext d0Hom_d0Hom)

theorem suMat_d0SU (x : SUid σ 4) :
    suMat (d0SU x) = diagonal ![-1, 1, 1, 1] * suMat x * diagonal ![-1, 1, 1, 1] :=
  suMat_d0Hom x

theorem d0SU_d0SU (x : SUid σ 4) : d0SU (d0SU x) = x :=
  d0Hom_d0Hom x

theorem suToSL_d0SU (x : SUid σ 4) :
    suToSL σ 4 (d0SU x) = slConjugation 4 K d0GL (suToSL σ 4 x) := by
  apply Subtype.ext
  rw [coe_suToSL, suMat_d0SU, slConjugation_matrix, coe_d0GL_inv]
  rfl

theorem map_d0SU_spU (m n : K) :
    (spU (σ := σ) (spForm m n)).map d0SU.toMonoidHom = spU (spForm (-m) n) := by
  have h : ∀ {m' n' : K} {x : SUid σ 4}, x ∈ spU (spForm m' n') → d0SU x ∈ spU (spForm (-m') n') :=
    fun hx => by
      show suToSL σ 4 (d0SU _) ∈ spM _
      rw [suToSL_d0SU]
      exact d0_mem_spM hx
  refine le_antisymm (by rintro _ ⟨x, hx, rfl⟩; exact h hx) fun x hx => ?_
  have hx' := h hx
  rw [neg_neg] at hx'
  exact ⟨_, hx', d0SU_d0SU x⟩

section Blocks

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem d0_mulVec_single {l : Fin 4} (hl : l ≠ 0) :
    (diagonal ![-1, 1, 1, 1] : Matrix (Fin 4) (Fin 4) K) *ᵥ Pi.single l 1 = Pi.single l 1 := by
  funext a
  fin_cases l <;> fin_cases a <;> simp_all [Matrix.mulVec_diagonal]

theorem d0SU_mem_block0 {x : Su K p f 4} (hx : x ∈ (blockEmb K p f 4 2 0 (by norm_num)).range) :
    d0SU x ∈ (blockEmb K p f 4 2 0 (by norm_num)).range := by
  rw [mem_range_blockEmb_iff] at hx ⊢
  intro l hl
  have hl0 : l ≠ 0 := fun h => hl (by rw [h]; simp)
  have hx' := hx l hl
  rw [suMat_smul] at hx' ⊢
  rw [suMat_d0SU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d0_mulVec_single hl0, hx',
    d0_mulVec_single hl0]

theorem map_d0SU_block0 :
    (blockEmb K p f 4 2 0 (by norm_num)).range.map (d0SU : MulAut (Su K p f 4)).toMonoidHom =
      (blockEmb K p f 4 2 0 (by norm_num)).range := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact d0SU_mem_block0 hx
  · intro x hx
    refine ⟨d0SU x, d0SU_mem_block0 hx, ?_⟩
    exact d0SU_d0SU x

theorem d0SU_block2 (B : Su K p f 2) :
    d0SU (blockEmb K p f 4 2 2 (by norm_num) B) = blockEmb K p f 4 2 2 (by norm_num) B := by
  apply suMat_injective
  rw [suMat_d0SU, CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4.suMat_blockEmb_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

variable {Y : Type} [Group Y] (θ : Su K p f 4 →* Y) (hθ : Function.Surjective θ)
  (hker : θ.ker = Subgroup.center (Su K p f 4))

@[expose] def cHatU : Y ≃* Y :=
  (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm.trans
    ((QuotientGroup.congr θ.ker θ.ker d0SU (by
      rw [hker]
      exact Subgroup.characteristic_iff_map_eq.mp inferInstance d0SU)).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ))

theorem cHatU_apply (x : Su K p f 4) : cHatU θ hθ hker (θ x) = θ (d0SU x) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective θ hθ).symm (θ x) =
      (x : Su K p f 4 ⧸ θ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [cHatU, MulEquiv.trans_apply, h1, QuotientGroup.congr_mk]
  rfl

theorem map_cHatU (H : Subgroup (Su K p f 4)) :
    (H.map θ).map (cHatU θ hθ hker).toMonoidHom = (H.map d0SU.toMonoidHom).map θ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  exact cHatU_apply θ hθ hker x

end Blocks

end CFSG.ClassicalInvolution.Asc77.CX.MF2U
