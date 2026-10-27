module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuAlg
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4 (mem_sup_of_comm sup_le_normalizer_of_comm)
open CFSG.ClassicalInvolution.ModelFacts.Orth15 (SLayer isQuasisimple_of_equiv)
open scoped MatrixGroups

section Defs

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]

@[expose] noncomputable def R0 : Subgroup (Su K p f 4) :=
  (blockEmb K p f 4 2 0 (by norm_num)).range

@[expose] noncomputable def R0' : Subgroup (Su K p f 4) :=
  (blockEmb K p f 4 2 2 (by norm_num)).range

@[expose] noncomputable def x0 : Su K p f 4 := rootInvSU K p f (show 2 ≤ 4 by norm_num)

@[expose] noncomputable def blk (A B : Su K p f 2) : Su K p f 4 :=
  blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) B

@[expose] noncomputable def u0 : Su K p f 4 := blk K p f (jSU K p f) (jSU K p f)

@[expose] noncomputable def zneg : Su K p f 4 := blk K p f (negOneSU K p f) (negOneSU K p f)

@[expose] noncomputable def t0 : Su K p f 4 := x0 K p f * u0 K p f

end Defs

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem suMat_blk (A B : Su K p f 2) :
    suMat (blk K p f A B) = !![suMat A 0 0, suMat A 0 1, 0, 0; suMat A 1 0, suMat A 1 1, 0, 0;
      0, 0, suMat B 0 0, suMat B 0 1; 0, 0, suMat B 1 0, suMat B 1 1] := by
  rw [blk, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem blockEmb_comm (A B : Su K p f 2) :
    blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) B =
      blockEmb K p f 4 2 2 (by norm_num) B * blockEmb K p f 4 2 0 (by norm_num) A := by
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_blockEmb_zero, suMat_blockEmb_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem R0_comm_R0' {a b : Su K p f 4} (ha : a ∈ R0 K p f) (hb : b ∈ R0' K p f) :
    a * b = b * a := by
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  exact blockEmb_comm A B

theorem blk_mul (A B C D : Su K p f 2) :
    blk K p f A B * blk K p f C D = blk K p f (A * C) (B * D) := by
  unfold blk
  calc blockEmb K p f 4 2 0 (by norm_num) A * blockEmb K p f 4 2 2 (by norm_num) B *
        (blockEmb K p f 4 2 0 (by norm_num) C * blockEmb K p f 4 2 2 (by norm_num) D)
      = blockEmb K p f 4 2 0 (by norm_num) A * (blockEmb K p f 4 2 2 (by norm_num) B *
          blockEmb K p f 4 2 0 (by norm_num) C) * blockEmb K p f 4 2 2 (by norm_num) D := by
        group
    _ = blockEmb K p f 4 2 0 (by norm_num) A * (blockEmb K p f 4 2 0 (by norm_num) C *
          blockEmb K p f 4 2 2 (by norm_num) B) * blockEmb K p f 4 2 2 (by norm_num) D := by
        rw [← blockEmb_comm C B]
    _ = blockEmb K p f 4 2 0 (by norm_num) (A * C) *
          blockEmb K p f 4 2 2 (by norm_num) (B * D) := by
        rw [map_mul, map_mul]
        group

theorem blk_one : blk K p f (1 : Su K p f 2) 1 = 1 := by simp [blk]

theorem blk_inv (A B : Su K p f 2) : (blk K p f A B)⁻¹ = blk K p f A⁻¹ B⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [blk_mul, mul_inv_cancel, mul_inv_cancel, blk_one])

theorem blk_mem (A B : Su K p f 2) : blk K p f A B ∈ R0 K p f ⊔ R0' K p f :=
  Subgroup.mul_mem_sup ⟨A, rfl⟩ ⟨B, rfl⟩

theorem u0_mem : u0 K p f ∈ R0 K p f ⊔ R0' K p f := blk_mem _ _

theorem x0_eq_blk : x0 K p f = blk K p f (negOneSU K p f) 1 := by
  simp [x0, blk, rootInvSU]

theorem x0_mem_R0 : x0 K p f ∈ R0 K p f := ⟨negOneSU K p f, rfl⟩

theorem u0_eq_blk : u0 K p f = blk K p f (jSU K p f) (jSU K p f) := rfl

theorem zneg_eq_blk : zneg K p f = blk K p f (negOneSU K p f) (negOneSU K p f) := rfl

theorem suMat_zneg : suMat (zneg K p f) = -1 := by
  rw [zneg, suMat_blk, suMat_negOneSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem suMat_x0 : suMat (x0 K p f) = !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :=
  suMat_rootInvSU_four

theorem suMat_u0 : suMat (u0 K p f) = !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  rw [u0, suMat_blk, suMat_jSU]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem zneg_mul_self : zneg K p f * zneg K p f = 1 := by
  rw [zneg_eq_blk, blk_mul, negOneSU_mul_self, blk_one]

theorem x0_mul_self : x0 K p f * x0 K p f = 1 := by
  rw [x0_eq_blk, blk_mul, negOneSU_mul_self, one_mul, blk_one]

theorem u0_mul_self : u0 K p f * u0 K p f = zneg K p f := by
  rw [u0_eq_blk, blk_mul, jSU_mul_self, zneg_eq_blk]

theorem zneg_mem_center : zneg K p f ∈ Subgroup.center (Su K p f 4) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_zneg]
  simp

theorem zneg_conj (g : Su K p f 4) : g * zneg K p f * g⁻¹ = zneg K p f := by
  rw [Subgroup.mem_center_iff.mp zneg_mem_center g]
  group

theorem x0_mul_u0 : x0 K p f * u0 K p f = u0 K p f * x0 K p f := by
  rw [x0_eq_blk, u0_eq_blk, blk_mul, blk_mul, one_mul, mul_one]
  congr 1
  exact negOneSU_comm _ |>.symm

theorem zneg_mul_x0 : zneg K p f * x0 K p f = blk K p f 1 (negOneSU K p f) := by
  rw [zneg_eq_blk, x0_eq_blk, blk_mul, negOneSU_mul_self, mul_one]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
