module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow
public import CFSG.LieType.Simplicity.Classical
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UC

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.LinearGroups.UnitaryThreeOverNine
open scoped Matrix

@[expose] def blkMat (N : Matrix (Fin 3) (Fin 3) F9) : Matrix (Fin 4) (Fin 4) F9 :=
  Matrix.of (Fin.cases (motive := fun _ => Fin 4 → F9)
    (Fin.cases (motive := fun _ => F9) 1 fun _ => 0)
    fun i => Fin.cases (motive := fun _ => F9) 0 fun j => N i j)

@[simp] theorem blkMat_zero_zero (N : Matrix (Fin 3) (Fin 3) F9) : blkMat N 0 0 = 1 := rfl

@[simp] theorem blkMat_zero_succ (N : Matrix (Fin 3) (Fin 3) F9) (j : Fin 3) :
    blkMat N 0 j.succ = 0 := rfl

@[simp] theorem blkMat_succ_zero (N : Matrix (Fin 3) (Fin 3) F9) (i : Fin 3) :
    blkMat N i.succ 0 = 0 := rfl

@[simp] theorem blkMat_succ_succ (N : Matrix (Fin 3) (Fin 3) F9) (i j : Fin 3) :
    blkMat N i.succ j.succ = N i j := rfl

theorem blkMat_one : blkMat 1 = 1 := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem blkMat_mul (M N : Matrix (Fin 3) (Fin 3) F9) : blkMat (M * N) = blkMat M * blkMat N := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

@[expose] def blkHom : Matrix (Fin 3) (Fin 3) F9 →* Matrix (Fin 4) (Fin 4) F9 where
  toFun := blkMat
  map_one' := blkMat_one
  map_mul' := blkMat_mul

@[expose] def blkGL : GL (Fin 3) F9 →* GL (Fin 4) F9 := Units.map blkHom

theorem coe_blkGL (A : GL (Fin 3) F9) :
    ((blkGL A : GL (Fin 4) F9) : Matrix (Fin 4) (Fin 4) F9) = blkMat A := rfl

theorem barF_one : barF 1 = 1 := by decide

theorem barF_zero : barF 0 = 0 := by decide

theorem blkMat_map_barF (N : Matrix (Fin 3) (Fin 3) F9) :
    (blkMat N).map barF = blkMat (N.map barF) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [Matrix.map_apply, blkMat_zero_zero, blkMat_zero_succ, blkMat_succ_zero,
      blkMat_succ_succ, barF_one, barF_zero]

theorem blkMat_transpose (N : Matrix (Fin 3) (Fin 3) F9) : (blkMat N)ᵀ = blkMat Nᵀ := by
  refine Matrix.ext fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem det_blkMat (N : Matrix (Fin 3) (Fin 3) F9) : (blkMat N).det = N.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, blkMat_zero_zero, Fin.succAbove_zero,
    blkMat_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1

theorem isUnitaryF_blkGL {A : GL (Fin 3) F9}
    (hA : ((A : Matrix (Fin 3) (Fin 3) F9).map (· ^ 3))ᵀ * A = 1) : IsUnitaryF (blkGL A) := by
  have hb : (A : Matrix (Fin 3) (Fin 3) F9).map barF =
      (A : Matrix (Fin 3) (Fin 3) F9).map (· ^ 3) :=
    Matrix.ext fun i j => barF_eq_pow _
  unfold IsUnitaryF
  rw [coe_blkGL, blkMat_map_barF, blkMat_transpose, ← blkMat_mul, hb, hA, blkMat_one]

theorem natCard_F9 : Nat.card F9 = 9 := by rw [Nat.card_eq_fintype_card, F9.card_eq]

@[expose] noncomputable def beta : StatedSU 3 3 F9 →* Equiv.Perm (Fin 820) :=
  perm820.comp (blkGL.comp (StatedSU 3 3 F9).subtype)

theorem beta_apply (N : StatedSU 3 3 F9) : beta N = perm820 (blkGL N) := rfl

theorem matDm1_eq : matN9 codeDm1 = Matrix.diagonal (Fin.cases (motive := fun _ => F9) (-1)
    fun _ => 1) := by
  decide +kernel

theorem blkMat_comm_dM1 (N : Matrix (Fin 3) (Fin 3) F9) :
    blkMat N * matN9 codeDm1 = matN9 codeDm1 * blkMat N := by
  rw [matDm1_eq]
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp only [Fin.cases_zero, Fin.cases_succ, blkMat_zero_zero, blkMat_zero_succ,
      blkMat_succ_zero, blkMat_succ_succ, mul_one, one_mul, mul_zero, zero_mul]

theorem beta_comm (N : StatedSU 3 3 F9) : beta N * d2P = d2P * beta N := by
  rw [beta_apply, d2P, ← map_mul, ← map_mul]
  congr 1
  exact Units.ext (by rw [Units.val_mul, Units.val_mul]; exact blkMat_comm_dM1 _)

theorem unitary_det_of_mem (N : StatedSU 3 3 F9) :
    (((N : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9).map (· ^ 3))ᵀ * (N : GL (Fin 3) F9) = 1 ∧
      ((N : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9).det = 1 := by
  have h : (N : GL (Fin 3) F9) ∈ (StatedSU 3 3 F9 : Set (GL (Fin 3) F9)) := N.2
  rw [coe_statedSU natCard_F9] at h
  exact h

theorem beta_mem (N : StatedSU 3 3 F9) : beta N ∈ P := by
  rw [P_eq_range, beta_apply]
  refine perm820_mem_range (isUnitaryF_blkGL (unitary_det_of_mem N).1) ?_
  rw [coe_blkGL, det_blkMat]
  exact (unitary_det_of_mem N).2

theorem beta_wGL_ne_one : beta ⟨wGL, wGL_mem_statedSU natCard_F9⟩ ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin 820) => ((σ ⟨810, by norm_num⟩ : Fin 820) : ℕ)) h
  simp only [Equiv.Perm.one_apply] at h1
  rw [beta_apply, perm820_apply, coe_blkGL, mulVec_eq_mv4] at h1
  have h2 : ptIndex (mv4 (blkMat wreathSwapMat) (decode 810)) = 819 := by decide +kernel
  have h3 : ptIndex (mv4 (blkMat wreathSwapMat) (decode 810)) = 810 := h1
  omega

theorem isSimpleGroup_statedSU : IsSimpleGroup (StatedSU 3 3 F9) :=
  (LieType.Simplicity.fam_classical_converse _
    ⟨.PSU, 3, 3, 1, classicalModel_statedSU natCard_F9⟩).2.2

theorem beta_injective : Function.Injective beta := by
  have := isSimpleGroup_statedSU
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal beta.ker with h | h
  · exact h
  · exfalso
    apply beta_wGL_ne_one
    have hm : (⟨wGL, wGL_mem_statedSU natCard_F9⟩ : StatedSU 3 3 F9) ∈ beta.ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact hm

theorem card_range_beta : Nat.card beta.range = 6048 := by
  rw [← card_statedSU natCard_F9]
  exact (Nat.card_congr (MonoidHom.ofInjective beta_injective).toEquiv).symm

theorem range_beta :
    beta.range = P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820))) := by
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_inf_centralizer_d2, card_range_beta])
  rintro _ ⟨N, rfl⟩
  exact Subgroup.mem_inf.2 ⟨beta_mem N, Subgroup.mem_centralizer_singleton_iff.2 (beta_comm N)⟩

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M
