module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.Open
open CFSG.StandardType.WitSpNs (planeMat planeMat_apply plane side coord plane_coord side_coord
  eq_of_plane_side)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped MatrixGroups

section Blocks

variable {F : Type}

private def planeSide : Fin 2 ⊕ Fin 2 ≃ Fin 2 × Fin 2 where
  toFun x := (plane x, side x)
  invFun y := coord y.2 y.1
  left_inv x := eq_of_plane_side (plane_coord (side x) (plane x)) (side_coord (side x) (plane x))
  right_inv y := Prod.ext (plane_coord y.2 y.1) (side_coord y.2 y.1)

private def dag (B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F)) :
    Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F) :=
  of fun p q => (B q p)ᵀ

private theorem dag_fin_two (a b c d : Matrix (Fin 2) (Fin 2) F) :
    dag !![a, b; c, d] = !![aᵀ, cᵀ; bᵀ, dᵀ] := by
  refine Matrix.ext fun p q => ?_
  fin_cases p <;> fin_cases q <;> rfl

variable [Field F]

variable (F) in
private def blk : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F) ≃+*
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  (compRingEquiv (Fin 2) (Fin 2) F).trans (reindexRingEquiv F planeSide.symm)

private theorem blk_apply (B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F))
    (x y : Fin 2 ⊕ Fin 2) : blk F B x y = B (plane x) (plane y) (side x) (side y) := rfl

private theorem transpose_blk (B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F)) :
    (blk F B)ᵀ = blk F (dag B) := rfl

private theorem dag_mul (A B : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F)) :
    dag (A * B) = dag B * dag A :=
  (blk F).injective (by rw [← transpose_blk, map_mul, transpose_mul, transpose_blk,
    transpose_blk, map_mul])

private def jTwo : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]

private theorem blk_jTwo :
    blk F !![jTwo, 0; 0, jTwo] = (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) _ F) := by
  ext x y
  rw [blk_apply]
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [jTwo]

private theorem blk_planeMat (N : Matrix (Fin 2) (Fin 2) F) :
    blk F !![N, 0; 0, N] = planeMat fun _ => N := by
  ext x y
  rw [blk_apply, planeMat_apply]
  rcases x with i | i <;> rcases y with j | j <;> fin_cases i <;> fin_cases j <;> simp

private theorem transpose_mul_jTwo_mul {M : Matrix (Fin 2) (Fin 2) F} (hdet : M.det = 1) :
    Mᵀ * jTwo * M = jTwo := by
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jTwo, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | linear_combination hdet | linear_combination -hdet | ring1

private def pM (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F) :=
  !![1, M; 1, M * M]

private def pI (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F) :=
  !![M * M, M; 1, 1]

private abbrev sc : F →+* Matrix (Fin 2) (Fin 2) F := algebraMap F (Matrix (Fin 2) (Fin 2) F)

private theorem sc_transpose (x : F) : (sc x)ᵀ = sc x := by
  rw [sc, Matrix.algebraMap_eq_diagonal, diagonal_transpose]

private theorem sc_mul_jTwo_mul (x y : F) : sc x * jTwo * sc y = sc (x * y) * jTwo := by
  rw [mul_assoc, ← Algebra.commutes y jTwo, ← mul_assoc, ← map_mul]

private def dT (t : SL(2, F)) : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F) :=
  (t : Matrix (Fin 2) (Fin 2) F).map sc

private theorem dT_eq (t : SL(2, F)) :
    dT t = !![sc (t 0 0), sc (t 0 1); sc (t 1 0), sc (t 1 1)] := by
  refine Matrix.ext fun p q => ?_
  fin_cases p <;> fin_cases q <;> rfl

private theorem commute_fin_two {N a b c d : Matrix (Fin 2) (Fin 2) F} (ha : Commute N a)
    (hb : Commute N b) (hc : Commute N c) (hd : Commute N d) :
    Commute !![N, 0; 0, N] !![a, b; c, d] := by
  rw [Commute, SemiconjBy, mul_fin_two, mul_fin_two]
  simp only [mul_zero, zero_mul, add_zero, zero_add, ha.eq, hb.eq, hc.eq, hd.eq]

end Blocks

theorem SG.exists_sl2_sp_two {F : Type} [Field F] [CharP F 2] {M : Matrix (Fin 2) (Fin 2) F}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) :
    ∃ ψ : SL(2, F) →* StatedSp 2 F, Function.Injective ψ ∧
      ∀ N : Matrix (Fin 2) (Fin 2) F, Commute N M → ∀ t,
        Commute (mat 2 F (ψ t)) (planeMat fun _ => N) := by
  have hMM : M * M + M = 1 := by
    rw [← add_zero (M * M + M), ← CharTwo.add_self_eq_zero (1 : Matrix (Fin 2) (Fin 2) F),
      ← add_assoc, hM, zero_add]
  have hMM' : M + M * M = 1 := by rw [add_comm, hMM]
  have hM3 : M * (M * M) = 1 := by
    have : M * (M * M) - 1 = (M - 1) * (M * M + M + 1) := by noncomm_ring
    rwa [hM, mul_zero, sub_eq_zero] at this
  have hM3' : M * M * M = 1 := by rw [mul_assoc, hM3]
  have hJ := transpose_mul_jTwo_mul hdet
  have hJ1 : Mᵀ * jTwo = jTwo * (M * M) := by
    calc Mᵀ * jTwo = Mᵀ * jTwo * (M * (M * M)) := by rw [hM3, mul_one]
      _ = jTwo * (M * M) := by rw [← mul_assoc, hJ]
  have hJ2 : (M * M)ᵀ * jTwo = jTwo * M := by
    rw [transpose_mul, mul_assoc, hJ1, ← mul_assoc, hJ1, mul_assoc, ← mul_assoc (M * M) M M, hM3',
      one_mul]
  have hPI : pM M * pI M = 1 := by
    rw [pM, pI, mul_fin_two, show (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F)) =
      !![1, 0; 0, 1] from one_fin_two]
    simp only [mul_one, one_mul, hMM, hMM', CharTwo.add_self_eq_zero]
  have hIP : pI M * pM M = 1 := by
    rw [pM, pI, mul_fin_two, show (1 : Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F)) =
      !![1, 0; 0, 1] from one_fin_two]
    simp only [mul_one, one_mul, hM3, hM3', hMM, hMM', CharTwo.add_self_eq_zero]
  have hB1 : dag (pM M) * !![jTwo, 0; 0, jTwo] * pM M = !![0, jTwo; jTwo, 0] := by
    rw [pM, dag_fin_two, mul_fin_two, mul_fin_two]
    simp only [transpose_one, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, hJ1, hJ2,
      mul_assoc, hM3, CharTwo.add_self_eq_zero, ← mul_add, hMM, hMM']
  have hB3 : dag (pI M) * !![0, jTwo; jTwo, 0] * pI M = !![jTwo, 0; 0, jTwo] := by
    rw [pI, dag_fin_two, mul_fin_two, mul_fin_two]
    simp only [transpose_one, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, hJ1, hJ2,
      mul_assoc, hM3, CharTwo.add_self_eq_zero, ← mul_add, hMM, hMM']
  have hB2 : ∀ t : SL(2, F), dag (dT t) * !![0, jTwo; jTwo, 0] * dT t = !![0, jTwo; jTwo, 0] := by
    intro t
    have ht := t.det_coe
    rw [det_fin_two] at ht
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [dT_eq, dag_fin_two, mul_fin_two, mul_fin_two]
    simp only [sc_transpose, mul_zero, zero_mul, add_zero, zero_add, sc_mul_jTwo_mul, ← add_mul,
      ← map_add]
    rw [show t 1 0 * t 0 0 + t 0 0 * t 1 0 = 0 by linear_combination t 0 0 * t 1 0 * h2,
      show t 1 0 * t 0 1 + t 0 0 * t 1 1 = 1 by linear_combination ht + t 0 1 * t 1 0 * h2,
      show t 1 1 * t 0 0 + t 0 1 * t 1 0 = 1 by linear_combination ht + t 0 1 * t 1 0 * h2,
      show t 1 1 * t 0 1 + t 0 1 * t 1 1 = 0 by linear_combination t 0 1 * t 1 1 * h2,
      map_zero, map_one, zero_mul, one_mul]
  let Pu : (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) F))ˣ := ⟨pM M, pI M, hPI, hIP⟩
  let ψ₁ : SL(2, F) →* GL (Fin 2 ⊕ Fin 2) F := (Units.map (blk F).toMonoidHom).comp
    ((MulAut.conj Pu).toMonoidHom.comp ((Units.map (sc.mapMatrix (m := Fin 2)).toMonoidHom).comp
      Matrix.SpecialLinearGroup.toGL))
  have hψ₁ : ∀ t, ((ψ₁ t : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      blk F (pM M * dT t * pI M) := fun t => rfl
  have hsp : ∀ t, ψ₁ t ∈ StatedSp 2 F := fun t => by
    rw [CFSG.Open.StatedAPI.mem_statedSp_iff, hψ₁, transpose_blk, ← blk_jTwo, ← map_mul,
      ← map_mul, dag_mul, dag_mul]
    congr 1
    calc dag (pI M) * (dag (dT t) * dag (pM M)) * !![jTwo, 0; 0, jTwo] * (pM M * dT t * pI M)
        = dag (pI M) * (dag (dT t) * (dag (pM M) * !![jTwo, 0; 0, jTwo] * pM M) * dT t) *
          pI M := by simp only [mul_assoc]
      _ = !![jTwo, 0; 0, jTwo] := by rw [hB1, hB2 t, hB3]
  refine ⟨ψ₁.codRestrict (StatedSp 2 F) hsp, (injective_iff_map_eq_one _).2 fun t ht => ?_,
    fun N hNM t => ?_⟩
  · have h1 : blk F (pM M * dT t * pI M) = blk F 1 := by
      rw [← hψ₁, map_one]
      exact congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) ht
    have h2 : dT t = 1 := by
      calc dT t = pI M * (pM M * dT t * pI M) * pM M := by
            rw [← mul_assoc, ← mul_assoc, hIP, one_mul, mul_assoc, hIP, mul_one]
        _ = 1 := by rw [(blk F).injective h1, mul_one, hIP]
    refine Subtype.ext (Matrix.ext fun p q => sc.injective ?_)
    have h3 := congrFun (congrFun h2 p) q
    rw [dT, Matrix.map_apply] at h3
    rw [h3, Matrix.SpecialLinearGroup.coe_one]
    by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq]
  · have hc : Commute !![N, 0; 0, N] (pM M * dT t * pI M) := by
      have h1 : Commute N 1 := Commute.one_right N
      refine ((?_ : Commute _ (pM M)).mul_right ?_).mul_right ?_
      · exact commute_fin_two h1 hNM h1 (hNM.mul_right hNM)
      · rw [dT_eq]
        exact commute_fin_two (Algebra.commutes _ N).symm (Algebra.commutes _ N).symm
          (Algebra.commutes _ N).symm (Algebra.commutes _ N).symm
      · exact commute_fin_two (hNM.mul_right hNM) hNM h1 h1
    rw [← blk_planeMat]
    exact (hc.map (blk F)).symm

end CFSG.LocalAnalysis.GLTheoremA.S265

end
