module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Weyl
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44
import all CFSG.Fischer.F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open CFSG.EvenSmallLie.UnitarySix.YamadaEnd
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem blockSL_transvection {m k i : ℕ} (h : i + k ≤ m) {a b : Fin k} (hab : a ≠ b) (c : K) :
    blockSL K m k i h (SpecialLinearGroup.transvection hab c) =
      SpecialLinearGroup.transvection ((blockIdx_injective h).ne hab) c := by
  apply Subtype.ext
  ext x y
  rw [coe_blockSL, blockMat_apply, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Fin.ext_iff, blockIdx_val]
  split_ifs <;> first | rfl | omega | simp_all

variable (K) in
@[expose] def antiDiagN (d : ℕ) : Matrix (Fin d) (Fin d) K :=
  (Fin.revPerm : Equiv.Perm (Fin d)).permMatrix K

variable (K) in
theorem antiDiagN_mul_self (d : ℕ) : antiDiagN K d * antiDiagN K d = 1 := by
  rw [antiDiagN, ← Matrix.permMatrix_mul]
  have : (Fin.revPerm : Equiv.Perm (Fin d)) * Fin.revPerm = 1 := by
    ext i
    simp
  rw [this, Matrix.permMatrix_one]

theorem fieldAutSL_transvectionN (ψ : K ≃+* K) {d : ℕ} {i j : Fin d} (h : i ≠ j) (c : K) :
    fieldAutSL ψ d (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection h (ψ c) := by
  ext a b
  rw [coe_fieldAutSL, Matrix.map_apply, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.add_apply, map_add, one_apply,
    single_apply, single_apply]
  split_ifs <;> simp

theorem invTransposeSL_transvectionN {d : ℕ} {i j : Fin d} (h : i ≠ j) (c : K) :
    invTransposeSL d (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection h.symm (-c) :=
  Subtype.ext (by
    rw [coe_invTransposeSL, SpecialLinearGroup.transvection_inv,
      SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, transpose_add,
      transpose_one, transpose_single])

omit [Field K] in
theorem permMatrix_conj_apply [Field K] {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    (σ.permMatrix K * M * τ.permMatrix K) a b = M (σ a) (τ.symm b) := by
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    submatrix_apply, id]

theorem conjSL_antiDiagN_transvection {d : ℕ} {i j : Fin d} (h : i ≠ j) (c : K) :
    conjSL (antiDiagN K d) (antiDiagN K d) (antiDiagN_mul_self K d)
        (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne h) c := by
  ext a b
  rw [coe_conjSL, antiDiagN, permMatrix_conj_apply,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  simp [one_apply, single_apply, Fin.rev_eq_iff]

variable [CharP K 2] [Finite K]

variable (K) in
@[expose] noncomputable def tauSL : SL(3, K) ≃* SL(3, K) :=
  (fieldAutSL (frobeniusEquiv K 2) 3).trans
    ((invTransposeSL 3).trans (conjSL (antiDiagN K 3) (antiDiagN K 3) (antiDiagN_mul_self K 3)))

theorem tauSL_transvection {i j : Fin 3} (h : i ≠ j) (c : K) :
    tauSL K (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection (Fin.rev_injective.ne h.symm) (c ^ 2) := by
  show conjSL (antiDiagN K 3) (antiDiagN K 3) (antiDiagN_mul_self K 3)
    (invTransposeSL 3 (fieldAutSL (frobeniusEquiv K 2) 3 (SpecialLinearGroup.transvection h c))) = _
  rw [fieldAutSL_transvectionN, invTransposeSL_transvectionN, conjSL_antiDiagN_transvection,
    frobeniusEquiv_apply, frobenius_def, CharTwo.neg_eq]

omit [CharP K 2] [Finite K] in
theorem blockSL_commute (A B : SL(3, K)) :
    Commute (blockSL K 6 3 0 (by omega) A) (blockSL K 6 3 3 (by omega) B) :=
  blockSL_comm _ _ (Or.inl (by omega)) A B

variable (K) in
@[expose] noncomputable def theta1 : SL(3, K) →* SL(6, K) :=
  (MonoidHom.noncommCoprod (blockSL K 6 3 0 (by omega)) (blockSL K 6 3 3 (by omega))
    blockSL_commute).comp ((MonoidHom.id _).prod (tauSL K).toMonoidHom)

theorem theta1_apply (A : SL(3, K)) :
    theta1 K A = blockSL K 6 3 0 (by omega) A * blockSL K 6 3 3 (by omega) (tauSL K A) := rfl

theorem theta1_transvection {i j : Fin 3} (h : i ≠ j) (c : K) :
    theta1 K (SpecialLinearGroup.transvection h c) =
      SpecialLinearGroup.transvection ((blockIdx_injective (show 0 + 3 ≤ 6 by omega)).ne h) c *
        SpecialLinearGroup.transvection
          (Fin.rev_injective.ne ((blockIdx_injective (show 0 + 3 ≤ 6 by omega)).ne h).symm)
          (c ^ 2) := by
  rw [theta1_apply, tauSL_transvection, blockSL_transvection, blockSL_transvection]
  congr 1
  apply YamadaInputs.transvection_congr_fin6
  · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega
  · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega

variable (K) in
@[expose] noncomputable def chi1 : SL(4, K) →* SL(6, K) := blockSL K 6 4 1 (by omega)

open CFSG.Fischer CFSG.LieType.Chevalley.E6GraphLevi

theorem theta1_transvection_mem {i j : Fin 3} (h : i ≠ j) (c : F4) :
    theta1 F4 (SpecialLinearGroup.transvection h c) ∈ SUJ := by
  rw [theta1_transvection, ← sig_apply]
  exact YamadaInputs.transvection_mul_mem_unitarySL F4.two_eq_zero sig_sig _ c

theorem theta1_mem_SUJ (A : SL(3, F4)) : theta1 F4 A ∈ SUJ := by
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F4) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 F4) ≤ SUJ.comap (theta1 F4) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact theta1_transvection_mem hij c
  exact hle hA

@[expose] noncomputable def theta0 : SL(3, F4) →* SUJ := (theta1 F4).codRestrict SUJ theta1_mem_SUJ

theorem coe_theta0 (A : SL(3, F4)) : (theta0 A : SpecialLinearGroup (Fin 6) F4) = theta1 F4 A :=
  rfl

theorem twist_chi1_transvection {i j : Fin 4} (h : i ≠ j) (c : F4) :
    unitaryTwist sig (chi1 F4 (SpecialLinearGroup.transvection h c)) =
      chi1 F4 (sigmaSL F4 (SpecialLinearGroup.transvection h c)) := by
  rw [chi1, blockSL_transvection, YamadaEnd.sigmaSL_transvection, blockSL_transvection,
    unitaryTwist, MonoidHom.comp_apply, map_transvection, graphSL_transvection F4.two_eq_zero,
    sig_apply]
  apply YamadaInputs.transvection_congr_fin6
  · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega
  · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega

theorem twist_chi1 : (unitaryTwist sig).comp (chi1 F4) =
    (chi1 F4).comp (sigmaSL F4).toMonoidHom := by
  refine MonoidHom.eq_of_eqOn_dense CFSG.LinearGroups.special_linear_elementary_generation ?_
  rintro _ ⟨i, j, hij, c, rfl⟩
  exact twist_chi1_transvection hij c

theorem chi1_mem_SUJ {B : SL(4, F4)} (hB : B ∈ msigma F4) : chi1 F4 B ∈ SUJ := by
  rw [mem_unitarySL_iff_unitaryTwist]
  have := congrArg (fun f => f B) twist_chi1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [this]
  exact congrArg (chi1 F4) hB

@[expose] noncomputable def chi0 : msigma F4 →* SUJ :=
  ((chi1 F4).comp (msigma F4).subtype).codRestrict SUJ fun B => chi1_mem_SUJ B.2

theorem coe_chi0 (B : msigma F4) :
    (chi0 B : SpecialLinearGroup (Fin 6) F4) = chi1 F4 (B : SL(4, F4)) := rfl

theorem chi1_sY02 : chi1 F4 (sY F4 0 * sY F4 2) =
    (yamGen 16 : SpecialLinearGroup (Fin 6) F4) := by
  apply Subtype.ext
  decide +kernel

theorem chi1_sY1 : chi1 F4 (sY F4 1) = (yamGen 17 : SpecialLinearGroup (Fin 6) F4) := by
  apply Subtype.ext
  decide +kernel

theorem theta0_transvection {i j : Fin 3} (h : i ≠ j) (c : F4) {i' j' : Fin 6} (h' : i' ≠ j')
    (hi : i'.val = i.val) (hj : j'.val = j.val) :
    theta0 (SpecialLinearGroup.transvection h c) = rootY i' j' h' c := by
  apply Subtype.ext
  rw [coe_theta0, theta1_transvection]
  show _ = SpecialLinearGroup.transvection h' c *
    SpecialLinearGroup.transvection (Fin.rev_injective.ne h'.symm) (sig c)
  rw [sig_apply]
  congr 1
  · apply YamadaInputs.transvection_congr_fin6
    · apply Fin.ext; simp [blockIdx_val]; omega
    · apply Fin.ext; simp [blockIdx_val]; omega
  · apply YamadaInputs.transvection_congr_fin6
    · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega
    · apply Fin.ext; simp [blockIdx_val, Fin.val_rev]; omega

theorem yamGen0_eq :
    yamGen 0 = theta0 (SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1) :=
  (theta0_transvection _ _ _ rfl rfl).symm

theorem yamGen1_eq :
    yamGen 1 = theta0 (SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) F4.ω) :=
  (theta0_transvection _ _ _ rfl rfl).symm

theorem yamGen2_eq :
    yamGen 2 = theta0 (SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1) :=
  (theta0_transvection _ _ _ rfl rfl).symm

theorem yamGen3_eq :
    yamGen 3 = theta0 (SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) F4.ω) :=
  (theta0_transvection _ _ _ rfl rfl).symm

theorem yamGen15_eq : yamGen 15 =
    theta0 (SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1 *
      SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1 *
      SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1) := by
  rw [map_mul, map_mul, theta0_transvection _ _ (by decide : (1 : Fin 6) ≠ 0) rfl rfl,
    theta0_transvection _ _ (by decide : (0 : Fin 6) ≠ 1) rfl rfl]
  rfl

theorem yamGen16_eq : yamGen 16 =
    theta0 (SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1 *
      SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1 *
      SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1) := by
  rw [map_mul, map_mul, theta0_transvection _ _ (by decide : (2 : Fin 6) ≠ 1) rfl rfl,
    theta0_transvection _ _ (by decide : (1 : Fin 6) ≠ 2) rfl rfl]
  rfl

theorem sigmaSL_T10_T32 (a : F4) :
    sigmaSL F4 (SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) (a ^ 2)) =
      SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) (a ^ 2) := by
  rw [map_mul, YamadaEnd.sigmaSL_transvection, YamadaEnd.sigmaSL_transvection]
  revert a
  decide +kernel

theorem sigmaSL_T20_T31 (a : F4) :
    sigmaSL F4 (SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 1) (a ^ 2)) =
      SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 0) a *
        SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 1) (a ^ 2) := by
  rw [map_mul, YamadaEnd.sigmaSL_transvection, YamadaEnd.sigmaSL_transvection]
  revert a
  decide +kernel

theorem sigmaSL_T21 :
    sigmaSL F4 (SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1) =
      SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1 := by
  rw [YamadaEnd.sigmaSL_transvection]
  decide +kernel

theorem sigmaSL_T30 :
    sigmaSL F4 (SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 0) 1) =
      SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 0) 1 := by
  rw [YamadaEnd.sigmaSL_transvection]
  decide +kernel

@[expose] noncomputable def mx2 (a : F4) : msigma F4 :=
  ⟨_, sigmaSL_T10_T32 a⟩

@[expose] noncomputable def mx5 (a : F4) : msigma F4 :=
  ⟨_, sigmaSL_T20_T31 a⟩

@[expose] noncomputable def mx3 : msigma F4 := ⟨_, sigmaSL_T21⟩

@[expose] noncomputable def mx7 : msigma F4 := ⟨_, sigmaSL_T30⟩

theorem sY02_mem : sY F4 0 * sY F4 2 ∈ msigma F4 := by
  show sigmaSL F4 (sY F4 0 * sY F4 2) = sY F4 0 * sY F4 2
  rw [map_mul, YamadaEnd.sigmaSL_sY_zero, YamadaEnd.sigmaSL_sY_two]
  exact (blockSL2_comm 3 0 2 (by decide) _ _).symm

theorem sY1_mem : sY F4 1 ∈ msigma F4 := YamadaEnd.sigmaSL_sY_one F4

theorem chi0_mx2_one : chi0 (mx2 1) = yamGen 2 := sujExt (by decide +kernel)

theorem chi0_mx2_ω : chi0 (mx2 F4.ω) = yamGen 3 := sujExt (by decide +kernel)

theorem chi0_mx3 : chi0 mx3 = yamGen 4 := sujExt (by decide +kernel)

theorem chi0_mx5_one : chi0 (mx5 1) = yamGen 7 := sujExt (by decide +kernel)

theorem chi0_mx5_ω : chi0 (mx5 F4.ω) = yamGen 8 := sujExt (by decide +kernel)

theorem chi0_mx7 : chi0 mx7 = yamGen 11 := sujExt (by decide +kernel)

theorem chi0_sY02 : chi0 ⟨_, sY02_mem⟩ = yamGen 16 := Subtype.ext chi1_sY02

theorem chi0_sY1 : chi0 ⟨_, sY1_mem⟩ = yamGen 17 := Subtype.ext chi1_sY1

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
