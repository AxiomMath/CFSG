module

public import CFSG.LieType.Chevalley.E6A5CubeFaithful

public noncomputable section

namespace CFSG.LieType.Chevalley.E6A5Cube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExteriorCube exteriorPower
  Set Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Chevalley.C2E6Std (setA jA exists_jA_of_mem_setA)
open scoped Pointwise

variable {K : Type} [Field K]

variable (K) in
@[expose] def antiDiag (s : Fin 6 → K) : Matrix (Fin 6) (Fin 6) K :=
  Matrix.of fun i j => if j = Fin.rev i then s i else 0

theorem antiDiag_apply (s : Fin 6 → K) (i j : Fin 6) :
    antiDiag K s i j = if j = Fin.rev i then s i else 0 := rfl

theorem antiDiag_mul (s s' : Fin 6 → K) :
    antiDiag K s * antiDiag K s' = diagonal fun i => s i * s' (Fin.rev i) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · by_cases hij : i = j
    · subst hij
      simp [antiDiag_apply]
    · simp [antiDiag_apply, diagonal_apply_ne _ hij, Ne.symm hij, hij]
  · intro k _ hk
    simp [antiDiag_apply, hk]
  · simp

theorem antiDiag_mul_single (s : Fin 6 → K) (a b : Fin 6) (x : K) :
    antiDiag K s * Matrix.single a b x = Matrix.single (Fin.rev a) b (s (Fin.rev a) * x) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · by_cases hi : i = Fin.rev a
    · subst hi
      by_cases hj : j = b
      · subst hj; simp [antiDiag_apply, Matrix.single_apply]
      · simp [antiDiag_apply, Matrix.single_apply, hj]
    · have h1 : ¬ a = Fin.rev i := fun h => hi (by rw [h, Fin.rev_rev])
      have h2 : ¬ Fin.rev a = i := fun h => hi h.symm
      simp [antiDiag_apply, Matrix.single_apply, h1, h2]
  · intro k _ hk
    simp [antiDiag_apply, hk]
  · simp

theorem single_mul_antiDiag (s : Fin 6 → K) (a b : Fin 6) (x : K) :
    Matrix.single a b x * antiDiag K s = Matrix.single a (Fin.rev b) (x * s b) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · by_cases hi : i = a
    · subst hi
      by_cases hj : j = Fin.rev b
      · subst hj; simp [antiDiag_apply, Matrix.single_apply]
      · have hj' : ¬ Fin.rev b = j := fun h => hj h.symm
        simp [antiDiag_apply, Matrix.single_apply, hj, hj']
    · have hi' : ¬ a = i := fun h => hi h.symm
      simp [antiDiag_apply, Matrix.single_apply, hi, hi']
  · intro k _ hk
    have hk' : ¬ b = k := fun h => hk h.symm
    simp [Matrix.single_apply, hk']
  · simp

variable (K) in
@[expose] def signAnti : Matrix (Fin 6) (Fin 6) K := antiDiag K fun i => (-1 : K) ^ (i : ℕ)

variable (K) in
@[expose] def signAntiInv : Matrix (Fin 6) (Fin 6) K :=
  antiDiag K fun i => (-1 : K) ^ ((i : ℕ) + 1)

theorem val_add_rev_add_one (i : Fin 6) : (i : ℕ) + ((Fin.rev i : Fin 6) : ℕ) + 1 = 6 := by
  have := i.2
  rw [Fin.val_rev]
  omega

theorem signAnti_mul_inv : signAnti K * signAntiInv K = 1 := by
  rw [signAnti, signAntiInv, antiDiag_mul]
  have : ∀ i : Fin 6, (-1 : K) ^ (i : ℕ) * (-1) ^ (((Fin.rev i : Fin 6) : ℕ) + 1) = 1 := by
    intro i
    rw [← pow_add, ← add_assoc, val_add_rev_add_one]
    norm_num
  simp only [this]
  exact diagonal_one

theorem signAntiInv_mul : signAntiInv K * signAnti K = 1 := by
  rw [signAnti, signAntiInv, antiDiag_mul]
  have : ∀ i : Fin 6, (-1 : K) ^ ((i : ℕ) + 1) * (-1) ^ ((Fin.rev i : Fin 6) : ℕ) = 1 := by
    intro i
    rw [← pow_add, show (i : ℕ) + 1 + ((Fin.rev i : Fin 6) : ℕ) = 6 by
      have := val_add_rev_add_one i; omega]
    norm_num
  simp only [this]
  exact diagonal_one

@[expose] def thetaFun (h : SpecialLinearGroup (Fin 6) K) : SpecialLinearGroup (Fin 6) K :=
  ⟨signAnti K * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ *
      signAntiInv K, by
    rw [det_mul, det_mul, det_transpose, (h⁻¹).2, mul_one, ← det_mul, signAnti_mul_inv, det_one]⟩

theorem coe_thetaFun (h : SpecialLinearGroup (Fin 6) K) :
    (thetaFun h : Matrix (Fin 6) (Fin 6) K) =
      signAnti K * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ *
        signAntiInv K := rfl

theorem thetaFun_mul (g h : SpecialLinearGroup (Fin 6) K) :
    thetaFun (g * h) = thetaFun g * thetaFun h := by
  apply Subtype.ext
  change (thetaFun (g * h) : Matrix (Fin 6) (Fin 6) K) =
    (thetaFun g : Matrix (Fin 6) (Fin 6) K) * (thetaFun h : Matrix (Fin 6) (Fin 6) K)
  rw [coe_thetaFun, coe_thetaFun, coe_thetaFun, _root_.mul_inv_rev,
    Matrix.SpecialLinearGroup.coe_mul, transpose_mul]
  have h1 : signAntiInv K * signAnti K = 1 := signAntiInv_mul
  generalize signAnti K = M at *
  generalize signAntiInv K = Mi at *
  generalize (((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ) = A
  generalize (((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ) = B
  calc
    M * (A * B) * Mi = M * A * (Mi * M) * B * Mi := by
      rw [h1, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = M * A * Mi * (M * B * Mi) := by simp only [Matrix.mul_assoc]

variable (K) in
@[expose] def thetaD : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  MonoidHom.mk' thetaFun thetaFun_mul

theorem coe_thetaD (h : SpecialLinearGroup (Fin 6) K) :
    (thetaD K h : Matrix (Fin 6) (Fin 6) K) =
      signAnti K * ((h⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)ᵀ *
        signAntiInv K := rfl

theorem sign_fact_up : ∀ t : Fin 5,
    (-1 : K) ^ (((Fin.castSucc (Fin.rev t) : Fin 6)) : ℕ) *
      (-1) ^ (((Fin.castSucc t : Fin 6) : ℕ) + 1) = -1 := by
  intro t
  fin_cases t <;> norm_num [Fin.rev]

theorem sign_fact_down : ∀ t : Fin 5,
    (-1 : K) ^ (((Fin.succ (Fin.rev t) : Fin 6)) : ℕ) *
      (-1) ^ (((Fin.succ t : Fin 6) : ℕ) + 1) = -1 := by
  intro t
  fin_cases t <;> norm_num [Fin.rev]

theorem thetaD_upAdj (t : Fin 5) (c : K) :
    thetaD K (upAdj K t c) = upAdj K (Fin.rev t) c := by
  apply Subtype.ext
  rw [coe_thetaD, upAdj, upAdj, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, transpose_add,
    transpose_one, Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    signAnti_mul_inv]
  congr 1
  rw [signAnti, signAntiInv, antiDiag_mul_single, single_mul_antiDiag, Fin.rev_succ,
    Fin.rev_castSucc]
  congr 1
  linear_combination (-c) * sign_fact_up (K := K) t

theorem thetaD_downAdj (t : Fin 5) (c : K) :
    thetaD K (downAdj K t c) = downAdj K (Fin.rev t) c := by
  apply Subtype.ext
  rw [coe_thetaD, downAdj, downAdj, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe, transpose_add,
    transpose_one, Matrix.transpose_single, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    signAnti_mul_inv]
  congr 1
  rw [signAnti, signAntiInv, antiDiag_mul_single, single_mul_antiDiag, Fin.rev_succ,
    Fin.rev_castSucc]
  congr 1
  linear_combination (-c) * sign_fact_down (K := K) t

variable (σ : K →+* K)

variable (K) in
@[expose] def tauSL : SpecialLinearGroup (Fin 6) K →* SpecialLinearGroup (Fin 6) K :=
  (thetaD K).comp (SpecialLinearGroup.map σ)

theorem map_upAdj (t : Fin 5) (c : K) :
    SpecialLinearGroup.map σ (upAdj K t c) = upAdj K t (σ c) := by
  apply Subtype.ext
  simp [upAdj, SpecialLinearGroup.transvection_coe, Matrix.map_add, Matrix.single]

theorem map_downAdj (t : Fin 5) (c : K) :
    SpecialLinearGroup.map σ (downAdj K t c) = downAdj K t (σ c) := by
  apply Subtype.ext
  simp [downAdj, SpecialLinearGroup.transvection_coe, Matrix.map_add, Matrix.single]

theorem tauSL_upAdj (t : Fin 5) (c : K) :
    tauSL K σ (upAdj K t c) = upAdj K (Fin.rev t) (σ c) := by
  rw [tauSL, MonoidHom.comp_apply, map_upAdj, thetaD_upAdj]

theorem tauSL_downAdj (t : Fin 5) (c : K) :
    tauSL K σ (downAdj K t c) = downAdj K (Fin.rev t) (σ c) := by
  rw [tauSL, MonoidHom.comp_apply, map_downAdj, thetaD_downAdj]

theorem tauSL_tauSL (hσσ : ∀ c, σ (σ c) = c) (h : SpecialLinearGroup (Fin 6) K) :
    tauSL K σ (tauSL K σ h) = h := by
  have key : (tauSL K σ).comp (tauSL K σ) = MonoidHom.id (SpecialLinearGroup (Fin 6) K) := by
    refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
    rintro _ ⟨t, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, tauSL_upAdj, Fin.rev_rev, hσσ]
    · simp only [MonoidHom.comp_apply, MonoidHom.id_apply, tauSL_downAdj, Fin.rev_rev, hσσ]
  exact congrArg (fun F => F h) key

theorem tauSL_smul_one {z : SpecialLinearGroup (Fin 6) K} {l : K}
    (hz : (z : Matrix (Fin 6) (Fin 6) K) = l • (1 : Matrix (Fin 6) (Fin 6) K)) :
    (tauSL K σ z : Matrix (Fin 6) (Fin 6) K) = (σ l)⁻¹ • (1 : Matrix (Fin 6) (Fin 6) K) := by
  set w : SpecialLinearGroup (Fin 6) K := SpecialLinearGroup.map σ z with hw
  have hwm : (w : Matrix (Fin 6) (Fin 6) K) = σ l • (1 : Matrix (Fin 6) (Fin 6) K) := by
    rw [hw, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hz]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, hij]
  have hl0 : σ l ≠ 0 := by
    intro h0
    have := w.2
    rw [hwm, h0, zero_smul, det_zero] at this
    exact zero_ne_one this
  have hinv : ((w⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (σ l)⁻¹ • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have h1 : ((w⁻¹ * w : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, hwm, Matrix.mul_smul, Matrix.mul_one] at h1
    have h2 := congrArg (fun m => (σ l)⁻¹ • m) h1
    simp only [smul_smul, inv_mul_cancel₀ hl0, one_smul, smul_zero] at h2
    exact h2
  change signAnti K * (((w⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))ᵀ *
    signAntiInv K = _
  rw [hinv, transpose_smul, transpose_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    signAnti_mul_inv]

section Twist

variable [Finite K]

variable (K) in
@[expose] def psiAEquiv : groupA K ≃* (cubeHom (K := K)).range :=
  (MonoidHom.ofInjective psiA_injective).trans (MulEquiv.subgroupCongr range_psiA)

theorem coe_psiAEquiv (g : groupA K) :
    (psiAEquiv K g : (Module.End K (⋀[K]^3 (Fin 6 → K)))ˣ) = psiA K g := rfl

variable (K) in
@[expose] def liftA : SpecialLinearGroup (Fin 6) K →* groupA K :=
  (psiAEquiv K).symm.toMonoidHom.comp (cubeHom (K := K)).rangeRestrict

theorem psiA_liftA (h : SpecialLinearGroup (Fin 6) K) : psiA K (liftA K h) = cubeHom h := by
  rw [← coe_psiAEquiv, liftA, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.coe_rangeRestrict]

theorem liftA_eq_of_psiA_eq {g : groupA K} {h : SpecialLinearGroup (Fin 6) K}
    (hgh : psiA K g = cubeHom h) : liftA K h = g :=
  psiA_injective ((psiA_liftA h).trans hgh.symm)

theorem liftA_upAdj (t : Fin 5) (c : K) :
    liftA K (upAdj K t c) = ⟨xUnit Tag.E6 K (jA t) c, xUnit_mem_groupA t c⟩ :=
  liftA_eq_of_psiA_eq (psiA_xUnit t c)

theorem liftA_downAdj (t : Fin 5) (c : K) :
    liftA K (downAdj K t c) = ⟨yUnit Tag.E6 K (jA t) c, yUnit_mem_groupA t c⟩ :=
  liftA_eq_of_psiA_eq (psiA_yUnit t c)

theorem perm_jA_val : ∀ t : Fin 5, (TwistTag.E6.perm (jA t)).val = (jA (Fin.rev t)).val := by
  decide

theorem perm_jA (t : Fin 5) : TwistTag.E6.perm (jA t) = jA (Fin.rev t) := Fin.ext (perm_jA_val t)

variable (K) in
abbrev twistE6 : ModGL Tag.E6 K →* ModGL Tag.E6 K := twistHom TwistTag.E6 K σ

theorem twistE6_xUnit (i : Fin Tag.E6.rank) (c : K) :
    twistE6 K σ (xUnit Tag.E6 K i c) = xUnit Tag.E6 K (TwistTag.E6.perm i) (σ c) :=
  twistHom_xUnit TwistTag.E6 K σ i c

theorem twistE6_yUnit (i : Fin Tag.E6.rank) (c : K) :
    twistE6 K σ (yUnit Tag.E6 K i c) = yUnit Tag.E6 K (TwistTag.E6.perm i) (σ c) :=
  twistHom_yUnit TwistTag.E6 K σ i c

theorem twistE6_mem_groupA {g : ModGL Tag.E6 K} (hg : g ∈ groupA K) :
    twistE6 K σ g ∈ groupA K := by
  refine Subgroup.closure_induction (p := fun g _ => twistE6 K σ g ∈ groupA K)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
      rw [twistE6_xUnit, perm_jA]
      exact xUnit_mem_groupA _ _
    · obtain ⟨t, rfl⟩ := exists_jA_of_mem_setA hi
      rw [twistE6_yUnit, perm_jA]
      exact yUnit_mem_groupA _ _
  · rw [map_one]
    exact one_mem _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact mul_mem hx hy
  · intro x _ hx
    rw [map_inv]
    exact inv_mem hx

variable (K) in
@[expose] def twistA : groupA K →* groupA K :=
  MonoidHom.mk' (fun g => ⟨twistE6 K σ g, twistE6_mem_groupA σ g.2⟩) fun g h =>
    Subtype.ext (map_mul (twistE6 K σ) (g : ModGL Tag.E6 K) h)

theorem coe_twistA (g : groupA K) :
    ((twistA K σ g : groupA K) : ModGL Tag.E6 K) = twistE6 K σ g := rfl

theorem psiA_twistA_liftA :
    (psiA K).comp ((twistA K σ).comp (liftA K)) = (cubeHom (K := K)).comp (tauSL K σ) := by
  refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
  rintro _ ⟨t, c, rfl | rfl⟩
  · simp only [MonoidHom.comp_apply, liftA_upAdj, tauSL_upAdj]
    rw [← psiA_xUnit]
    congr 1
    apply Subtype.ext
    rw [coe_twistA, twistE6_xUnit, perm_jA]
  · simp only [MonoidHom.comp_apply, liftA_downAdj, tauSL_downAdj]
    rw [← psiA_yUnit]
    congr 1
    apply Subtype.ext
    rw [coe_twistA, twistE6_yUnit, perm_jA]

theorem psiA_twistA {g : groupA K} {h : SpecialLinearGroup (Fin 6) K}
    (hgh : psiA K g = cubeHom h) : psiA K (twistA K σ g) = cubeHom (tauSL K σ h) := by
  rw [← liftA_eq_of_psiA_eq hgh]
  exact congrArg (fun F => F h) (psiA_twistA_liftA σ)

end Twist

end CFSG.LieType.Chevalley.E6A5Cube
