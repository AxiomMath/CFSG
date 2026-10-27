module

public import CFSG.Adapters.TauCetiExceptional.ReePoints

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti Matrix

variable {L : Type} [Field L]

theorem col_basisMat_eq : (∀ r, basisMat 4 r 0 = 0 ∧ basisMat 5 r 0 = 0) ∧
    (∀ r, basisMat 9 r 0 = if r = 1 then 1 else 0) ∧
    (∀ r, basisMat 8 r 1 = if r = 2 then -1 else 0) ∧
    (∀ r, basisMat 9 r 2 = if r = 3 then 1 else 0) ∧
    (∀ r, basisMat 9 r 3 = if r = 4 then 2 else 0) ∧
    (∀ r, basisMat 8 r 4 = if r = 5 then -1 else 0) ∧
    (∀ r, basisMat 9 r 5 = if r = 6 then 1 else 0) := by
  decide

theorem mulVec_single_basisMatR (t : Fin 14) (c : Fin 7) :
    basisMatR L t *ᵥ Pi.single c 1 = fun r => (basisMat t r c : L) := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem mulVec_single_of_col {t : Fin 14} {c c' : Fin 7} {a : ℤ}
    (h : ∀ r, basisMat t r c = if r = c' then a else 0) :
    basisMatR L t *ᵥ Pi.single c 1 = (a : L) • Pi.single c' 1 := by
  rw [mulVec_single_basisMatR]
  funext r
  rw [h r, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem eq_smul_single_of_mulVec_eq_zero (h2 : (2 : L) ≠ 0) (v : Fin 7 → L)
    (h4 : basisMatR L 4 *ᵥ v = 0) (h5 : basisMatR L 5 *ᵥ v = 0) : v = v 0 • Pi.single 0 1 := by
  have e : ∀ r, (basisMatR L 4 *ᵥ v) r = 0 ∧ (basisMatR L 5 *ᵥ v) r = 0 := fun r =>
    ⟨by rw [h4]; rfl, by rw [h5]; rfl⟩
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_seven, basisMat] at e0 e1 e2 e3 e4 e5
  funext r
  fin_cases r <;> simp_all

theorem commute_mulVec {M X : Matrix (Fin 7) (Fin 7) L} (h : M * X = X * M) (v : Fin 7 → L) :
    M *ᵥ (X *ᵥ v) = X *ᵥ (M *ᵥ v) := by
  rw [mulVec_mulVec, mulVec_mulVec, h]

theorem eq_smul_one_of_commute (h2 : (2 : L) ≠ 0) (M : Matrix (Fin 7) (Fin 7) L)
    (h : ∀ t ∈ ({4, 5, 8, 9} : Finset (Fin 14)), M * basisMatR L t = basisMatR L t * M) :
    M = M 0 0 • (1 : Matrix (Fin 7) (Fin 7) L) := by
  obtain ⟨c45, c90, c81, c92, c93, c84, c95⟩ := col_basisMat_eq
  have h4 := h 4 (by decide)
  have h5 := h 5 (by decide)
  have h8 := h 8 (by decide)
  have h9 := h 9 (by decide)
  set l := M 0 0
  have hcol : ∀ c, M *ᵥ Pi.single c 1 = fun r => M r c := fun c => by
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have z4 : basisMatR L 4 *ᵥ Pi.single (0 : Fin 7) 1 = 0 := by
    rw [mulVec_single_basisMatR]; funext r; simp [(c45 r).1]
  have z5 : basisMatR L 5 *ᵥ Pi.single (0 : Fin 7) 1 = 0 := by
    rw [mulVec_single_basisMatR]; funext r; simp [(c45 r).2]
  have v0 : M *ᵥ Pi.single 0 1 = l • Pi.single 0 1 := by
    have k4 : basisMatR L 4 *ᵥ (M *ᵥ Pi.single 0 1) = 0 := by
      rw [← commute_mulVec h4, z4, Matrix.mulVec_zero]
    have k5 : basisMatR L 5 *ᵥ (M *ᵥ Pi.single 0 1) = 0 := by
      rw [← commute_mulVec h5, z5, Matrix.mulVec_zero]
    have := eq_smul_single_of_mulVec_eq_zero h2 _ k4 k5
    rw [this, hcol]
  have step : ∀ {t : Fin 14} {c c' : Fin 7} {a : ℤ}, (a : L) ≠ 0 →
      M * basisMatR L t = basisMatR L t * M →
      (∀ r, basisMat t r c = if r = c' then a else 0) →
      M *ᵥ Pi.single c 1 = l • Pi.single c 1 → M *ᵥ Pi.single c' 1 = l • Pi.single c' 1 := by
    intro t c c' a ha hX hc hv
    have e := commute_mulVec hX (Pi.single c 1)
    rw [mulVec_single_of_col hc, hv, Matrix.mulVec_smul, Matrix.mulVec_smul,
      mulVec_single_of_col hc, smul_comm] at e
    exact smul_right_injective _ ha e
  have v1 := step (by simp) h9 c90 v0
  have v2 := step (by simp) h8 c81 v1
  have v3 := step (by simp) h9 c92 v2
  have v4 := step (by exact_mod_cast h2) h9 c93 v3
  have v5 := step (by simp) h8 c84 v4
  have v6 := step (by simp) h9 c95 v5
  ext r c
  have hv : M *ᵥ Pi.single c 1 = l • Pi.single c 1 := by
    fin_cases c
    exacts [v0, v1, v2, v3, v4, v5, v6]
  have e : M r c = (M *ᵥ Pi.single c 1) r := by rw [hcol]
  rw [e, hv, Matrix.smul_apply, Pi.smul_apply, Matrix.one_apply, Pi.single_apply]

theorem conj_eq_of_adConj_eq_one [Algebra (ZMod 3) L] {g : Matrix.GeneralLinearGroup (Fin 7) L}
    (hg : g ∈ G2ShortRoot.PrimeField.points L) (h1 : adConj g = 1) (t : Fin 14) :
    (g : Matrix (Fin 7) (Fin 7) L) * basisMatR L t *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) =
        basisMatR L t := by
  have hc : ∀ u, coord u ((g : Matrix (Fin 7) (Fin 7) L) * basisMatR L t *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L)) =
        if t = u then 1 else 0 := fun u => by
    have e := adOp_single_apply (g : Matrix (Fin 7) (Fin 7) L)
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) (lab t) (lab u)
    rw [labMat_lab, ← bas_apply u, Equiv.symm_apply_apply] at e
    rw [← e]
    change ((adConj g) (Finsupp.single (lab t) 1)) (bas u) = _
    rw [h1, Module.End.one_apply, Finsupp.single_apply, bas_apply]
    exact if_congr lab_injective.eq_iff rfl rfl
  rw [(points_le_normGroup hg t).1.eq_sum]
  simp only [hc, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem two_ne_zero_of_algebra [Algebra (ZMod 3) L] : (2 : L) ≠ 0 := by
  rw [show (2 : L) = algebraMap (ZMod 3) L 2 by rw [map_ofNat]]
  exact (map_ne_zero _).2 (by decide)

theorem adPoints_injective [Algebra (ZMod 3) L] : Function.Injective (adPoints L) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have h1 : adConj (g : Matrix.GeneralLinearGroup (Fin 7) L) = 1 := by
    rw [← coe_adPoints, hg]
    rfl
  set M := ((g : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) with hMdef
  have hinv : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) * M = 1 :=
    by rw [hMdef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : ∀ t, M * basisMatR L t = basisMatR L t * M := fun t => by
    have e := conj_eq_of_adConj_eq_one g.2 h1 t
    calc M * basisMatR L t = M * basisMatR L t *
          (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) L) : Matrix (Fin 7) (Fin 7) L) * M) := by
          rw [hinv, Matrix.mul_one]
      _ = basisMatR L t * M := by rw [← Matrix.mul_assoc, e]
  have hM := eq_smul_one_of_commute two_ne_zero_of_algebra M fun t _ => hcomm t
  set l := M 0 0
  have hX := (Matrix.preservesG2Cross_def _).1
    (G2ShortRoot.PrimeField.preservesG2Cross_of_mem_points g.2) 0
  rw [← hMdef, hM] at hX
  have hsum : ∑ a, (l • (1 : Matrix (Fin 7) (Fin 7) L)) a 0 •
      (G2ShortRoot.crossOperator a).map (Int.cast : ℤ → L) =
        l • (G2ShortRoot.crossOperator 0).map (Int.cast : ℤ → L) := by
    rw [Finset.sum_eq_single 0]
    · rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    · intro a _ ha
      rw [Matrix.smul_apply, Matrix.one_apply_ne ha, smul_zero, zero_smul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [hsum, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at hX
  have hent := congrFun (congrFun hX 3) 6
  have hc : G2ShortRoot.crossOperator 0 3 6 = -1 := by
    rw [G2ShortRoot.crossOperator_def]
    rfl
  simp only [Matrix.smul_apply, Matrix.map_apply, hc, smul_eq_mul] at hent
  have hl0 : l ≠ 0 := by
    intro h0
    have e := hinv
    rw [hM, h0, zero_smul, Matrix.mul_zero] at e
    exact zero_ne_one e
  have hl : l = 1 := by
    have e : l * 1 = l * l := by linear_combination -hent
    exact (mul_left_cancel₀ hl0 e).symm
  refine Subtype.ext (Units.ext ?_)
  change M = 1
  rw [hM, hl, one_smul]

end CFSG.TauCetiBridge.Ree
