module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviAut

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Swap

variable {K : Type} [Field K]

@[expose] noncomputable def swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K :=
  reindexAlgEquiv K K finSumFinEquiv (fromBlocks 0 1 1 0)

theorem swapBlk_mul_swapBlk : (swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) * swapBlk = 1 := by
  rw [swapBlk, ← map_mul, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, add_zero, zero_add, fromBlocks_one,
    map_one]

theorem swapBlk_mul_blk (X S : Matrix (Fin 2) (Fin 2) K) :
    swapBlk * blk X S = blk S X * swapBlk := by
  rw [swapBlk, blk, blk, ← map_mul, ← map_mul, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]

theorem swapBlk_conj (X S : Matrix (Fin 2) (Fin 2) K) :
    swapBlk * blk X S * swapBlk = blk S X := by
  rw [swapBlk_mul_blk, Matrix.mul_assoc, swapBlk_mul_swapBlk, Matrix.mul_one]

variable [CharP K 2]

theorem det_swapBlk : (swapBlk : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).det = 1 := by
  have h := congrArg det (swapBlk_mul_swapBlk (K := K))
  rw [det_mul, det_one] at h
  exact eq_of_mul_self_eq (h.trans (mul_one 1).symm)

@[expose] noncomputable def swapSL : SpecialLinearGroup (Fin (2 + 2)) K := ⟨swapBlk, det_swapBlk⟩

theorem swapSL_mul_self : (swapSL : SpecialLinearGroup (Fin (2 + 2)) K) * swapSL = 1 :=
  Subtype.ext swapBlk_mul_swapBlk

theorem swapSL_inv : (swapSL : SpecialLinearGroup (Fin (2 + 2)) K)⁻¹ = swapSL :=
  inv_eq_of_mul_eq_one_right swapSL_mul_self

theorem swapSL_conj_blkSL₁ (X : SpecialLinearGroup (Fin 2) K) :
    swapSL * blkSL₁ X * swapSL⁻¹ = (blkSL₂ X : SpecialLinearGroup (Fin (2 + 2)) K) := by
  rw [swapSL_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₁,
    coe_blkSL₂]
  exact swapBlk_conj _ _

theorem swapSL_conj_blkSL₂ (X : SpecialLinearGroup (Fin 2) K) :
    swapSL * blkSL₂ X * swapSL⁻¹ = (blkSL₁ X : SpecialLinearGroup (Fin (2 + 2)) K) := by
  rw [swapSL_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blkSL₁,
    coe_blkSL₂]
  exact swapBlk_conj _ _

theorem swapSL_conj_torus (c : Kˣ) :
    swapSL * torus c * swapSL⁻¹ = (torus c⁻¹ : SpecialLinearGroup (Fin (2 + 2)) K) := by
  rw [swapSL_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torus, coe_torus,
    inv_inv]
  exact swapBlk_conj _ _

theorem conj_proj_swapSL (g : SpecialLinearGroup (Fin (2 + 2)) K) :
    MulAut.conj (proj (2 + 2) K swapSL) (proj (2 + 2) K g) =
      proj (2 + 2) K (swapSL * g * swapSL⁻¹) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem map_conj_barW :
    (barW K 2).map (MulAut.conj (proj (2 + 2) K swapSL)).toMonoidHom = barL K 2 := by
  rw [barW, MonoidHom.map_range, barL]
  refine congrArg MonoidHom.range (MonoidHom.ext fun X => ?_)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [conj_proj_swapSL, swapSL_conj_blkSL₁]

theorem map_conj_barL :
    (barL K 2).map (MulAut.conj (proj (2 + 2) K swapSL)).toMonoidHom = barW K 2 := by
  rw [barL, MonoidHom.map_range, barW]
  refine congrArg MonoidHom.range (MonoidHom.ext fun X => ?_)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [conj_proj_swapSL, swapSL_conj_blkSL₂]

theorem map_conj_barT :
    (barT K).map (MulAut.conj (proj (2 + 2) K swapSL)).toMonoidHom = barT K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨c⁻¹, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_proj_swapSL, swapSL_conj_torus]
  · rintro _ ⟨c, rfl⟩
    refine ⟨proj (2 + 2) K (torus c⁻¹), ⟨c⁻¹, rfl⟩, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [conj_proj_swapSL, swapSL_conj_torus, inv_inv]

end Swap

section Five

variable {K : Type} [Field K] [CharP K 2]

@[expose] def fiveM (ω : K) : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, ω]

theorem det_fiveM (ω : K) : (fiveM ω).det = 1 := by
  rw [fiveM, det_fin_two_of]
  simp [CharTwo.neg_eq]

@[expose] def fiveSL (ω : K) : SpecialLinearGroup (Fin 2) K := ⟨fiveM ω, det_fiveM ω⟩

theorem fiveM_pow_five {ω : K} (hω : ω * ω + ω + 1 = 0) : fiveM ω ^ 5 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e1 : fiveM ω * fiveM ω = !![1, ω; ω, ω] := by
    rw [fiveM, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
        cons_val_fin_one, one_mul]
      linear_combination hω - ω * h2
  have e2 : !![1, ω; ω, ω] * fiveM ω = !![ω, ω; ω, 1] := by
    rw [fiveM, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
        cons_val_zero, empty_val', cons_val_fin_one, one_mul, mul_one]
      linear_combination hω - ω * h2
    · simp
    · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
        cons_val_fin_one, mul_one]
      linear_combination hω - h2
  have e3 : !![ω, ω; ω, 1] * fiveM ω = !![ω, 1; 1, 0] := by
    rw [fiveM, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
        cons_val_zero, empty_val', cons_val_fin_one, mul_one]
      linear_combination hω - h2
    · simp
    · simp only [Fin.mk_one, Fin.isValue, of_apply, cons_val', cons_val_one, empty_val',
        cons_val_fin_one, mul_one, one_mul]
      linear_combination ω * h2
  have e4 : !![ω, 1; 1, 0] * fiveM ω = 1 := by
    rw [fiveM, mul_fin_two, one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_one,
        cons_val_zero, empty_val', cons_val_fin_one, mul_one, one_mul]
      linear_combination ω * h2
    · simp
    · simp
  rw [show (5 : ℕ) = 0 + 1 + 1 + 1 + 1 + 1 from rfl, pow_succ, pow_succ, pow_succ, pow_succ,
    pow_succ, pow_zero, Matrix.one_mul, e1, e2, e3, e4]

theorem fiveSL_pow_five {ω : K} (hω : ω * ω + ω + 1 = 0) : fiveSL ω ^ 5 = 1 :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow]; exact fiveM_pow_five hω)

theorem fiveSL_ne_one (ω : K) : fiveSL ω ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp [fiveSL, fiveM] at this

omit [CharP K 2] in
theorem eq_of_mul_fiveM {S : Matrix (Fin 2) (Fin 2) K} {ω : K} (h : S * fiveM ω = fiveM ω * S) :
    S 1 0 = S 0 1 ∧ S 1 1 = S 0 0 + ω * S 0 1 := by
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [fiveM, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  exact ⟨h00.symm, by rw [← h01, mul_comm]⟩

omit [CharP K 2] in
theorem commute_of_mul_fiveM {S S' : Matrix (Fin 2) (Fin 2) K} {ω : K}
    (h : S * fiveM ω = fiveM ω * S) (h' : S' * fiveM ω = fiveM ω * S') : S * S' = S' * S := by
  obtain ⟨h10, h11⟩ := eq_of_mul_fiveM h
  obtain ⟨h10', h11'⟩ := eq_of_mul_fiveM h'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h11, h10', h11'] <;> ring

theorem eq_smul_one_of_mul_fiveM {D : Matrix (Fin 2) (Fin 2) K} {ω : K} (hω0 : ω ≠ 0)
    (h : D * fiveM ω = fiveM ω * D) {z : K} (hz : D * D = z • 1) : D = D 0 0 • 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨h10, h11⟩ := eq_of_mul_fiveM h
  have e := congrFun (congrFun hz 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, h11] at e
  have hb : ω * (D 0 1 * D 0 1) = 0 := by linear_combination e - D 0 0 * D 0 1 * h2
  have hb0 : D 0 1 = 0 := mul_self_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hω0)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h11, hb0]

end Five

section Four

variable {K : Type} [Field K] [CharP K 2]

theorem scalars_four_eq_bot : scalars (2 + 2) K = ⊥ := by
  refine eq_bot_iff.mpr fun u hu => ?_
  obtain ⟨c, hc4, hc⟩ := mem_scalars.mp hu
  have h4 : ((c : K) * c) * ((c : K) * c) = 1 * 1 := by
    have := congrArg Units.val hc4
    rw [Units.val_pow_eq_pow_val, Units.val_one] at this
    rw [one_mul, ← this]
    ring
  have h1 : (c : K) = 1 := eq_of_mul_self_eq ((eq_of_mul_self_eq h4).trans (mul_one 1).symm)
  rw [mem_bot]
  apply Subtype.ext
  rw [hc, h1, map_one]
  rfl

theorem proj_injective_four : Function.Injective (proj (2 + 2) K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_four_eq_bot]

theorem exists_blk_of_commute_torus {g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K} {c : Kˣ}
    (hc : c ≠ 1)
    (h : g * (torus c : SpecialLinearGroup (Fin (2 + 2)) K) =
      (torus c : SpecialLinearGroup (Fin (2 + 2)) K) * g) :
    ∃ X D : Matrix (Fin 2) (Fin 2) K, g = blk X D := by
  obtain ⟨A, B, C, D, hg⟩ := eq_reindex_fromBlocks g
  rw [hg, coe_torus, blk, ← map_mul, ← map_mul] at h
  have h' := (reindexAlgEquiv K K finSumFinEquiv).injective h
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h'
  obtain ⟨-, hB, hC, -⟩ := h'
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hB hC
  have hne : (c : K) - ((c⁻¹ : Kˣ) : K) ≠ 0 := by
    intro h0
    apply hc
    have h1 : (c : K) * c = 1 * 1 :=
      calc (c : K) * c = (c : K) * ((c⁻¹ : Kˣ) : K) := by rw [← sub_eq_zero.mp h0]
        _ = 1 * 1 := by rw [Units.mul_inv, one_mul]
    exact Units.ext (eq_of_mul_self_eq h1)
  have hB0 : B = 0 := by
    have : ((c : K) - ((c⁻¹ : Kˣ) : K)) • B = 0 := by rw [sub_smul, hB, sub_self]
    exact (smul_eq_zero.mp this).resolve_left hne
  have hC0 : C = 0 := by
    have : ((c : K) - ((c⁻¹ : Kˣ) : K)) • C = 0 := by rw [sub_smul, hC, sub_self]
    exact (smul_eq_zero.mp this).resolve_left hne
  exact ⟨A, D, by rw [hg, hB0, hC0, blk]⟩

omit [CharP K 2] in
theorem mul_eq_of_slConjugation_eq {n : ℕ} (B : GL (Fin n) K)
    {h h' : SpecialLinearGroup (Fin n) K}
    (hh : CatalogueBHigherLinearAction.slConjugation n K B h = h') :
    (B : Matrix (Fin n) (Fin n) K) * h = h' * B := by
  have h1 := congrArg Subtype.val hh
  rw [CatalogueBHigherLinearAction.slConjugation_matrix] at h1
  rw [← h1, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem eq_one_of_fixes_five [Finite K] (α : MulAut (projectiveSL (2 + 2) K)) (h2 : α * α = 1)
    (hW : ∀ w ∈ barW K 2, α w = w) {c : Kˣ} (hc : c ≠ 1)
    (hT : α (proj (2 + 2) K (torus c)) = proj (2 + 2) K (torus c)) {ω : K} (hω0 : ω ≠ 0)
    (hx : α (proj (2 + 2) K (blkSL₂ (fiveSL ω))) = proj (2 + 2) K (blkSL₂ (fiveSL ω))) :
    α = 1 := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 2 + 2) (by omega)
  obtain ⟨B, τ, ε, hε, rfl⟩ := hgen α
  interval_cases ε
  · obtain ⟨hτ, c', D, -, hB⟩ := fix_barW_zero hW
    rw [fieldAut_eq_one hτ, pow_zero, mul_one, mul_one] at h2 hx ⊢
    rw [conjAut_proj] at hx
    have hBx := mul_eq_of_slConjugation_eq B (proj_injective_four hx)
    rw [coe_blkSL₂, hB, blk_mul, blk_mul] at hBx
    have hDx : D * fiveM ω = fiveM ω * D := by
      have := (blk_injective hBx).2
      exact this
    obtain ⟨z, hz⟩ := exists_scalar_of_conjAut_sq B h2
    rw [Units.val_mul, hB, blk_mul, scalar_eq_blk] at hz
    obtain ⟨hz1, hz2⟩ := blk_injective hz
    have hD := eq_smul_one_of_mul_fiveM hω0 hDx hz2
    have e1 : c' * c' = z := by
      have := congrFun (congrFun hz1 0) 0
      simpa [Matrix.smul_mul] using this
    have e2 : D 0 0 * D 0 0 = z := by
      have := congrFun (congrFun hz2 0) 0
      rw [hD] at this
      simpa [Matrix.smul_mul] using this
    have hcd : c' = D 0 0 := eq_of_mul_self_eq (e1.trans e2.symm)
    refine conjAut_eq_one_of_scalar B (c := c') ?_
    rw [hB, hD, ← hcd, scalar_eq_blk]
  · exact (false_of_fix_one_two hW hc hT).elim

end Four

end CFSG.ComponentClassification.RankTwoClassical
