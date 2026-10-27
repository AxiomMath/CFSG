module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisLinearInvol
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine

public section

namespace CFSG.AGLEmbeddingD2.HeisLinear

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi CFSG.AGLEmbeddingD2.SquareLinear
  CFSG.AGLEmbeddingD2.HeisEngine

section SL2

variable {F : Type} [Field F]

@[expose] noncomputable def sl2Anti [CharP F 2] (t : Fˣ) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, (t : F); ((t⁻¹ : Fˣ) : F), 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem sl2Anti_mul_self [CharP F 2] (t : Fˣ) :
    sl2Anti t * sl2Anti t = (1 : Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp [sl2Anti, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Anti_mul_sl2Swap [CharP F 2] (t : Fˣ) :
    sl2Anti t * sl2Swap = (sl2Diag t : Matrix.SpecialLinearGroup (Fin 2) F) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp [sl2Anti, sl2Swap, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Upper_one_mul_self [CharP F 2] : sl2Upper (1 : F) * sl2Upper 1 = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Upper, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem sl2Lower_mul_self [CharP F 2] (c : F) : sl2Lower c * sl2Lower c = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;>
    simp [sl2Lower, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem sl2Upper_one_mul_sl2Lower_pow_five [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    (sl2Upper (1 : F) * sl2Lower ω) ^ 5 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  have hM : ((sl2Upper (1 : F) : Matrix (Fin 2) (Fin 2) F) *
      (sl2Lower ω : Matrix (Fin 2) (Fin 2) F)) = !![1 + ω, 1; ω, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hM]
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

theorem sl2Upper_one_mul_sl2Lower_ne_one {ω : F} : sl2Upper (1 : F) * sl2Lower ω ≠ 1 := by
  intro h
  have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
    (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  simp [sl2Upper, sl2Lower, Matrix.mul_apply, Fin.sum_univ_two] at h1

end SL2

section Real

variable {m : ℕ} {F : Type} [Field F] [CharP F 2] {Y : Type*} [Group Y]
  {π : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* Y} {J : Subgroup Y}

theorem realOver_torus_five (hBJ : borel (rootDatum m F) (torus m F) ≤ J.comap π) (i : Fin m)
    {t : Fˣ} (ht : orderOf t = 5) :
    RealOver 5 π (rankOne (rootDatum m F).rootGroup i) J := by
  have hrange := rankOne_eq_range_blockHom (F := F) i
  have ht5 : t ^ 5 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  refine RealOver.of_involutions' (by decide : Odd 5) (x := SL.blockHom F i (sl2Anti t))
    (y := SL.blockHom F i sl2Swap) (hrange ▸ ⟨_, rfl⟩) (hrange ▸ ⟨_, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, sq, sl2Anti_mul_self, map_one]
  · rw [← map_pow, sq, sl2Swap_mul_self, map_one]
  · rw [← map_mul, sl2Anti_mul_sl2Swap, ← map_pow, sl2Diag_pow, ht5, sl2Diag_one, map_one]
  · rw [← map_mul, sl2Anti_mul_sl2Swap]
    intro h
    have h' := SL.blockHom_injective i (h.trans (map_one _).symm)
    have h'' := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) h'
    exact ht1 (by simpa [coe_sl2Diag] using h'')
  · rw [← map_mul, sl2Anti_mul_sl2Swap]
    exact hBJ (le_sup_left (a := ⨆ k, torus m F k)
      (le_iSup (torus m F) i (blockHom_sl2Diag_mem_torus i t)))

theorem realOver_upper_lower_five (hBJ : borel (rootDatum m F) (torus m F) ≤ J.comap π)
    {i : Fin m} (hi : i ∈ negIndices (rootDatum m F) (J.comap π)) {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) : RealOver 5 π (rankOne (rootDatum m F).rootGroup i) J := by
  have hrange := rankOne_eq_range_blockHom (F := F) i
  refine RealOver.of_involutions' (by decide : Odd 5) (x := SL.blockHom F i (sl2Upper 1))
    (y := SL.blockHom F i (sl2Lower ω)) (hrange ▸ ⟨_, rfl⟩) (hrange ▸ ⟨_, rfl⟩) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, sq, sl2Upper_one_mul_self, map_one]
  · rw [← map_pow, sq, sl2Lower_mul_self, map_one]
  · rw [← map_mul, ← map_pow, sl2Upper_one_mul_sl2Lower_pow_five hω, map_one]
  · rw [← map_mul]
    intro h
    exact sl2Upper_one_mul_sl2Lower_ne_one (SL.blockHom_injective i (h.trans (map_one _).symm))
  · rw [← map_mul]
    have hL := rankOne_le_of_mem_negIndices hBJ hi
    exact hL (hrange ▸ ⟨_, rfl⟩)

theorem realOver_leviM_five (hBJ : borel (rootDatum m F) (torus m F) ≤ J.comap π) {a : ℕ}
    (ha : a + 3 ≤ m)
    (hI : ∀ k : Fin m, a ≤ k.val → k.val < a + 3 →
      k ∈ negIndices (rootDatum m F) (J.comap π)) :
    RealOver 5 π (leviM (rootDatum m F) {k : Fin m | a ≤ k.val ∧ k.val < a + 3}) J := by
  obtain ⟨x, y, hx, hy, hx2, hy2, h5, h1⟩ := exists_involutions_five (F := F) ha
  refine RealOver.of_involutions' (by decide : Odd 5) hx hy hx2 hy2 h5 h1 ?_
  have hle : leviM (rootDatum m F) {k : Fin m | a ≤ k.val ∧ k.val < a + 3} ≤ J.comap π :=
    iSup₂_le fun i hi => rankOne_le_of_mem_negIndices hBJ (hI i hi.1 hi.2)
  exact hle (mul_mem hx hy)

end Real

end CFSG.AGLEmbeddingD2.HeisLinear
