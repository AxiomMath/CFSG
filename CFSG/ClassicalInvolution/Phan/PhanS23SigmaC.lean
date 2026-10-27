module

public import CFSG.ClassicalInvolution.Phan.PhanS23Sigma
public import CFSG.ClassicalInvolution.Phan.PhanS20Model

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent

@[expose] def Iu : GF49 := ⟨0, 1⟩

theorem Iu_mul_Iu : Iu * Iu = -1 := by decide

theorem star_Iu : star Iu = -Iu := by decide

theorem Iu_ne_zero : Iu ≠ 0 := by decide

@[expose] def gammaMap (u : Fin 7 → GF49) : Vec GF49 :=
  Sum.elim ![u 0 + Iu * u 3, u 1 + Iu * u 4, u 2 + Iu * u 5]
    (Sum.elim ![u 0 - Iu * u 3, u 1 - Iu * u 4, u 2 - Iu * u 5] (fun _ => u 6))

theorem bf_gammaMap (u v : Fin 7 → GF49) : bf m0 (gammaMap u) (gammaMap v) = polarK u v := by
  simp only [bf, gammaMap, polarK, Fin.sum_univ_three, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, m0]
  linear_combination (-2 * (u 3 * v 3 + u 4 * v 4 + u 5 * v 5)) * Iu_mul_Iu

theorem tauV_gammaMap (u : Fin 7 → GF49) : tauV m0 (gammaMap u) = gammaMap (starV u) := by
  funext i
  rcases i with i | i | i
  · fin_cases i <;> simp [tauV, gammaMap, starV, m0, starRingEnd_apply, star_Iu]
  · fin_cases i <;> simp [tauV, gammaMap, starV, m0, starRingEnd_apply, star_Iu] <;> ring
  · simp [tauV, gammaMap, starV, m0, starRingEnd_apply]

@[expose] def gammaLin : (Fin 7 → GF49) →ₗ[GF49] Vec GF49 where
  toFun := gammaMap
  map_add' u v := by
    funext i
    rcases i with i | i | i
    · fin_cases i <;> simp [gammaMap] <;> ring
    · fin_cases i <;> simp [gammaMap] <;> ring
    · simp [gammaMap]
  map_smul' c u := by
    funext i
    rcases i with i | i | i
    · fin_cases i <;> simp [gammaMap] <;> ring
    · fin_cases i <;> simp [gammaMap] <;> ring
    · simp [gammaMap]

theorem pair_eq_zero {x y : GF49} (e1 : x + Iu * y = 0) (e2 : x - Iu * y = 0) :
    x = 0 ∧ y = 0 := by
  have h2 : (2 : GF49) ≠ 0 := by decide
  have hx : 2 * x = 0 := by linear_combination e1 + e2
  have hy : 2 * (Iu * y) = 0 := by linear_combination e1 - e2
  refine ⟨(mul_eq_zero.mp hx).resolve_left h2, ?_⟩
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left h2)).resolve_left Iu_ne_zero

theorem gammaLin_injective : Function.Injective gammaLin := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h : gammaMap u = 0 := hu
  have a0 := congrFun h (Sum.inl 0)
  have a1 := congrFun h (Sum.inl 1)
  have a2 := congrFun h (Sum.inl 2)
  have b0 := congrFun h (Sum.inr (Sum.inl 0))
  have b1 := congrFun h (Sum.inr (Sum.inl 1))
  have b2 := congrFun h (Sum.inr (Sum.inl 2))
  have c0 := congrFun h (Sum.inr (Sum.inr ()))
  simp only [gammaMap, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Pi.zero_apply] at a0 a1 a2 b0 b1 b2 c0
  obtain ⟨h0, h3⟩ := pair_eq_zero a0 b0
  obtain ⟨h1, h4⟩ := pair_eq_zero a1 b1
  obtain ⟨h2, h5⟩ := pair_eq_zero a2 b2
  funext j
  fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, c0]

@[expose] noncomputable def gammaEquiv : (Fin 7 → GF49) ≃ₗ[GF49] Vec GF49 :=
  gammaLin.linearEquivOfInjective gammaLin_injective
    (by simp [Module.finrank_fintype_fun_eq_card])

theorem bf_gammaEquiv (u v : Fin 7 → GF49) :
    bf m0 (gammaEquiv u) (gammaEquiv v) = polarK u v := bf_gammaMap u v

theorem tauV_gammaEquiv (u : Fin 7 → GF49) :
    tauV m0 (gammaEquiv u) = gammaEquiv (starV u) := tauV_gammaMap u

theorem her_gammaEquiv (u v : Fin 7 → GF49) :
    her m0 (gammaEquiv u) (gammaEquiv v) = polarK u (starV v) := by
  rw [her, tauV_gammaEquiv, bf_gammaEquiv]

theorem polarK_symm (x y : Vec GF49) :
    polarK (gammaEquiv.symm x) (gammaEquiv.symm y) = bf m0 x y := by
  rw [← bf_gammaEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem polarK_starV_symm (x y : Vec GF49) :
    polarK (gammaEquiv.symm x) (starV (gammaEquiv.symm y)) = her m0 x y := by
  rw [← her_gammaEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem tauV_symm (x : Vec GF49) :
    gammaEquiv.symm (tauV m0 x) = starV (gammaEquiv.symm x) := by
  apply gammaEquiv.injective
  rw [LinearEquiv.apply_symm_apply, ← tauV_gammaEquiv, LinearEquiv.apply_symm_apply]

theorem rel_gamma {ι : Type} [Fintype ι] (a : ι → Fin 7 → GF49) (c d : ι → GF49) :
    gammaEquiv (∑ i, c i • a i + ∑ i, d i • starV (a i)) =
      ∑ i, c i • gammaEquiv (a i) + ∑ i, d i • tauV m0 (gammaEquiv (a i)) := by
  simp only [map_add, map_sum, map_smul, tauV_gammaEquiv]

theorem rel_symm {ι : Type} [Fintype ι] (v : ι → Vec GF49) (c d : ι → GF49) :
    ∑ i, c i • gammaEquiv.symm (v i) + ∑ i, d i • starV (gammaEquiv.symm (v i)) = 0 ↔
      ∑ i, c i • v i + ∑ i, d i • tauV m0 (v i) = 0 := by
  rw [← LinearEquiv.map_eq_zero_iff gammaEquiv, rel_gamma]
  simp only [LinearEquiv.apply_symm_apply]

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent
