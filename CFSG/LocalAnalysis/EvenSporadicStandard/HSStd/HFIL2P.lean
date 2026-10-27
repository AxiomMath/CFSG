module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Matrix

section Scalar

variable {F : Type*} [Field F]

theorem scalar_contradiction (P q r f g h : F) (h2 : (2 : F) ≠ 0)
    (h1 : P ^ 2 + 4 * (q * r) = 0) (hne : P ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0)
    (e1 : 2 * (f * q) = g * P) (e2 : h * P = 2 * (f * r)) (e3 : g * r = q * h)
    (hdet : f ^ 2 + g * h ≠ 0) : False := by
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  by_cases hP : P = 0
  · subst hP
    have hqr : q * r = 0 := by
      have : 4 * (q * r) = 0 := by simpa using h1
      exact (mul_eq_zero.1 this).resolve_left h4
    rcases mul_eq_zero.1 hqr with hq | hr
    · subst hq
      have hr : r ≠ 0 := by
        rcases hne with h | h | h
        · exact absurd rfl h
        · exact absurd rfl h
        · exact h
      have hf : f = 0 := by
        have : 2 * (f * r) = 0 := by simpa using e2.symm
        have hfr : f * r = 0 := (mul_eq_zero.1 this).resolve_left h2
        exact (mul_eq_zero.1 hfr).resolve_right hr
      have hg : g = 0 := by
        have : g * r = 0 := by simpa using e3
        exact (mul_eq_zero.1 this).resolve_right hr
      exact hdet (by rw [hf, hg]; ring)
    · subst hr
      have hq : q ≠ 0 := by
        rcases hne with h | h | h
        · exact absurd rfl h
        · exact h
        · exact absurd rfl h
      have hf : f = 0 := by
        have : 2 * (f * q) = 0 := by simpa using e1
        have hfq : f * q = 0 := (mul_eq_zero.1 this).resolve_left h2
        exact (mul_eq_zero.1 hfq).resolve_right hq
      have hh : h = 0 := by
        have : q * h = 0 := by simpa using e3.symm
        exact (mul_eq_zero.1 this).resolve_left hq
      exact hdet (by rw [hf, hh]; ring)
  · have : P ^ 2 * (f ^ 2 + g * h) = 0 := by
      linear_combination f ^ 2 * h1 + (g * P) * e2 - (2 * (f * r)) * e1
    exact hdet ((mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hP))

end Scalar

section Entries

variable {F : Type*} [Field F] [CharP F 5]

theorem two_ne_zero_char_five : (2 : F) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff F 5 2).1 h1
  omega

theorem five_eq_zero_char_five : (5 : F) = 0 := by
  have := CharP.cast_eq_zero F 5
  exact_mod_cast this

omit [CharP F 5] in
theorem pow_five_fin_two (a b c e : F) :
    (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) F) ^ 5 =
      ((a + e) ^ 4 - 3 * (a + e) ^ 2 * (a * e - b * c) + (a * e - b * c) ^ 2) •
        (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) F) +
      (-(a * e - b * c) * (a + e) ^ 3 + 2 * (a + e) * (a * e - b * c) ^ 2) •
        (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem entries_false (a b c e f g h k κ u w : F)
    (hYdet : a * e - b * c ≠ 0) (hZdet : f * k - g * h ≠ 0)
    (hYn : ¬ (b = 0 ∧ c = 0 ∧ a = e)) (hZn : ¬ (g = 0 ∧ h = 0 ∧ f = k))
    (hY5 : (!![a, b; c, e] : Matrix (Fin 2) (Fin 2) F) ^ 5 = u • (1 : Matrix (Fin 2) (Fin 2) F))
    (hZ2 : (!![f, g; h, k] : Matrix (Fin 2) (Fin 2) F) * !![f, g; h, k] =
      w • (1 : Matrix (Fin 2) (Fin 2) F))
    (hc : (!![f, g; h, k] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, e] =
      κ • ((!![a, b; c, e] : Matrix (Fin 2) (Fin 2) F) * !![f, g; h, k])) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_char_five
  have h5 : (5 : F) = 0 := five_eq_zero_char_five
  rw [pow_five_fin_two] at hY5
  have y01 := congrFun (congrFun hY5 0) 1
  have y10 := congrFun (congrFun hY5 1) 0
  have y00 := congrFun (congrFun hY5 0) 0
  have y11 := congrFun (congrFun hY5 1) 1
  simp at y01 y10 y00 y11
  have hp : (a + e) ^ 4 - 3 * (a + e) ^ 2 * (a * e - b * c) + (a * e - b * c) ^ 2 = 0 := by
    by_contra hne
    apply hYn
    refine ⟨y01.resolve_left hne, y10.resolve_left hne, ?_⟩
    have : ((a + e) ^ 4 - 3 * (a + e) ^ 2 * (a * e - b * c) + (a * e - b * c) ^ 2) * (a - e) = 0 :=
      by linear_combination y00 - y11
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)
  have hd : (a + e) ^ 2 + (a * e - b * c) = 0 := by
    have : ((a + e) ^ 2 + (a * e - b * c)) ^ 2 = 0 := by
      linear_combination hp + ((a + e) ^ 2 * (a * e - b * c)) * h5
    exact (pow_eq_zero_iff two_ne_zero).1 this
  have ht : a + e ≠ 0 := fun ht => hYdet (by linear_combination hd - (a + e) * ht)
  have z01 : f * g + g * k = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hZ2 0) 1
  have z10 : h * f + k * h = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hZ2 1) 0
  have z00 : f * f + g * h = w := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hZ2 0) 0
  have z11 : h * g + k * k = w := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hZ2 1) 1
  have hftr : f + k = 0 := by
    by_contra hs
    have hg : g = 0 := by
      have : g * (f + k) = 0 := by linear_combination z01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hh : h = 0 := by
      have : h * (f + k) = 0 := by linear_combination z10
      exact (mul_eq_zero.1 this).resolve_right hs
    have hfk : f = k := by
      have : (f - k) * (f + k) = 0 := by linear_combination z00 - z11
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hs)
    exact hZn ⟨hg, hh, hfk⟩
  have hk : k = -f := by linear_combination hftr
  subst hk
  have c00 : f * a + g * c = κ * (a * f + b * h) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 0
  have c01 : f * b + g * e = κ * (a * g + b * -f) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 0) 1
  have c10 : h * a + -f * c = κ * (c * f + e * h) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 0
  have c11 : h * b + -f * e = κ * (c * g + e * -f) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hc 1) 1
  have hκ : κ ^ 2 = 1 := by
    have hdet := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_mul] at hdet
    simp only [Matrix.det_fin_two_of, Fintype.card_fin] at hdet
    have hne : (f * -f - g * h) * (a * e - b * c) ≠ 0 := mul_ne_zero hZdet hYdet
    apply mul_left_cancel₀ hne
    linear_combination -hdet
  have hκ' : (κ - 1) * (κ + 1) = 0 := by linear_combination hκ
  rcases mul_eq_zero.1 hκ' with hk1 | hk1
  ·
    have hκ1 : κ = 1 := by linear_combination hk1
    subst hκ1
    refine scalar_contradiction (a - e) b c f g h h2 ?_ ?_ ?_ ?_ ?_ ?_
    · linear_combination hd - (a * e - b * c) * h5
    · by_contra hne
      simp only [not_or, not_not, ne_eq] at hne
      exact hYn ⟨hne.2.1, hne.2.2, sub_eq_zero.1 hne.1⟩
    · linear_combination c01
    · linear_combination c10
    · linear_combination c00
    · intro hz
      apply hZdet
      linear_combination -hz
  ·
    have hκ1 : κ = -1 := by linear_combination hk1
    subst hκ1
    have hg : g = 0 := by
      have : g * (a + e) = 0 := by linear_combination c01
      exact (mul_eq_zero.1 this).resolve_right ht
    have hh : h = 0 := by
      have : h * (a + e) = 0 := by linear_combination c10
      exact (mul_eq_zero.1 this).resolve_right ht
    subst hg
    subst hh
    have hfa : f * a = 0 := by
      have : 2 * (f * a) = 0 := by linear_combination c00
      exact (mul_eq_zero.1 this).resolve_left h2
    have hfe : f * e = 0 := by
      have : 2 * (f * e) = 0 := by linear_combination -c11
      exact (mul_eq_zero.1 this).resolve_left h2
    have hf : f = 0 := by
      have : f * (a + e) = 0 := by linear_combination hfa + hfe
      exact (mul_eq_zero.1 this).resolve_right ht
    exact hZdet (by rw [hf]; ring)

omit [CharP F 5] in
theorem scalar_eq_of_entries (a : F) :
    (!![a, 0; 0, a] : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

omit [CharP F 5] in
theorem scalar_eq_smul_one (c : F) : Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) F) :=
  by
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem false_of_commute_five_two {y z : Matrix.ProjGenLinGroup (Fin 2) F}
    (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1) (hz2 : z * z = 1) (hz1 : z ≠ 1) (hc : y * z = z * y) :
    False := by
  obtain ⟨Y, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  obtain ⟨Z, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective z
  have hY5 : (Y ^ 5 : Matrix.GeneralLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_pow]
    exact hy5
  have hZ2 : (Z * Z : Matrix.GeneralLinearGroup (Fin 2) F) ∈
      Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) F) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one, map_mul]
    exact hz2
  obtain ⟨u, hu⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hY5
  obtain ⟨w, hw⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hZ2
  have hYn : ¬ ∃ c : F, (Y : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := fun h => by
    apply hy1
    rw [Matrix.ProjGenLinGroup.mk_eq_one]
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 (by
      obtain ⟨c, hc⟩ := h
      exact ⟨c, hc.symm⟩)
  have hZn : ¬ ∃ c : F, (Z : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) c := fun h => by
    apply hz1
    rw [Matrix.ProjGenLinGroup.mk_eq_one]
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 (by
      obtain ⟨c, hc⟩ := h
      exact ⟨c, hc.symm⟩)
  have hcomm : Matrix.ProjGenLinGroup.mk (Y * Z) = Matrix.ProjGenLinGroup.mk (Z * Y) := by
    rw [map_mul, map_mul]
    exact hc
  obtain ⟨κg, hκg, hκ⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff'.1 hcomm
  obtain ⟨κ, hκ'⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.1 hκg
  have hmat : (Z : Matrix (Fin 2) (Fin 2) F) * (Y : Matrix (Fin 2) (Fin 2) F) =
      κ • ((Y : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F)) := by
    have := congrArg Units.val hκ
    simp only [Units.val_mul] at this
    rw [← this, ← hκ', scalar_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
  have hYdet : (Y : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det Y).ne_zero
  have hZdet : (Z : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det Z).ne_zero
  have hY5m : (Y : Matrix (Fin 2) (Fin 2) F) ^ 5 = u • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have : ((Y ^ 5 : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (Y : Matrix (Fin 2) (Fin 2) F) ^ 5 := Units.val_pow_eq_pow_val _ _
    rw [← this, ← hu, scalar_eq_smul_one]
  have hZ2m : (Z : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F) =
      w • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have : ((Z * Z : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (Z : Matrix (Fin 2) (Fin 2) F) * (Z : Matrix (Fin 2) (Fin 2) F) := Units.val_mul _ _
    rw [← this, ← hw, scalar_eq_smul_one]
  obtain ⟨a, b, c, e, hYe⟩ : ∃ a b c e : F,
      (Y : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, e] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  obtain ⟨f, g, h, k, hZe⟩ : ∃ f g h k : F,
      (Z : Matrix (Fin 2) (Fin 2) F) = !![f, g; h, k] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hYe] at hYdet hY5m hmat hYn
  rw [hZe] at hZdet hZ2m hmat hZn
  rw [Matrix.det_fin_two_of] at hYdet hZdet
  refine entries_false a b c e f g h k κ u w hYdet hZdet ?_ ?_ hY5m hZ2m hmat
  · rintro ⟨hb, hc', hae⟩
    exact hYn ⟨a, by rw [← scalar_eq_of_entries, hb, hc', hae]⟩
  · rintro ⟨hg, hh, hfk⟩
    exact hZn ⟨f, by rw [← scalar_eq_of_entries, hg, hh, hfk]⟩

end Entries

end CFSG.EvenSporadicStandard.HSStd.HFI
