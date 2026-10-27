module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

variable {F : Type} [Field F]

theorem matrix_commute_of_commute_traceless (h2 : (2 : F) ≠ 0)
    {T X Y : Matrix (Fin 2) (Fin 2) F} (htr : T 1 1 = -T 0 0)
    (hns : T 0 1 ≠ 0 ∨ T 1 0 ≠ 0 ∨ T 0 0 ≠ 0) (hX : X * T = T * X) (hY : Y * T = T * Y) :
    X * Y = Y * X := by
  have eqs : ∀ Z : Matrix (Fin 2) (Fin 2) F, Z * T = T * Z →
      Z 0 1 * T 1 0 = T 0 1 * Z 1 0 ∧
      T 0 1 * (Z 0 0 - Z 1 1) = 2 * T 0 0 * Z 0 1 ∧
      2 * T 0 0 * Z 1 0 = T 1 0 * (Z 0 0 - Z 1 1) := by
    intro Z hZ
    have e : ∀ i j, (Z * T) i j = (T * Z) i j := fun i j => by rw [hZ]
    have e00 := e 0 0
    have e01 := e 0 1
    have e10 := e 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, htr] at e00 e01 e10
    refine ⟨?_, ?_, ?_⟩
    · linear_combination e00
    · linear_combination e01
    · linear_combination e10
  obtain ⟨x1, x2, x3⟩ := eqs X hX
  obtain ⟨y1, y2, y3⟩ := eqs Y hY
  set a := T 0 0
  set b := T 0 1
  set c := T 1 0
  have key : X 0 1 * Y 1 0 = Y 0 1 * X 1 0 ∧
      Y 0 1 * (X 0 0 - X 1 1) = X 0 1 * (Y 0 0 - Y 1 1) ∧
      X 1 0 * (Y 0 0 - Y 1 1) = Y 1 0 * (X 0 0 - X 1 1) := by
    rcases hns with hb | hc | ha
    · refine ⟨?_, ?_, ?_⟩
      · apply mul_left_cancel₀ hb
        linear_combination (-(X 0 1)) * y1 + (Y 0 1) * x1
      · apply mul_left_cancel₀ hb
        linear_combination (Y 0 1) * x2 - (X 0 1) * y2
      · apply mul_left_cancel₀ (mul_ne_zero hb hb)
        linear_combination (-(b * (Y 0 0 - Y 1 1))) * x1 + (X 0 1 * c) * y2 +
          (b * (X 0 0 - X 1 1)) * y1 - (Y 0 1 * c) * x2
    · by_cases hb : b = 0
      · have hxy : X 0 1 = 0 := by
          have := x1
          rw [hb, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_right hc
        have hyy : Y 0 1 = 0 := by
          have := y1
          rw [hb, zero_mul] at this
          exact (mul_eq_zero.mp this).resolve_right hc
        refine ⟨by rw [hxy, hyy]; ring, by rw [hxy, hyy]; ring, ?_⟩
        apply mul_left_cancel₀ hc
        linear_combination (-(X 1 0)) * y3 + (Y 1 0) * x3
      · refine ⟨?_, ?_, ?_⟩
        · apply mul_left_cancel₀ hb
          linear_combination (-(X 0 1)) * y1 + (Y 0 1) * x1
        · apply mul_left_cancel₀ hb
          linear_combination (Y 0 1) * x2 - (X 0 1) * y2
        · apply mul_left_cancel₀ (mul_ne_zero hb hb)
          linear_combination (-(b * (Y 0 0 - Y 1 1))) * x1 + (X 0 1 * c) * y2 +
            (b * (X 0 0 - X 1 1)) * y1 - (Y 0 1 * c) * x2
    · by_cases hb : b = 0
      · by_cases hc : c = 0
        · have h2a : 2 * a ≠ 0 := mul_ne_zero h2 ha
          have hx01 : X 0 1 = 0 := by
            have := x2
            rw [hb, zero_mul] at this
            exact (mul_eq_zero.mp this.symm).resolve_left h2a
          have hy01 : Y 0 1 = 0 := by
            have := y2
            rw [hb, zero_mul] at this
            exact (mul_eq_zero.mp this.symm).resolve_left h2a
          have hx10 : X 1 0 = 0 := by
            have := x3
            rw [hc, zero_mul] at this
            exact (mul_eq_zero.mp this).resolve_left h2a
          have hy10 : Y 1 0 = 0 := by
            have := y3
            rw [hc, zero_mul] at this
            exact (mul_eq_zero.mp this).resolve_left h2a
          refine ⟨?_, ?_, ?_⟩ <;> simp [hx01, hy01, hx10, hy10]
        · have hxy : X 0 1 = 0 := by
            have := x1
            rw [hb, zero_mul] at this
            exact (mul_eq_zero.mp this).resolve_right hc
          have hyy : Y 0 1 = 0 := by
            have := y1
            rw [hb, zero_mul] at this
            exact (mul_eq_zero.mp this).resolve_right hc
          refine ⟨by rw [hxy, hyy]; ring, by rw [hxy, hyy]; ring, ?_⟩
          apply mul_left_cancel₀ hc
          linear_combination (-(X 1 0)) * y3 + (Y 1 0) * x3
      · refine ⟨?_, ?_, ?_⟩
        · apply mul_left_cancel₀ hb
          linear_combination (-(X 0 1)) * y1 + (Y 0 1) * x1
        · apply mul_left_cancel₀ hb
          linear_combination (Y 0 1) * x2 - (X 0 1) * y2
        · apply mul_left_cancel₀ (mul_ne_zero hb hb)
          linear_combination (-(b * (Y 0 0 - Y 1 1))) * x1 + (X 0 1 * c) * y2 +
            (b * (X 0 0 - X 1 1)) * y1 - (Y 0 1 * c) * x2
  obtain ⟨k1, k2, k3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination k1
  · linear_combination k2
  · linear_combination k3
  · linear_combination -k1

theorem commute_lift_of_odd {T Z : GL (Fin 2) F} {l : F}
    (hl : (T : Matrix (Fin 2) (Fin 2) F) * T = l • 1) (hl0 : l ≠ 0)
    (hz : Matrix.ProjGenLinGroup.mk Z * Matrix.ProjGenLinGroup.mk T =
      Matrix.ProjGenLinGroup.mk T * Matrix.ProjGenLinGroup.mk Z)
    (hzo : Odd (orderOf (Matrix.ProjGenLinGroup.mk Z))) :
    (Z : Matrix (Fin 2) (Fin 2) F) * T = T * Z := by
  set t' : Matrix (Fin 2) (Fin 2) F := (T : Matrix (Fin 2) (Fin 2) F)
  set z' : Matrix (Fin 2) (Fin 2) F := (Z : Matrix (Fin 2) (Fin 2) F)
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hz
  obtain ⟨μ, hμ⟩ := hz
  have hμ' : (μ : F) • (z' * t') = t' * z' := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hμ
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [← this, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]
  have ht0 : t' ≠ 0 := by
    intro h
    have := T.det_ne_zero
    rw [show (T : Matrix (Fin 2) (Fin 2) F) = 0 from h, Matrix.det_zero] at this
    exact this rfl
  have hμ2 : (μ : F) ^ 2 = 1 := by
    have h1 : ((μ : F) ^ 2 * l) • z' = l • z' := by
      calc ((μ : F) ^ 2 * l) • z' = (μ : F) • ((μ : F) • (z' * t')) * t' := by
            rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hl, Matrix.mul_smul,
              Matrix.mul_one, smul_smul, smul_smul, pow_two, mul_assoc]
        _ = (μ : F) • (t' * z') * t' := by rw [hμ']
        _ = t' * ((μ : F) • (z' * t')) := by
            rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
        _ = t' * (t' * z') := by rw [hμ']
        _ = l • z' := by rw [← Matrix.mul_assoc, hl, Matrix.smul_mul, Matrix.one_mul]
    have hz0 : z' ≠ 0 := by
      intro h
      have := Z.det_ne_zero
      rw [show (Z : Matrix (Fin 2) (Fin 2) F) = 0 from h, Matrix.det_zero] at this
      exact this rfl
    have h2 : ((μ : F) ^ 2 * l - l) • z' = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · have : ((μ : F) ^ 2 - 1) * l = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hl0)
    · exact absurd h hz0
  set m := orderOf (Matrix.ProjGenLinGroup.mk Z)
  have hpow : ∀ k : ℕ, ((μ : F) ^ k) • (z' ^ k * t') = t' * z' ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc ((μ : F) ^ (k + 1)) • (z' ^ (k + 1) * t') =
          (μ : F) • ((μ : F) ^ k • (z' ^ k * (z' * t'))) := by
            rw [pow_succ (μ : F) k, pow_succ z' k, Matrix.mul_assoc, smul_smul,
              mul_comm ((μ : F) ^ k) (μ : F)]
        _ = (μ : F) ^ k • (z' ^ k * ((μ : F) • (z' * t'))) := by
            rw [Matrix.mul_smul, smul_comm]
        _ = (μ : F) ^ k • (z' ^ k * (t' * z')) := by rw [hμ']
        _ = ((μ : F) ^ k • (z' ^ k * t')) * z' := by
            rw [Matrix.smul_mul, Matrix.mul_assoc]
        _ = t' * z' ^ k * z' := by rw [ih]
        _ = t' * z' ^ (k + 1) := by rw [Matrix.mul_assoc, ← pow_succ]
  have hzm : Matrix.ProjGenLinGroup.mk (Z ^ m) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hzm
  obtain ⟨ν, hν⟩ := hzm
  have hν' : z' ^ m = (ν : F) • 1 := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hν
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hμm : (μ : F) ^ m = 1 := by
    have h1 := hpow m
    rw [hν', Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h1
    have h2 : ((μ : F) ^ m * ν - ν) • t' = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · have : ((μ : F) ^ m - 1) * ν = 0 := by linear_combination h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ν.ne_zero)
    · exact absurd h ht0
  have hμ1 : (μ : F) = 1 := by
    have hg : Nat.gcd m 2 = 1 := Nat.coprime_two_right.mpr hzo
    have := (pow_gcd_eq_one (a := (μ : F))).mpr ⟨hμm, hμ2⟩
    rwa [hg, pow_one] at this
  rw [hμ1, one_smul] at hμ'
  exact hμ'

theorem pgl2_commute_of_odd (h2 : (2 : F) ≠ 0) {t x y : PGL2 F} (ht : t * t = 1)
    (ht1 : t ≠ 1) (hx : x * t = t * x) (hy : y * t = t * y) (hxo : Odd (orderOf x))
    (hyo : Odd (orderOf y)) : x * y = y * x := by
  obtain ⟨T, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective t
  obtain ⟨X, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective y
  have hTT : Matrix.ProjGenLinGroup.mk (T * T) = 1 := by rw [map_mul]; exact ht
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hTT
  obtain ⟨l, hl⟩ := hTT
  set t' : Matrix (Fin 2) (Fin 2) F := (T : Matrix (Fin 2) (Fin 2) F)
  have hl' : t' * t' = (l : F) • 1 := by
    have := congrArg (fun C : GL (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F)) hl
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_mul] at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have e : ∀ i j, (t' * t') i j = ((l : F) • (1 : Matrix (Fin 2) (Fin 2) F)) i j :=
    fun i j => by rw [hl']
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_one, mul_zero] at e00 e01 e10 e11
  have hns : ¬ (t' 0 1 = 0 ∧ t' 1 0 = 0 ∧ t' 0 0 = t' 1 1) := by
    rintro ⟨h01, h10, h00⟩
    apply ht1
    rw [Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
    refine ⟨t' 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, h01, h10, h00, t']
  have htr : t' 1 1 = -t' 0 0 := by
    by_contra hne
    have hs : t' 0 0 + t' 1 1 ≠ 0 := fun h => hne (by linear_combination h)
    have h01 : t' 0 1 = 0 := by
      have : t' 0 1 * (t' 0 0 + t' 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have h10 : t' 1 0 = 0 := by
      have : t' 1 0 * (t' 0 0 + t' 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have h00 : t' 0 0 = t' 1 1 := by
      have : (t' 0 0 - t' 1 1) * (t' 0 0 + t' 1 1) = 0 := by
        linear_combination e00 - e11 - t' 0 1 * e10 + t' 1 0 * e01 - t' 1 0 * e01 +
          t' 0 1 * e10
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hs)
    exact hns ⟨h01, h10, h00⟩
  have hns' : t' 0 1 ≠ 0 ∨ t' 1 0 ≠ 0 ∨ t' 0 0 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h01, h10, h00⟩ := h
    exact hns ⟨h01, h10, by rw [htr, h00, neg_zero]⟩
  have hX := commute_lift_of_odd hl' l.ne_zero hx hxo
  have hY := commute_lift_of_odd hl' l.ne_zero hy hyo
  have hXY := matrix_commute_of_commute_traceless h2 htr hns' hX hY
  rw [← map_mul, ← map_mul]
  congr 1
  ext i j
  have := congrFun (congrFun hXY i) j
  simpa using this

end CFSG.ComponentClassification.AutL2Facts
