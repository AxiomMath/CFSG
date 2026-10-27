module

public import CFSG.Quasithin.Vol2.Ch11SecBK10H
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Quasithin.Vol2.Ch11.SecD.BK10.L2
open scoped MatrixGroups

section

variable {K : Type} [Field K]

theorem l2fld_poly_aux {p q r s x1 x2 x3 x4 : K} (hns : ¬ (q = 0 ∧ r = 0 ∧ p = s))
    (e11 : x1 * p + x2 * r = p * x1 + q * x3) (e12 : x1 * q + x2 * s = p * x2 + q * x4)
    (e21 : x3 * p + x4 * r = r * x1 + s * x3) (e22 : x3 * q + x4 * s = r * x2 + s * x4) :
    ∃ a b : K, x1 = a + b * p ∧ x2 = b * q ∧ x3 = b * r ∧ x4 = a + b * s := by
  by_cases hq : q = 0
  · by_cases hr : r = 0
    · have hps : p ≠ s := fun h => hns ⟨hq, hr, h⟩
      have hd : p - s ≠ 0 := sub_ne_zero.2 hps
      have h2 : x2 = 0 := by
        subst hq
        have : x2 * (s - p) = 0 := by linear_combination e12
        exact (mul_eq_zero.1 this).resolve_right (fun h => hd (by linear_combination -h))
      have h3 : x3 = 0 := by
        subst hr
        have : x3 * (p - s) = 0 := by linear_combination e21
        exact (mul_eq_zero.1 this).resolve_right hd
      obtain ⟨b, hb⟩ : ∃ b, x1 - x4 = b * (p - s) := ⟨(x1 - x4) / (p - s), by field_simp⟩
      refine ⟨x1 - b * p, b, by ring, by rw [h2, hq, mul_zero], by rw [h3, hr, mul_zero], ?_⟩
      linear_combination -hb
    · obtain ⟨b, hb⟩ : ∃ b, x3 = b * r := ⟨x3 / r, by field_simp⟩
      subst hb
      have h2 : x2 = 0 := by
        subst hq
        have : r * x2 = 0 := by linear_combination -e22
        exact (mul_eq_zero.1 this).resolve_left hr
      have h4 : x1 - x4 = b * (p - s) := by
        have : r * (x1 - x4 - b * (p - s)) = 0 := by linear_combination -e21
        have := (mul_eq_zero.1 this).resolve_left hr
        linear_combination this
      refine ⟨x1 - b * p, b, by ring, by rw [h2, hq, mul_zero], rfl, ?_⟩
      linear_combination -h4
  · obtain ⟨b, hb⟩ : ∃ b, x2 = b * q := ⟨x2 / q, by field_simp⟩
    subst hb
    have h3 : x3 = b * r := by
      have : q * (x3 - b * r) = 0 := by linear_combination -e11
      have := (mul_eq_zero.1 this).resolve_left hq
      linear_combination this
    have h4 : x1 - x4 = b * (p - s) := by
      have : q * (x1 - x4 - b * (p - s)) = 0 := by linear_combination e12
      have := (mul_eq_zero.1 this).resolve_left hq
      linear_combination this
    refine ⟨x1 - b * p, b, by ring, rfl, h3, ?_⟩
    linear_combination -h4

theorem l2fld_exists_poly {Y X : Matrix (Fin 2) (Fin 2) K} (hY : ¬ ∃ c : K, Y = c • 1)
    (hX : X * Y = Y * X) : ∃ a b : K, X = a • 1 + b • Y := by
  have e11 := congrFun (congrFun hX 0) 0
  have e12 := congrFun (congrFun hX 0) 1
  have e21 := congrFun (congrFun hX 1) 0
  have e22 := congrFun (congrFun hX 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e11 e12 e21 e22
  have hns : ¬ (Y 0 1 = 0 ∧ Y 1 0 = 0 ∧ Y 0 0 = Y 1 1) := by
    rintro ⟨h1, h2, h3⟩
    apply hY
    refine ⟨Y 0 0, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  obtain ⟨a, b, h1, h2, h3, h4⟩ := l2fld_poly_aux hns e11 e12 e21 e22
  refine ⟨a, b, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem l2fld_commute_of_nonscalar {Y X X' : Matrix (Fin 2) (Fin 2) K}
    (hY : ¬ ∃ c : K, Y = c • 1) (hX : X * Y = Y * X) (hX' : X' * Y = Y * X') :
    X * X' = X' * X := by
  obtain ⟨a, b, rfl⟩ := l2fld_exists_poly hY hX
  obtain ⟨a', b', rfl⟩ := l2fld_exists_poly hY hX'
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem l2fld_pow_comm {M N : Matrix (Fin 2) (Fin 2) K} {r : K} (h : N * M = r • (M * N))
    (k : ℕ) : N * M ^ k = r ^ k • (M ^ k * N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc, h,
      Matrix.mul_smul, ← Matrix.mul_assoc, pow_succ, smul_smul]

theorem l2fld_fixed_comm_mat (G : GL (Fin 2) K) (c : Kˣ)
    (hG3 : G ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c) (A : SL(2, K))
    (h : psl2QuotientMap K (conjSL G A) = psl2QuotientMap K A) :
    (G : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) * (G : Matrix (Fin 2) (Fin 2) K) := by
  have hcl : (conjSL G A)⁻¹ * A ∈ Subgroup.center (SL(2, K)) := (QuotientGroup.eq).1 h
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcl
  rw [Fintype.card_fin] at hr
  have hz : A = conjSL G A * ((conjSL G A)⁻¹ * A) := by simp
  have hN : (A : Matrix (Fin 2) (Fin 2) K) = r • ((G : Matrix (Fin 2) (Fin 2) K) * A *
      ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
    conv_lhs => rw [hz]
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hrA, coe_conjSL, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal]
  set M := (G : Matrix (Fin 2) (Fin 2) K) with hM
  set N := (A : Matrix (Fin 2) (Fin 2) K) with hNdef
  have hinv : ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have R1 : N * M = r • (M * N) := by
    have h1 : N * M = (r • (M * N * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))) * M := by
      rw [← hN]
    rw [h1, Matrix.smul_mul, Matrix.mul_assoc (M * N), hinv, Matrix.mul_one]
  have hM3 : M ^ 3 = (c : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) hG3
    simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] at this ⊢
    exact this
  have H3 := l2fld_pow_comm R1 3
  rw [hM3] at H3
  have hdet : N.det = 1 := A.2
  have hij : ∃ i j, N i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    rw [Matrix.det_fin_two, hcon 0 0, hcon 1 1, hcon 0 1, hcon 1 0] at hdet
    simp at hdet
  obtain ⟨i₀, j₀, hne⟩ := hij
  have hr3 : r ^ 3 = 1 := by
    have h1 := congrFun (congrFun H3 i₀) j₀
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul] at h1
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    have : (c : K) * N i₀ j₀ * (1 - r ^ 3) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hc0 hne)
    · linear_combination -h
  have hr1 : r = 1 := by
    calc r = r * r ^ 2 := by rw [hr, mul_one]
      _ = r ^ 3 := by ring
      _ = 1 := hr3
  rw [hr1, one_smul] at R1
  exact R1.symm

theorem l2fld_fixed_comm (G : GL (Fin 2) K) (c : Kˣ)
    (hG3 : G ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (hGn : ∀ d : Kˣ, G ≠ Matrix.GeneralLinearGroup.scalar (Fin 2) d) (x y : PSL2 K)
    (hx : pglAction K (ProjGenLinGroup.mk G) x = x) (hy : pglAction K (ProjGenLinGroup.mk G) y = y) :
    x * y = y * x := by
  obtain ⟨A, rfl⟩ := (psl2QuotientMap_surjective (K := K)) x
  obtain ⟨B, rfl⟩ := (psl2QuotientMap_surjective (K := K)) y
  rw [pglAction_mk] at hx hy
  have hA := l2fld_fixed_comm_mat G c hG3 A hx
  have hB := l2fld_fixed_comm_mat G c hG3 B hy
  have hns : ¬ ∃ d : K, (G : Matrix (Fin 2) (Fin 2) K) = d • 1 := by
    rintro ⟨d, hd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      have := G.isUnit.ne_zero
      apply this
      simp at hd
    exact hGn (Units.mk0 d hd0) (Units.ext (by
      rw [hd, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]; rfl))
  have hcomm : (A : Matrix (Fin 2) (Fin 2) K) * B = B * A :=
    l2fld_commute_of_nonscalar hns hA.symm hB.symm
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hcomm

end

end CFSG.HardMathSupport.Solomon.Coordinator
