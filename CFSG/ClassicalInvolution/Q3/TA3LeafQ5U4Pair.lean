module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5U4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.Assembly.LowTwoRank StabU HBlocks TBlocks UnitaryOut UnitaryConj Subgroup

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem four_le_card : 4 ≤ Nat.card K := by
  rw [h.card]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left h.prime.two_le 2
    _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right h.prime.pos (by have := h.one_le; omega)

include h in
theorem exists_pair_frame (hp2 : p ≠ 2) (hq : p ^ f % 4 = 1) (X : unitarySU p f K 4)
    (hX : ((X : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (X : GL (Fin 4) K) = -1) :
    ∃ (P : GL (Fin 4) K) (l : K), uStar h (P : Matrix (Fin 4) (Fin 4) K) *
        (P : Matrix (Fin 4) (Fin 4) K) = stdG ∧ l ^ 2 = -1 ∧ h.bar l * l = -1 ∧
      cP P X = X1 l := by
  classical
  have : Finite K := h.finite
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 = -1 := by
    let : Fintype K := Fintype.ofFinite K
    have hcK : Fintype.card K % 4 = 1 := by
      rw [Fintype.card_eq_nat_card, h.card, pow_mul, Nat.pow_mod]
      rw [show p ^ 2 % 4 = 1 by
        rcases Nat.even_or_odd p with he | ho
        · exfalso
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two h.prime).1
            (even_iff_two_dvd.1 he)).symm
        · obtain ⟨t, rfl⟩ := ho
          ring_nf
          omega]
      simp
    obtain ⟨r, hr⟩ := (FiniteField.isSquare_neg_one_iff (F := K)).2 (by omega)
    exact ⟨r, by rw [sq, ← hr]⟩
  have hbl : h.bar l * l = -1 := by
    have := norm_eq_neg_one_of_sq h hq hl
    rw [UnitaryFieldData.norm, mul_comm] at this
    exact this
  obtain ⟨Pm, hPm, hXP⟩ := exists_hyperbolic_basis h hp2 hq X hX hl
  have hPdet : Pm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPm
    have hGd : (stdG : Matrix (Fin 4) (Fin 4) K).det = 1 := det_stdG
    rw [det_mul, h0, mul_zero, hGd] at this
    exact zero_ne_one this
  set P : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hPdef
  have hPv : (P : Matrix (Fin 4) (Fin 4) K) = Pm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  refine ⟨P, l, by rw [hPv]; exact hPm, hl, hbl, ?_⟩
  rw [cP, Matrix.mul_assoc, hPv, hXP, ← Matrix.mul_assoc, ← hPv, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul, X1_eq_stdDl]

@[expose] noncomputable def dualU (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  ((((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ

theorem dualU_one : dualU h 1 = 1 := by
  rw [dualU, inv_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one _ (map_zero _) (map_one _), transpose_one]

theorem dualU_mul (a b : Matrix.SpecialLinearGroup (Fin 2) K) :
    dualU h (a * b) = dualU h a * dualU h b := by
  rw [dualU, dualU, dualU, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul,
    transpose_mul]

theorem star_mul_dualU (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((a : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * dualU h a = 1 := by
  rw [dualU, ← transpose_mul, ← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _) (map_one _),
    transpose_one]

theorem dualU_star_mul (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((dualU h a).map h.bar)ᵀ * (a : Matrix (Fin 2) (Fin 2) K) = 1 := by
  have hbb : (h.bar ∘ h.bar) = id := funext h.bar_bar
  rw [dualU, transpose_map, transpose_transpose, Matrix.map_map, hbb, Matrix.map_id,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem bd_mul_stdG_mul_bd {x y a d : Matrix (Fin 2) (Fin 2) K}
    (h1 : x * d = 1) (h2 : y * a = 1) : bd x y * stdG * bd a d = stdG := by
  have e : ∀ i j, x i 0 * d 0 j + x i 1 * d 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h1 i) j
  have e' : ∀ i j, y i 0 * a 0 j + y i 1 * a 1 j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h2 i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  have f00 := e' 0 0
  have f01 := e' 0 1
  have f10 := e' 1 0
  have f11 := e' 1 1
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11 f00 f01 f10 f11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, stdG, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first
    | linear_combination e00 | linear_combination e01 | linear_combination e10
    | linear_combination e11 | linear_combination f00 | linear_combination f01
    | linear_combination f10 | linear_combination f11

theorem unitary_bd_dualU (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    uStar h (bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a)) * stdG *
      bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a) = stdG := by
  rw [uStar, map_bd, transpose_bd]
  exact bd_mul_stdG_mul_bd (star_mul_dualU h a) (dualU_star_mul h a)

theorem det_bd_dualU (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    (bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a)).det = 1 := by
  rw [det_bd, Matrix.SpecialLinearGroup.det_coe, one_mul, dualU, det_transpose,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

variable {P : GL (Fin 4) K}
  (hP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = stdG)

@[expose] noncomputable def pairHom : Matrix.SpecialLinearGroup (Fin 2) K →* unitarySU p f K 4 where
  toFun a := hypSU h P hP (bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a)) (unitary_bd_dualU h a)
    (det_bd_dualU h a)
  map_one' := by
    apply eq_of_cP_eq P
    simp only [cP_hypSU, Matrix.SpecialLinearGroup.coe_one, dualU_one, bd_one, cP_one]
  map_mul' a b := by
    apply eq_of_cP_eq P
    simp only [cP_mul, cP_hypSU, Matrix.SpecialLinearGroup.coe_mul, dualU_mul, bd_mul]

theorem cP_pairHom (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    cP P (pairHom h hP a) = bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a) :=
  cP_hypSU h P hP _ (unitary_bd_dualU h a) (det_bd_dualU h a)

theorem val_pairHom (a : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((pairHom h hP a : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (P : Matrix (Fin 4) (Fin 4) K) * bd (a : Matrix (Fin 2) (Fin 2) K) (dualU h a) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) :=
  val_hypSU h P hP _ (unitary_bd_dualU h a) (det_bd_dualU h a)

theorem pairHom_uu (c : K) : pairHom h hP (PSpL.slU c) = uU h P hP c := by
  apply eq_of_cP_eq P
  rw [cP_pairHom, cP_uU, dualU, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, U12, uu, PSpL.slU]

theorem pairHom_ll (c : K) : pairHom h hP (PSpL.slL c) = uL h P hP c := by
  apply eq_of_cP_eq P
  rw [cP_pairHom, cP_uL, dualU, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bd, U21, ll, PSpL.slL]

theorem hasUnipU_pair (μ : K) :
    HasUnipU h P hP μ ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range :=
  ⟨⟨PSpL.slU 1, by rw [MonoidHom.comp_apply, pairHom_uu]; rfl⟩,
    ⟨PSpL.slL 1, by rw [MonoidHom.comp_apply, pairHom_ll]; rfl⟩,
    ⟨PSpL.slU μ, by rw [MonoidHom.comp_apply, pairHom_uu]; rfl⟩⟩

theorem range_pairHom_le_centralizer {X : unitarySU p f K 4} {l : K} (hX : cP P X = X1 l) :
    ((QuotientGroup.mk' (scal p f K)).comp (pairHom h hP)).range ≤
      centralizer {QuotientGroup.mk' (scal p f K) X} := by
  rintro _ ⟨a, rfl⟩
  rw [mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  apply eq_of_cP_eq P
  rw [cP_mul, cP_mul, cP_pairHom, hX, bd_comm_X1]

end CFSG.ClassicalInvolution.Q3.TA3.Q5U4
