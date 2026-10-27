module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineE3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine GenLocL3NineR3 GenLocL3NineE3
open scoped MatrixGroups Classical

namespace GenLocL3NineE2

variable {K : Type} [Field K]

theorem word_identity (ι : K) (hι : ι * ι = -1) (h3 : (3 : K) = 0) :
    !![ι, ι, 0; ι, -ι, 0; 0, 0, -1] * !![ι, 0, 0; 0, 1 + ι, 0; 0, 0, 1 + ι] *
      !![ι, ι, 0; ι, -ι, 0; 0, 0, -1] * !![ι, 0, 0; 0, 1 - ι, 0; 0, 0, ι - 1] *
      !![-ι, ι, 0; -ι, -ι, 0; 0, 0, 1] = (!![1, ι, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring_nf
  · linear_combination (-2 * ι ^ 3 - 2 * ι ^ 2 + 3 * ι + 2) * hι + (-ι - 1) * h3
  · linear_combination (2 * ι ^ 3 - ι) * hι
  · linear_combination (2 * ι ^ 3 - 3 * ι) * hι + ι * h3
  · linear_combination (2 * ι ^ 3 - 2 * ι ^ 2 - 3 * ι + 2) * hι + (ι - 1) * h3
  · linear_combination hι + (-1 : K) * h3

theorem slConj_diag3_of_diag (u : Fin 3 → Kˣ) (g : SL(3, K))
    (hg : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).IsDiag) : slConjugation 3 K (diag3 u) g = g := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_diag3, coe_diag3_inv, ← hg.diagonal_diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  have : ((u i : Kˣ) : K) ≠ 0 := (u i).ne_zero
  simp only [Units.val_inv_eq_inv_val]
  field_simp

theorem torus_mem [Finite K] (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K)
    (hA : IsRank23 ↥D) [Finite ↥D]
    (hF : ∀ (y : D) (u : Fin 3 → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε ≤ 1 →
      (y : MulAut (LinearFlag.projectiveSL 3 K)) = LinearFlag.conjAut 3 K (diag3 u) *
        LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε → σ = 1)
    (g : SL(3, K)) (hg : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    LinearFlag.proj 3 K g ∈ gammaAct D.subtype := by
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  refine le_gammaAct D.subtype (adm_comap_noDual hA.1 D.subtype hα) ?_
  rw [GenLocBasic.mem_fixedIn_map]
  intro e he
  obtain ⟨x, σ, hx, hax⟩ := he
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  have hσ := hF e u σ 0 (Nat.zero_le 1) (by rw [pow_zero, mul_one]; exact hax)
  subst hσ
  have : D.subtype e = LinearFlag.conjAut 3 K (diag3 u) := by
    rw [hax, map_one, mul_one]
  rw [this, LinearFlag.conjAut_proj, slConj_diag3_of_diag u g hg]

theorem exists_cube_root [Finite K] (hK : Nat.card K = 9) (c : Kˣ) : ∃ μ : Kˣ, μ ^ 3 = c := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hcard : Fintype.card Kˣ = 8 := by rw [Fintype.card_units, hK']
  have hinj : Function.Injective (fun x : Kˣ => x ^ 3) := by
    intro x y hxy
    have h3 : (x / y) ^ 3 = 1 := by rw [div_pow]; simp only at hxy; rw [hxy]; exact div_self' _
    have h8 : (x / y) ^ 8 = 1 := by rw [← hcard]; exact pow_card_eq_one
    have h1 : x / y = 1 := by
      have := pow_gcd_eq_one.2 ⟨h3, h8⟩
      simpa using this
    exact div_eq_one.1 h1
  obtain ⟨μ, hμ⟩ := (Finite.injective_iff_surjective.1 hinj) c
  exact ⟨μ, hμ⟩

theorem exists_diag_sqrt [Finite K] (hK : Nat.card K = 9) (v : Fin 3 → Kˣ)
    (h1 : IsSquare ((v 0 : K) * v 1)) (h2 : IsSquare ((v 0 : K) * v 2)) :
    ∃ (p : Fin 3 → Kˣ) (lam : Kˣ), (∀ i, ((p i : Kˣ) : K) * p i = lam * v i) ∧ p 0 * p 1 * p 2 = 1 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have ha0 : a ≠ 0 := by
    rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by
    rintro rfl; simp at hb
  let p' : Fin 3 → Kˣ := ![v 0, Units.mk0 a ha0, Units.mk0 b hb0]
  obtain ⟨μ, hμ⟩ := exists_cube_root hK (p' 0 * p' 1 * p' 2)⁻¹
  refine ⟨fun i => μ * p' i, μ * μ * v 0, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [p']; ring
    · simp [p']; linear_combination (-((μ : K) * μ)) * ha
    · simp [p']; linear_combination (-((μ : K) * μ)) * hb
  · have h3 : μ ^ 3 = μ * μ * μ := by simp [pow_succ]
    have : (μ * p' 0) * (μ * p' 1) * (μ * p' 2) = μ ^ 3 * (p' 0 * p' 1 * p' 2) := by
      rw [h3]; ac_rfl
    show (μ * p' 0) * (μ * p' 1) * (μ * p' 2) = 1
    rw [this, hμ, inv_mul_cancel]

theorem reflection_conj (v p : Fin 3 → Kˣ) (lam : Kˣ) (hp : ∀ i, ((p i : Kˣ) : K) * p i = lam * v i) :
    (LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K) * LinearFlag.conjAut 3 K (diag3 p) =
      LinearFlag.conjAut 3 K (diag3 p) * LinearFlag.dualAut 3 K := by
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K) (diag3 p)
  have hinv : GeneralLinearGroup.inverseTranspose (diag3 p) = diag3 (fun i => (p i)⁻¹) := by
    apply Units.ext
    rw [coe_inverseTranspose_diag3, coe_diag3]
  have hmul : diag3 v * diag3 (fun i => (p i)⁻¹) = diag3 (fun i => lam⁻¹ * p i) := by
    apply Units.ext
    rw [Units.val_mul, coe_diag3, coe_diag3, coe_diag3, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have h0 : ((p i : Kˣ) : K) ≠ 0 := (p i).ne_zero
    have h1 : (lam : K) ≠ 0 := lam.ne_zero
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination (-1 : K) * hp i
  calc (LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K) * LinearFlag.conjAut 3 K (diag3 p)
      = LinearFlag.conjAut 3 K (diag3 v) * (LinearFlag.dualAut 3 K * LinearFlag.conjAut 3 K (diag3 p)) := by
        simp only [mul_assoc]
    _ = LinearFlag.conjAut 3 K (diag3 v) * (LinearFlag.conjAut 3 K (diag3 (fun i => (p i)⁻¹)) *
          LinearFlag.dualAut 3 K) := by rw [s2, hinv]
    _ = LinearFlag.conjAut 3 K (diag3 v * diag3 (fun i => (p i)⁻¹)) * LinearFlag.dualAut 3 K := by
        rw [map_mul, mul_assoc]
    _ = LinearFlag.conjAut 3 K (diag3 (fun i => lam⁻¹ * p i)) * LinearFlag.dualAut 3 K := by rw [hmul]
    _ = LinearFlag.conjAut 3 K (diag3 p) * LinearFlag.dualAut 3 K := by rw [conjAut_diag3_smul]

theorem slConj_diag3_block (w : Fin 3 → Kˣ) (h01 : w 0 = w 1) (X : SL(3, K))
    (h02 : (X : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h12 : (X : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h20 : (X : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (X : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    slConjugation 3 K (diag3 w) X = X := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, coe_diag3, coe_diag3_inv]
  have h2 : ((w 2 : Kˣ) : K) ≠ 0 := (w 2).ne_zero
  have h0 : ((w 0 : Kˣ) : K) ≠ 0 := (w 0).ne_zero
  have h01' : ((w 0 : Kˣ) : K) = (w 1 : K) := by rw [h01]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Units.val_inv_eq_inv_val, h02, h12, h20, h21, ← h01']
  all_goals field_simp

theorem inv_transpose_eq_of_orth (X : SL(3, K)) (hX : X.transpose * X = 1) : (X⁻¹).transpose = X := by
  have h1 : X * X.transpose = 1 := mul_eq_one_comm.1 hX
  have : X⁻¹ = X.transpose := inv_eq_of_mul_eq_one_right h1
  rw [this]
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose]

theorem orth_mem [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) (hshape : ShapeE2 D) (X : SL(3, K)) (hX : X.transpose * X = 1)
    (h02 : (X : Matrix (Fin 3) (Fin 3) K) 0 2 = 0) (h12 : (X : Matrix (Fin 3) (Fin 3) K) 1 2 = 0)
    (h20 : (X : Matrix (Fin 3) (Fin 3) K) 2 0 = 0) (h21 : (X : Matrix (Fin 3) (Fin 3) K) 2 1 = 0) :
    LinearFlag.proj 3 K X ∈ gammaAct D.subtype := by
  obtain ⟨hF, hK3, r, v, hrv, hsqv⟩ := hshape
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  obtain ⟨τ, w, hτ1, hτw, hτm⟩ := hK3 2
  have hw01 : w 0 = w 1 := by simpa [crd] using hτm
  have h1 : IsSquare ((v 0 : K) * v 1) := by simpa [crd] using hsqv 2
  have h2 : IsSquare ((v 0 : K) * v 2) := by simpa [crd] using hsqv 1
  obtain ⟨p, lam, hp, hdet⟩ := exists_diag_sqrt hK v h1 h2
  let P : SL(3, K) := ⟨(diag3 p : Matrix (Fin 3) (Fin 3) K), by
    rw [coe_diag3, Matrix.det_diagonal, Fin.prod_univ_three]
    exact congrArg Units.val hdet⟩
  have hP : LinearFlag.proj 3 K P ∈ gammaAct D.subtype :=
    torus_mem D hfs hA hF P (by show (diag3 p : Matrix (Fin 3) (Fin 3) K).IsDiag; exact isDiag_diag3 p)
  have hPgl : SpecialLinearGroup.toGL P = diag3 p := Units.ext rfl
  have hconj : LinearFlag.conjAut 3 K (diag3 p) = MulAut.conj (LinearFlag.proj 3 K P) := by
    rw [← hPgl]; exact LinearFlag.conjAut_toGL P
  set x : LinearFlag.projectiveSL 3 K := LinearFlag.proj 3 K X with hx
  have hδx : LinearFlag.dualAut 3 K x = x := by
    rw [hx, LinearFlag.dualAut_proj, inv_transpose_eq_of_orth X hX]
  have hτx : LinearFlag.conjAut 3 K (diag3 w) x = x := by
    rw [hx, LinearFlag.conjAut_proj, slConj_diag3_block w hw01 X h02 h12 h20 h21]
  have hrδ : (r : MulAut (LinearFlag.projectiveSL 3 K)) =
      LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K := by
    rw [hrv, pow_one, map_one, mul_one]
  have hcomm : LinearFlag.conjAut 3 K (diag3 w) * LinearFlag.conjAut 3 K (diag3 p) =
      LinearFlag.conjAut 3 K (diag3 p) * LinearFlag.conjAut 3 K (diag3 w) := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diag3, coe_diag3, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hfixτ : (τ : MulAut (LinearFlag.projectiveSL 3 K)) (LinearFlag.conjAut 3 K (diag3 p) x) =
      LinearFlag.conjAut 3 K (diag3 p) x := by
    rw [hτw]
    have := congrArg (fun φ : MulAut (LinearFlag.projectiveSL 3 K) => φ x) hcomm
    simp only [MulAut.mul_apply] at this
    rw [this, hτx]
  have hfixr : (r : MulAut (LinearFlag.projectiveSL 3 K)) (LinearFlag.conjAut 3 K (diag3 p) x) =
      LinearFlag.conjAut 3 K (diag3 p) x := by
    rw [hrδ]
    have := congrArg (fun φ : MulAut (LinearFlag.projectiveSL 3 K) => φ x)
      (reflection_conj v p lam hp)
    simp only [MulAut.mul_apply] at this
    rw [MulAut.mul_apply, this, hδx]
  have hr1 : r ≠ 1 := by
    intro h
    apply reflection_not_mem_noDual hrv
    rw [h]
    exact (noDual K).one_mem
  have hτr : τ ≠ r := by
    intro h
    apply reflection_not_mem_noDual hrv
    rw [← h, hτw]
    exact ⟨diag3 w, 1, isDiag_diag3 w, by rw [map_one, mul_one]⟩
  have hE := adm_closure_pair hA.1 h8 τ r hτ1 hr1 hτr
  have hfix : ∀ e ∈ Subgroup.closure ({τ, r} : Set ↥D),
      (D.subtype e) (LinearFlag.conjAut 3 K (diag3 p) x) = LinearFlag.conjAut 3 K (diag3 p) x := by
    intro e he
    refine Subgroup.closure_induction
      (p := fun e _ => (D.subtype e) (LinearFlag.conjAut 3 K (diag3 p) x) = LinearFlag.conjAut 3 K (diag3 p) x)
      ?_ ?_ ?_ ?_ he
    · rintro y (rfl | rfl)
      · exact hfixτ
      · exact hfixr
    · simp
    · intro a b _ _ ha hb
      rw [map_mul, MulAut.mul_apply, hb, ha]
    · intro a _ ha
      rw [map_inv]
      calc ((D.subtype a)⁻¹) (LinearFlag.conjAut 3 K (diag3 p) x) =
            ((D.subtype a)⁻¹) ((D.subtype a) (LinearFlag.conjAut 3 K (diag3 p) x)) := by rw [ha]
        _ = LinearFlag.conjAut 3 K (diag3 p) x := by simp
  have hy : LinearFlag.conjAut 3 K (diag3 p) x ∈ gammaAct D.subtype :=
    le_gammaAct D.subtype hE ((GenLocBasic.mem_fixedIn_map _ _ _).2 hfix)
  have hback : x = (LinearFlag.proj 3 K P)⁻¹ * (LinearFlag.conjAut 3 K (diag3 p) x) *
      LinearFlag.proj 3 K P := by
    rw [hconj, MulAut.conj_apply]; group
  rw [hx] at hback ⊢
  rw [hback]
  exact (gammaAct D.subtype).mul_mem ((gammaAct D.subtype).mul_mem ((gammaAct D.subtype).inv_mem hP) hy) hP

theorem three_eq_zero_of_card_nine [Finite K] (hK : Nat.card K = 9) : (3 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 9 := by rw [Fintype.card_eq_nat_card]; exact hK
  obtain ⟨n, hp, hq⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 9 := by
    rw [← hK', hq]
    exact dvd_pow_self _ (by exact n.pos.ne')
  have h3 : ringChar K ∣ 3 ^ 2 := by simpa using hdvd
  have : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
  have h := CharP.cast_eq_zero K (ringChar K)
  rw [this] at h
  simpa using h

section Word

variable (ι : K) (hι : ι * ι = -1) (h3 : (3 : K) = 0)
include hι h3

@[expose] def X1 : SL(3, K) := ⟨!![ι, ι, 0; ι, -ι, 0; 0, 0, -1], by
  simp [Matrix.det_fin_three]
  linear_combination 2 * hι - h3⟩

@[expose] def X2 : SL(3, K) := ⟨!![-ι, ι, 0; -ι, -ι, 0; 0, 0, 1], by
  simp [Matrix.det_fin_three]
  linear_combination 2 * hι - h3⟩

@[expose] def T1 : SL(3, K) := ⟨!![ι, 0, 0; 0, 1 + ι, 0; 0, 0, 1 + ι], by
  simp [Matrix.det_fin_three]
  linear_combination (ι + 2) * hι - h3⟩

@[expose] def T2 : SL(3, K) := ⟨!![ι, 0, 0; 0, 1 - ι, 0; 0, 0, ι - 1], by
  simp [Matrix.det_fin_three]
  linear_combination (2 - ι) * hι - h3⟩

theorem X1_orth : (X1 ι hι h3).transpose * X1 ι hι h3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose]
  show (!![ι, ι, 0; ι, -ι, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![ι, ι, 0; ι, -ι, 0; 0, 0, -1] = 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linear_combination 2 * hι - h3

theorem X2_orth : (X2 ι hι h3).transpose * X2 ι hι h3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose]
  show (!![-ι, ι, 0; -ι, -ι, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![-ι, ι, 0; -ι, -ι, 0; 0, 0, 1] = 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  all_goals linear_combination 2 * hι - h3

omit hι h3 in
@[expose] def Wsw : SL(3, K) := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

omit hι h3 in
theorem Wsw_orth : (Wsw (K := K)).transpose * Wsw = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose]
  show (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K)ᵀ * !![0, 1, 0; 1, 0, 0; 0, 0, -1] = 1
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem word_eq : X1 ι hι h3 * T1 ι hι h3 * X1 ι hι h3 * T2 ι hι h3 * X2 ι hι h3 =
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) ι := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection]
  show (!![ι, ι, 0; ι, -ι, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) * !![ι, 0, 0; 0, 1 + ι, 0; 0, 0, 1 + ι] *
      !![ι, ι, 0; ι, -ι, 0; 0, 0, -1] * !![ι, 0, 0; 0, 1 - ι, 0; 0, 0, ι - 1] *
      !![-ι, ι, 0; -ι, -ι, 0; 0, 0, 1] = _
  rw [word_identity ι hι h3]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.add_apply]

end Word

@[expose] def Dsl (a : Kˣ) : SL(3, K) := ⟨!![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)], by
  simp [Matrix.det_fin_three]⟩

theorem Dsl_mul_transvection (a : Kˣ) (t : K) :
    Dsl a * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) ((a : K) * t) * Dsl a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection]
  show (!![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] : Matrix (Fin 3) (Fin 3) K) * _ = _ *
    (!![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply]

theorem Wsw_mul_transvection (t : K) :
    Wsw * Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) t * Wsw := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection]
  show (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K) * _ = _ *
    (!![0, 1, 0; 1, 0, 0; 0, 0, -1] : Matrix (Fin 3) (Fin 3) K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply]

theorem e2_rt01 [Finite K] (hK : Nat.card K = 9)
    (D : Subgroup (MulAut (LinearFlag.projectiveSL 3 K))) (hfs : D ≤ frameStab 3 K) (hA : IsRank23 ↥D)
    (h8 : Nat.card ↥D = 8) (hshape : ShapeE2 D) (c : K) :
    rt 0 1 (by decide) c ∈ gammaAct D.subtype := by
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hF := hshape.1
  obtain ⟨ι, hι'⟩ := isSquare_neg_one_nine hK
  have hι : ι * ι = -1 := hι'.symm
  have h3 := three_eq_zero_of_card_nine hK
  have hι0 : ι ≠ 0 := by
    rintro rfl
    simp at hι
  have m1 : LinearFlag.proj 3 K (X1 ι hι h3) ∈ gammaAct D.subtype :=
    orth_mem hK D hfs hA h8 hshape _ (X1_orth ι hι h3) (by simp [X1]) (by simp [X1]) (by simp [X1]) (by simp [X1])
  have m2 : LinearFlag.proj 3 K (X2 ι hι h3) ∈ gammaAct D.subtype :=
    orth_mem hK D hfs hA h8 hshape _ (X2_orth ι hι h3) (by simp [X2]) (by simp [X2]) (by simp [X2]) (by simp [X2])
  have t1 : LinearFlag.proj 3 K (T1 ι hι h3) ∈ gammaAct D.subtype :=
    torus_mem D hfs hA hF _ (by
      show (!![ι, 0, 0; 0, 1 + ι, 0; 0, 0, 1 + ι] : Matrix (Fin 3) (Fin 3) K).IsDiag
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  have t2 : LinearFlag.proj 3 K (T2 ι hι h3) ∈ gammaAct D.subtype :=
    torus_mem D hfs hA hF _ (by
      show (!![ι, 0, 0; 0, 1 - ι, 0; 0, 0, ι - 1] : Matrix (Fin 3) (Fin 3) K).IsDiag
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
  have hword : rt 0 1 (by decide) ι ∈ gammaAct D.subtype := by
    have := (gammaAct D.subtype).mul_mem ((gammaAct D.subtype).mul_mem ((gammaAct D.subtype).mul_mem
      ((gammaAct D.subtype).mul_mem m1 t1) m1) t2) m2
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, word_eq ι hι h3] at this
    exact this
  by_cases hc : c = 0
  · subst hc
    have : rt (0 : Fin 3) 1 (by decide) (0 : K) = 1 := by
      unfold rt
      rw [show Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (0 : K) = 1 from by
        apply Subtype.ext
        rw [CFSG.LinearGroups.coe_transvection]
        simp, map_one]
    rw [this]
    exact (gammaAct D.subtype).one_mem
  · let a : Kˣ := Units.mk0 (c / ι) (div_ne_zero hc hι0)
    have hD : LinearFlag.proj 3 K (Dsl a) ∈ gammaAct D.subtype :=
      torus_mem D hfs hA hF _ (by
        show (!![(a : K), 0, 0; 0, 1, 0; 0, 0, ((a⁻¹ : Kˣ) : K)] : Matrix (Fin 3) (Fin 3) K).IsDiag
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all)
    have key := Dsl_mul_transvection a ι
    have hac : (a : K) * ι = c := by
      show c / ι * ι = c
      field_simp
    rw [hac] at key
    have : rt (0 : Fin 3) 1 (by decide) c = LinearFlag.proj 3 K (Dsl a) * rt 0 1 (by decide) ι *
        (LinearFlag.proj 3 K (Dsl a))⁻¹ := by
      unfold rt
      rw [← map_inv, ← map_mul, ← map_mul, key, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact (gammaAct D.subtype).mul_mem ((gammaAct D.subtype).mul_mem hD hword) ((gammaAct D.subtype).inv_mem hD)

theorem phiM2_mem_of_fullPair {H : Subgroup (LinearFlag.projectiveSL 3 K)}
    (hF : FullPair H 0 1 (by decide)) (g : SL(2, K)) : phiM 2 g ∈ H := by
  have hg : g ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 2 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := 2)]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction (p := fun g _ => phiM 2 g ∈ H) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨i, j, hij, c, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · have := hF.1 c
      show GenLocL3Blk.phi 0 _ ∈ H
      unfold GenLocL3Blk.phi
      rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection]
      exact this
    · have := hF.2 c
      show GenLocL3Blk.phi 0 _ ∈ H
      unfold GenLocL3Blk.phi
      rw [MonoidHom.comp_apply, GenLocL3Blk.blkHom_transvection]
      exact this
    · exact absurd rfl hij
  · rw [map_one]; exact H.one_mem
  · intro a b _ _ ha hb
    rw [map_mul]; exact H.mul_mem ha hb
  · intro a _ ha
    rw [map_inv]; exact H.inv_mem ha

theorem excE2 [Finite K] (hK : Nat.card K = 9) : ExcE2 K := by
  intro D hfs hA h8 hshape
  have hfin : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hα : D.subtype.range ≤ frameStab 3 K := by rwa [Subgroup.range_subtype]
  have hfp : FullPair (gammaAct D.subtype) 0 1 (by decide) := by
    refine ⟨e2_rt01 hK D hfs hA h8 hshape, fun c => ?_⟩
    have hW : LinearFlag.proj 3 K (Wsw (K := K)) ∈ gammaAct D.subtype :=
      orth_mem hK D hfs hA h8 hshape _ Wsw_orth (by simp [Wsw]) (by simp [Wsw]) (by simp [Wsw]) (by simp [Wsw])
    have key := Wsw_mul_transvection (K := K) c
    have : rt (1 : Fin 3) 0 (by decide) c = LinearFlag.proj 3 K (Wsw (K := K)) * rt 0 1 (by decide) c *
        (LinearFlag.proj 3 K (Wsw (K := K)))⁻¹ := by
      unfold rt
      rw [← map_inv, ← map_mul, ← map_mul, key, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]
    exact (gammaAct D.subtype).mul_mem ((gammaAct D.subtype).mul_mem hW (e2_rt01 hK D hfs hA h8 hshape c))
      ((gammaAct D.subtype).inv_mem hW)
  have hfull : ∀ g, phiM 2 g ∈ gammaAct D.subtype := phiM2_mem_of_fullPair hfp
  obtain ⟨hF, hK3, r, v, hrv, hsqv⟩ := hshape
  obtain ⟨τ, w, hτ1, hτw, hτm⟩ := hK3 0
  have hsq1 : IsSquare ((v 1 : K) * v 2) := by simpa [crd] using hsqv 0
  obtain ⟨s, hs⟩ := hsq1
  have hv1 : ((v 1 : Kˣ) : K) ≠ 0 := (v 1).ne_zero
  have hv2 : ((v 2 : Kˣ) : K) ≠ 0 := (v 2).ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hβ : s / (v 2 : K) ≠ 0 := div_ne_zero hs0 hv2
  have hrel : (s / (v 2 : K)) * (s / (v 2 : K)) * (v (crd 0 1) : K) = (v (crd 0 0) : K) := by
    simp only [crd]
    simp
    field_simp
    linear_combination -hs
  have fixR := fixed_anti_of_reflection 0 (hfs r.2) hrv hβ hrel
  have fixτ : (τ : MulAut (LinearFlag.projectiveSL 3 K)) (phiM 0 (anti hβ)) = phiM 0 (anti hβ) := by
    rw [restM_spec 0 ⟨τ, hfs τ.2⟩ (anti hβ), rho_eq_one_of_eq 0 (hfs τ.2) hτw hτm]
    rfl
  have hr1 : r ≠ 1 := by
    intro h
    apply reflection_not_mem_noDual hrv
    rw [h]
    exact (noDual K).one_mem
  have hτr : τ ≠ r := by
    intro h
    apply reflection_not_mem_noDual hrv
    rw [← h, hτw]
    exact ⟨diag3 w, 1, isDiag_diag3 w, by rw [map_one, mul_one]⟩
  have hE := adm_closure_pair hA.1 h8 τ r hτ1 hr1 hτr
  have hfix : ∀ e ∈ Subgroup.closure ({τ, r} : Set ↥D),
      (D.subtype e) (phiM 0 (anti hβ)) = phiM 0 (anti hβ) := by
    intro e he
    refine Subgroup.closure_induction
      (p := fun e _ => (D.subtype e) (phiM 0 (anti hβ)) = phiM 0 (anti hβ)) ?_ ?_ ?_ ?_ he
    · rintro y (rfl | rfl)
      · exact fixτ
      · exact fixR
    · simp
    · intro a b _ _ ha hb
      rw [map_mul, MulAut.mul_apply, hb, ha]
    · intro a _ ha
      rw [map_inv]
      calc ((D.subtype a)⁻¹) (phiM 0 (anti hβ)) = ((D.subtype a)⁻¹) ((D.subtype a) (phiM 0 (anti hβ))) := by
            rw [ha]
        _ = phiM 0 (anti hβ) := by simp
  have hw : phiM 0 (anti hβ) ∈ gammaAct D.subtype :=
    le_gammaAct D.subtype hE ((GenLocBasic.mem_fixedIn_map _ _ _).2 hfix)
  exact top_of_full_mono (a := 2) (b := 0) (by decide) hfull hβ hw

end GenLocL3NineE2

end CFSG.GH74.Generic.BProg.B2
