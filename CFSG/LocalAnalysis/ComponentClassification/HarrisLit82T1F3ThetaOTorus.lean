module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaPSU
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL)

variable {K : Type} [Field K]

theorem add_smul_pow_card [Fintype K] {A : Type*} [Ring A] [Algebra K A] {ℓ e : ℕ}
    [Fact ℓ.Prime] [CharP A ℓ] (hKc : Fintype.card K = ℓ ^ e) {N : A} {l : K}
    (hN : N * N = l • 1) {m : ℕ} (hm : Fintype.card K = 2 * m + 1) (a b : K) :
    (a • (1 : A) + b • N) ^ Fintype.card K = a • 1 + (b * l ^ m) • N := by
  have hc : Commute (a • (1 : A)) (b • N) := ((Commute.one_left N).smul_left a).smul_right b
  rw [hKc, add_pow_char_pow_of_commute ℓ e hc, ← hKc, smul_pow, smul_pow, one_pow,
    FiniteField.pow_card, FiniteField.pow_card]
  congr 1
  rw [hm, pow_succ, pow_mul, sq, hN, smul_pow, one_pow, smul_mul_assoc, one_mul, smul_smul]

theorem pow_card_sq_sub_one_of_sq [Finite K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2)
    {N : Matrix ι ι K} {l : K} (hl : l ≠ 0) (hN : N * N = l • 1) {D : GL ι K} {a b : K}
    (hD : (D : Matrix ι ι K) = a • 1 + b • N) : D ^ (Nat.card K ^ 2 - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hKc ⊢
  obtain ⟨m, hm⟩ : Odd (Fintype.card K) := by
    rw [hKc]
    exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2 |>.pow
  have hl2 : l ^ m * l ^ m = 1 := by
    rw [← pow_add, ← two_mul, show 2 * m = Fintype.card K - 1 by omega]
    exact FiniteField.pow_card_sub_one_eq_one l hl
  have hsq : D ^ (Fintype.card K ^ 2) = D := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, pow_mul, hD, add_smul_pow_card hKc hN hm,
      add_smul_pow_card hKc hN hm, mul_assoc, hl2, mul_one]
  have hpos : 1 ≤ Fintype.card K ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
  have : D ^ (Fintype.card K ^ 2 - 1) * D = 1 * D := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, one_mul, hsq]
  exact mul_right_cancel this

theorem isometry_two_pow_card_sq_sub_one [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) {m : ℕ} (hm : m = 2) {v : Fin m → K}
    (hv : ∀ i, v i ≠ 0) {g : GL (Fin m) K}
    (hg : g ∈ CatalogueBGraphForm.isometryGroup m K (diagGL hv)) :
    g ^ (Nat.card K ^ 2 - 1) = 1 := by
  subst hm
  have hg' := (CatalogueBGraphForm.mem_isometryGroup _ _ _ _).1 hg
  rw [coe_diagGL] at hg'
  set M := (g : Matrix (Fin 2) (Fin 2) K) with hM
  set δ := M.det with hδ
  have hdD : (diagonal v).det ≠ 0 := by
    rw [det_diagonal, Fin.prod_univ_two]
    exact mul_ne_zero (hv 0) (hv 1)
  have hδ2 : δ * δ = 1 := by
    have e1 := congrArg Matrix.det hg'
    rw [det_mul, det_mul, det_transpose] at e1
    have : (δ * δ - 1) * (diagonal v).det = 0 := by linear_combination e1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hdD)
  have hadj : δ • (Mᵀ * diagonal v) = diagonal v * adjugate M := by
    have e1 := congrArg (· * adjugate M) hg'
    rw [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at e1
    exact e1
  have e00 := congrFun (congrFun hadj 0) 0
  have e01 := congrFun (congrFun hadj 0) 1
  simp [adjugate_fin_two, Matrix.mul_apply, diagonal_apply] at e00 e01
  have hdet : δ = M 0 0 * M 1 1 - M 0 1 * M 1 0 := det_fin_two M
  have hv0 := hv 0
  have hv1 := hv 1
  rcases mul_self_eq_one_iff.1 hδ2 with h1 | h1
  ·
    rw [h1, one_mul] at e00 e01
    set N : Matrix (Fin 2) (Fin 2) K := !![0, 1; -(v 0 / v 1), 0] with hN
    have hNN : N * N = (-(v 0 / v 1)) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hN, Matrix.mul_apply, Fin.sum_univ_two]
    have hMN : M = M 0 0 • 1 + M 0 1 • N := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [hN]
      · simp [hN]
      · simp [hN]
        field_simp
        linear_combination e01
      · simp [hN]
        field_simp at e00
        linear_combination -e00
    exact pow_card_sq_sub_one_of_sq hKc hℓ2 (neg_ne_zero.2 (div_ne_zero hv0 hv1)) hNN hMN
  ·
    rw [h1] at e00 hdet
    field_simp at e00
    have hM2 : M * M = 1 := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination hdet - M 0 0 * e00
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (-M 0 1) * e00
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination (-M 1 0) * e00
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
        linear_combination hdet - M 1 1 * e00
    have hg2 : g ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
      exact hM2
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨k, hk⟩ : Odd (Nat.card K) := by
      rw [hKc]
      exact (Fact.out : ℓ.Prime).odd_of_ne_two hℓ2 |>.pow
    rw [show Nat.card K ^ 2 - 1 = 2 * (2 * k * k + 2 * k) from
      Nat.sub_eq_of_eq_add (by rw [hk]; ring), pow_mul, hg2, one_pow]

theorem oIsoBlock_pow_card_sq_sub_one [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hJ : J.card = 2) {R : GL (Fin d) K} (hR : R ∈ oIsoBlock K hw J) :
    R ^ (Nat.card K ^ 2 - 1) = 1 := by
  set g := (oIsoBlockEquiv hw J).symm ⟨R, hR⟩ with hg
  have h1 : g ^ (Nat.card K ^ 2 - 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact isometry_two_pow_card_sq_sub_one hKc hℓ2 hJ (wRes_ne_zero hw J) g.2
  have h2 : (⟨R, hR⟩ : oIsoBlock K hw J) ^ (Nat.card K ^ 2 - 1) = 1 := by
    rw [← (oIsoBlockEquiv hw J).apply_symm_apply ⟨R, hR⟩, ← map_pow, ← hg, h1, map_one]
  have h3 := congrArg Subtype.val h2
  rwa [Subgroup.coe_pow] at h3

theorem similarityPairs_pow_eq_one {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {g : similarityPairs Q} (hg : g.val.right = 1) {k : ℕ} (hk : g.val.left ^ k = 1) :
    g ^ k = 1 := by
  have key : ∀ m : ℕ, (g ^ m).val.left = g.val.left ^ m ∧ (g ^ m).val.right = 1 := by
    intro m
    induction m with
    | zero => exact ⟨rfl, rfl⟩
    | succ m ih =>
      rw [pow_succ]
      change ((g ^ m).val * g.val).left = _ ∧ ((g ^ m).val * g.val).right = 1
      rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, ih.2, hg, map_one,
        MulAut.one_apply, ih.1, pow_succ, one_mul]
      exact ⟨rfl, rfl⟩
  apply Subtype.ext
  apply SemidirectProduct.ext
  · rw [(key k).1, hk]
    rfl
  · rw [(key k).2]
    rfl

theorem oκ_pow_card_sq_sub_one_of_sq [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) {d : ℕ} [Nonempty (Fin d)]
    {Q : QuadraticForm K (Fin d → K)} {g : similarityPairs Q} (hg : g.val.right = 1)
    {N : Matrix (Fin d) (Fin d) K} {l : K} (hl : l ≠ 0) (hN : N * N = l • 1) {a b : K}
    (hD : (g.val.left : Matrix (Fin d) (Fin d) K) = a • 1 + b • N) :
    oκ Q g ^ (Nat.card K ^ 2 - 1) = 1 := by
  rw [← map_pow, similarityPairs_pow_eq_one hg (pow_card_sq_sub_one_of_sq hKc hℓ2 hl hN hD),
    map_one]

theorem oκ_linPair_pow_card_sq_sub_one [Finite K] {ℓ e : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hKc : Nat.card K = ℓ ^ e) (hℓ2 : ℓ ≠ 2) {d : ℕ} {w : Fin d → K} (hw : ∀ i, w i ≠ 0)
    {J : Finset (Fin d)} (hJ : J.card = 2) {R : GL (Fin d) K}
    (hR : R ∈ matrixIsometries (oQ (diagGL hw))) (hRJ : R ∈ oIsoBlock K hw J) :
    oκ _ (linPair R hR) ^ (Nat.card K ^ 2 - 1) = 1 := by
  rw [← map_pow, similarityPairs_pow_eq_one (linPair_right R hR)
    (by rw [linPair_left]; exact oIsoBlock_pow_card_sq_sub_one hKc hℓ2 hw hJ hRJ), map_one]

end CFSG.ComponentClassification.Burgoyne.O
