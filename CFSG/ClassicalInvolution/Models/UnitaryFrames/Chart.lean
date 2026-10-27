module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Chart
public import CFSG.ClassicalInvolution.Models.UnitaryPairs.RootSU2

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.Generic CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Basic

variable (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ)

@[expose] noncomputable def suMatHom : Su K p f n →* Matrix (Fin n) (Fin n) K where
  toFun := suMat
  map_one' := suMat_one
  map_mul' := suMat_mul

variable {K p f n}

@[simp] theorem suMatHom_apply (x : Su K p f n) : suMatHom K p f n x = suMat x := rfl

theorem suMatHom_injective : Function.Injective (suMatHom K p f n) := suMat_injective

variable (K p f n) in
@[expose] noncomputable def signGroupU : Subgroup (Su K p f n) :=
  signSubgroup (suMatHom K p f n)

theorem mem_signGroupU {x : Su K p f n} : x ∈ signGroupU K p f n ↔ IsSignDiag (suMat x) :=
  Iff.rfl

theorem signGroupU_sq {x : Su K p f n} (hx : x ∈ signGroupU K p f n) : x * x = 1 :=
  signSubgroup_sq suMatHom_injective hx

theorem signGroupU_comm {x y : Su K p f n} (hx : x ∈ signGroupU K p f n)
    (hy : y ∈ signGroupU K p f n) : x * y = y * x :=
  signSubgroup_comm suMatHom_injective hx hy

variable (K p f) in
@[expose] noncomputable def mkSU {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (hdet : M.det = 1)
    (hM : conjTr (unitaryInvolution K p f) M * M = 1) : Su K p f n :=
  ⟨Matrix.SpecialLinearGroup.toGL ⟨M, hdet⟩, hdet, hM⟩

theorem suMat_mkSU {M : Matrix (Fin n) (Fin n) K} (hdet : M.det = 1)
    (hM : conjTr (unitaryInvolution K p f) M * M = 1) : suMat (mkSU K p f M hdet hM) = M := rfl

variable (K p f) in
@[expose] noncomputable def zEltU (T : Pair n) : Su K p f n :=
  mkSU K p f (zMat K n T.1) (by rw [det_zMat, T.2]; norm_num)
    (by rw [conjTr_zMat, zMat_mul_self])

theorem suMat_zEltU (T : Pair n) : suMat (zEltU K p f T) = zMat K n T.1 := rfl

theorem zEltU_mem_signGroupU (T : Pair n) : zEltU K p f T ∈ signGroupU K p f n :=
  isSignDiag_zMat T.1

theorem zEltU_mul_self (T : Pair n) : zEltU K p f T * zEltU K p f T = 1 :=
  suMat_injective (by rw [suMat_mul, suMat_zEltU, zMat_mul_self, suMat_one])

variable (K p f) in
@[expose] noncomputable def LcU (T : Pair n) : Subgroup (Su K p f n) :=
  longRootGroupSU K p f (zMat K n T.1)

end Basic

section Monomial

variable {K : Type} [Field K] {n : ℕ}

theorem conjTr_monoMat_mul_self (σ : K ≃+* K) (τ : Equiv.Perm (Fin n)) :
    conjTr σ (monoMat K τ) * monoMat K τ = 1 := by
  have hs : permSign K τ * permSign K τ = 1 := permSign_mul_self τ
  have hσs : σ (permSign K τ) = permSign K τ := by
    rcases permSign_cases (K := K) τ with h | h <;> simp [h]
  set d : Fin n → K := fun a => if a.val = 0 then permSign K τ else 1 with hd
  have hdd : ∀ a, d a * d a = 1 := fun a => by
    by_cases ha : a.val = 0 <;> simp [hd, ha, hs]
  have hσd : ∀ a, σ (d a) = d a := fun a => by
    by_cases ha : a.val = 0 <;> simp [hd, ha, hσs]
  have hP : conjTr σ (Matrix.permMatrixHom (R := K) τ) = (Matrix.permMatrixHom (R := K) τ)ᵀ := by
    ext i j
    simp [conjTr, Matrix.permMatrixHom_apply, PEquiv.toMatrix_apply, apply_ite σ]
  have hPP : (Matrix.permMatrixHom (R := K) τ)ᵀ * Matrix.permMatrixHom (R := K) τ = 1 := by
    rw [Matrix.permMatrixHom_apply, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one]
  have hD : conjTr σ (Matrix.diagonal d) = Matrix.diagonal d := by
    rw [conjTr_diagonal]
    congr 1
    funext a
    exact hσd a
  have hDD : Matrix.diagonal d * Matrix.diagonal d = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hdd a
  rw [monoMat, conjTr_mul, hD, hP]
  calc Matrix.diagonal d * (Matrix.permMatrixHom (R := K) τ)ᵀ *
        (Matrix.permMatrixHom (R := K) τ * Matrix.diagonal d)
      = Matrix.diagonal d * ((Matrix.permMatrixHom (R := K) τ)ᵀ *
          Matrix.permMatrixHom (R := K) τ) * Matrix.diagonal d := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hPP, Matrix.mul_one, hDD]

end Monomial

section LongRoot

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

variable (K p f) in
@[expose] noncomputable def monoSU (hn : 0 < n) (τ : Equiv.Perm (Fin n)) : Su K p f n :=
  mkSU K p f (monoMat K τ) (det_monoMat hn τ) (conjTr_monoMat_mul_self _ τ)

theorem suMat_monoSU (hn : 0 < n) (τ : Equiv.Perm (Fin n)) :
    suMat (monoSU K p f hn τ) = monoMat K τ := rfl

theorem exists_suMonomial_pair (hn : 2 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ∃ (g : Su K p f n) (τ : Equiv.Perm (Fin n)), IsMonomialFor (suMat g) τ ∧
      τ ⟨0, by omega⟩ = i ∧ τ ⟨1, by omega⟩ = j := by
  obtain ⟨τ, h0, h1⟩ := exists_perm_pair hn hij
  exact ⟨monoSU K p f (by omega) τ, τ, isMonomialFor_monoMat τ, h0, h1⟩

theorem exists_suMonomial_of_pair (hn : 2 ≤ n) (T : Pair n) :
    ∃ (g : Su K p f n) (τ : Equiv.Perm (Fin n)), IsMonomialFor (suMat g) τ ∧
      T.1 = {τ ⟨0, by omega⟩, τ ⟨0 + 1, by omega⟩} := by
  obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp T.2
  obtain ⟨g, τ, hg, h0, h1⟩ := exists_suMonomial_pair (K := K) (p := p) (f := f) hn hij
  refine ⟨g, τ, hg, ?_⟩
  rw [hT, ← h0]
  congr 2
  exact h1.symm

theorem suMonomial_conj_negBlock {g : Su K p f n} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (suMat g) τ) {j : ℕ} (hj : j + 2 ≤ n) :
    suMat g * negBlock K n j * suMat g⁻¹ = zMat K n {τ ⟨j, by omega⟩, τ ⟨j + 1, by omega⟩} := by
  rw [negBlock_eq_zMat hj, hg.mul_zMat_mul_inv (suMat_mul_suMat_inv g)]
  simp [Finset.map_insert]

theorem LcU_eq_map_conj (h2 : (2 : K) ≠ 0) {g : Su K p f n} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (suMat g) τ) {j : ℕ} (hj : j + 2 ≤ n) {T : Pair n}
    (hT : T.1 = {τ ⟨j, by omega⟩, τ ⟨j + 1, by omega⟩}) :
    LcU K p f T = (blockEmb K p f n 2 j hj).range.map (MulAut.conj g).toMonoidHom := by
  rw [range_blockEmb_eq_longRootGroupSU h2 hj, ← longRootGroupSU_conj,
    suMonomial_conj_negBlock hg hj, ← hT]
  rfl

theorem isLongRootSU2_LcU (h2 : (2 : K) ≠ 0) (hn : 2 ≤ n) (T : Pair n) :
    IsLongRootSU2 K p f hn (LcU K p f T) (zEltU K p f T) := by
  obtain ⟨g, τ, hg, hT⟩ := exists_suMonomial_of_pair (K := K) (p := p) (f := f) hn T
  refine ⟨g, LcU_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT, ?_⟩
  apply suMat_injective
  rw [suMat_mul, suMat_mul, suMat_rootInvSU, suMonomial_conj_negBlock hg (by omega : 0 + 2 ≤ n),
    suMat_zEltU, hT]

end LongRoot

section Entries

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

noncomputable abbrev entU (e : Su K p f n) (a : Fin n) : K := entOf (suMatHom K p f n) e a

theorem entU_cases {e : Su K p f n} (he : e ∈ signGroupU K p f n) (a : Fin n) :
    entU e a = 1 ∨ entU e a = -1 :=
  entOf_cases he a

theorem entU_mul_self {e : Su K p f n} (he : e ∈ signGroupU K p f n) (a : Fin n) :
    entU e a * entU e a = 1 :=
  entOf_mul_self he a

theorem suMat_eq_diagonal {e : Su K p f n} (he : e ∈ signGroupU K p f n) :
    suMat e = Matrix.diagonal (entU e) :=
  mat_eq_diagonal he

theorem entU_mul {e e' : Su K p f n} (he : e ∈ signGroupU K p f n)
    (he' : e' ∈ signGroupU K p f n) (a : Fin n) : entU (e * e') a = entU e a * entU e' a :=
  entOf_mul he he' a

theorem entU_ne_neg (h2 : (2 : K) ≠ 0) {e : Su K p f n} (he : e ∈ signGroupU K p f n)
    (a : Fin n) : entU e a ≠ -entU e a :=
  entOf_ne_neg h2 he a

theorem inv_eq_self_of_mem_signGroupU {e : Su K p f n} (he : e ∈ signGroupU K p f n) : e⁻¹ = e :=
  inv_eq_self_of_mem_signSubgroup suMatHom_injective he

theorem conj_mem_signGroupU {g : Su K p f n} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (suMat g) τ) {e : Su K p f n} (he : e ∈ signGroupU K p f n) :
    g⁻¹ * e * g ∈ signGroupU K p f n ∧ ∀ a, entU (g⁻¹ * e * g) a = entU e (τ a) :=
  conj_mem_signSubgroup (mat := suMatHom K p f n) hg he

theorem zEltU_entU (T : Pair n) (a : Fin n) :
    entU (zEltU K p f T) a = if a ∈ T.1 then -1 else 1 :=
  zMat_apply_self T.1 a

theorem suMat_conj_blockEmb (hn : 2 ≤ n) {e : Su K p f n} (he : e ∈ signGroupU K p f n)
    (A : Su K p f 2) :
    suMat (e * blockEmb K p f n 2 0 (by omega) A * e⁻¹) =
      blockMat n 0 (Matrix.diagonal ![entU e ⟨0, by omega⟩, entU e ⟨1, by omega⟩] * suMat A *
        Matrix.diagonal ![entU e ⟨0, by omega⟩, entU e ⟨1, by omega⟩]) := by
  rw [inv_eq_self_of_mem_signGroupU he, suMat_mul, suMat_mul, suMat_blockEmb,
    suMat_eq_diagonal he]
  exact diagonal_conj_blockMat_two hn (entU_mul_self he) _

end Entries

section Psi

variable {K : Type} [Field K]

@[expose] def wittMat (μ : K) : Matrix (Fin 2) (Fin 2) K := !![1, 2⁻¹; μ, -μ / 2]

@[expose] def wittMatInv (μ : K) : Matrix (Fin 2) (Fin 2) K := !![2⁻¹, (2 * μ)⁻¹; 1, -μ⁻¹]

theorem wittMat_mul_inv (h2 : (2 : K) ≠ 0) {μ : K} (hμ0 : μ ≠ 0) :
    wittMat μ * wittMatInv μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittMat, wittMatInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem wittMatInv_mul (h2 : (2 : K) ≠ 0) {μ : K} (hμ0 : μ ≠ 0) :
    wittMatInv μ * wittMat μ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wittMat, wittMatInv, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

@[expose] def wittGL (h2 : (2 : K) ≠ 0) {μ : K} (hμ0 : μ ≠ 0) : GL (Fin 2) K :=
  ⟨wittMat μ, wittMatInv μ, wittMat_mul_inv h2 hμ0, wittMatInv_mul h2 hμ0⟩

theorem ne_zero_of_norm_neg_one (σ : K ≃+* K) {μ : K} (hμ : σ μ * μ = -1) : μ ≠ 0 := by
  rintro rfl
  rw [mul_zero] at hμ
  exact one_ne_zero (by linear_combination hμ)

theorem conjTr_wittMat_mul (σ : K ≃+* K) {μ : K} (hμ : σ μ * μ = -1) (h2 : (2 : K) ≠ 0) :
    conjTr σ (wittMat μ) * wittMat μ = antidiag 2 := by
  have hσ2 : σ (2 : K) = 2 := map_ofNat σ 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, conjTr, wittMat, Matrix.mul_apply, Fin.sum_univ_two, hσ2, map_div₀] <;>
    field_simp <;> first | linear_combination hμ | linear_combination (-1 : K) * hμ

end Psi

section Psi2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {ζ μ : K}

@[expose] noncomputable def psiEquiv (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ)
    (h2 : (2 : K) ≠ 0) (hμ : unitaryInvolution K p f μ * μ = -1) :
    SL(2, fixedSubfield K p f) ≃* Su K p f 2 :=
  (hypEquiv hζ0 hζ).trans (conjEquiv (wittGL h2 (ne_zero_of_norm_neg_one _ hμ))
    (conjTr_wittMat_mul _ hμ h2))

theorem suMat_psiEquiv (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ) (h2 : (2 : K) ≠ 0)
    (hμ : unitaryInvolution K p f μ * μ = -1) (A : SL(2, fixedSubfield K p f)) :
    suMat (psiEquiv hζ0 hζ h2 hμ A) =
      wittMat μ * hypMat ζ (A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)) * wittMatInv μ :=
  rfl

theorem mem_fixedSubfield_t (hζ : unitaryInvolution K p f ζ = -ζ) :
    (ζ ^ 2)⁻¹ / 4 ∈ fixedSubfield K p f := by
  rw [mem_fixedSubfield]
  have h4 : unitaryInvolution K p f (4 : K) = 4 := map_ofNat _ 4
  simp [map_div₀, map_inv₀, map_pow, hζ, h4]

@[expose] noncomputable def tF (hζ : unitaryInvolution K p f ζ = -ζ) : fixedSubfield K p f :=
  ⟨(ζ ^ 2)⁻¹ / 4, mem_fixedSubfield_t hζ⟩

theorem coe_tF (hζ : unitaryInvolution K p f ζ = -ζ) : ((tF hζ : fixedSubfield K p f) : K) =
    (ζ ^ 2)⁻¹ / 4 := rfl

theorem tF_ne_zero (hζ0 : ζ ≠ 0) (h2 : (2 : K) ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ) :
    tF hζ ≠ 0 := by
  intro h
  have h' : (ζ ^ 2)⁻¹ / 4 = 0 := congrArg (fun x : fixedSubfield K p f => (x : K)) h
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  exact (div_ne_zero (inv_ne_zero (pow_ne_zero 2 hζ0)) h4) h'

@[expose] def swapConj {F : Type*} [Field F] (t : F) (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![A 1 1, t * A 1 0; t⁻¹ * A 0 1, A 0 0]

theorem swap_mul_mul {F : Type*} [Field F] {t : F} (ht : t ≠ 0) (A : Matrix (Fin 2) (Fin 2) F) :
    !![0, t; 1, 0] * A * !![0, 1; t⁻¹, 0] = swapConj t A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapConj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    (try field_simp)

theorem psi_conj_diag (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ) (h2 : (2 : K) ≠ 0)
    (hμ : unitaryInvolution K p f μ * μ = -1)
    (A : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)) :
    Matrix.diagonal ![(1 : K), -1] * (wittMat μ * hypMat ζ A * wittMatInv μ) *
        Matrix.diagonal ![(1 : K), -1] =
      wittMat μ * hypMat ζ (swapConj (tF hζ) A) * wittMatInv μ := by
  have hμ0 := ne_zero_of_norm_neg_one _ hμ
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have ht0 : ((tF hζ : fixedSubfield K p f) : K) ≠ 0 := by
    rw [coe_tF]
    exact div_ne_zero (inv_ne_zero (pow_ne_zero 2 hζ0)) h4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, swapConj, wittMat, wittMatInv, Matrix.mul_apply, Fin.sum_univ_two, coe_tF,
      Matrix.diagonal_apply] <;> field_simp <;> ring

end Psi2

section ChartU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
  {ζ μ : K}

@[expose] noncomputable def chartU (hn : 2 ≤ n) (g : Su K p f n)
    (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2) : SL(2, fixedSubfield K p f) →* Su K p f n :=
  ((MulAut.conj g).toMonoidHom.comp (blockEmb K p f n 2 0 (by omega))).comp ψ.toMonoidHom

theorem chartU_apply (hn : 2 ≤ n) (g : Su K p f n) (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2)
    (s : SL(2, fixedSubfield K p f)) :
    chartU hn g ψ s = g * blockEmb K p f n 2 0 (by omega) (ψ s) * g⁻¹ := rfl

theorem chartU_injective (hn : 2 ≤ n) (g : Su K p f n)
    (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2) : Function.Injective (chartU hn g ψ) :=
  ((MulAut.conj g).injective.comp (blockEmb_injective (by omega))).comp ψ.injective

theorem range_chartU (hn : 2 ≤ n) (g : Su K p f n)
    (ψ : SL(2, fixedSubfield K p f) ≃* Su K p f 2) :
    (chartU hn g ψ).range = (rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom := by
  have h1 : ψ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr ψ.surjective
  rw [chartU, MonoidHom.range_comp, h1, ← MonoidHom.range_eq_map, MonoidHom.range_comp]
  rfl

omit [Finite K] in
theorem eq_neg_of_ne_of_sign {x y : K} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) (hne : x ≠ y) :
    y = -x := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · simp
  · exact absurd rfl hne

omit [Finite K] in
theorem diagonal_two_neg_conj (a : K) (ha : a * a = 1) (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal ![a, -a] * M * Matrix.diagonal ![a, -a] =
      Matrix.diagonal ![(1 : K), -1] * M * Matrix.diagonal ![(1 : K), -1] := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination (M _ _) * ha

@[expose] noncomputable def gSwapGL (hζ0 : ζ ≠ 0) (h2 : (2 : K) ≠ 0)
    (hζ : unitaryInvolution K p f ζ = -ζ) : GL (Fin 2) (fixedSubfield K p f) :=
  ⟨!![0, tF hζ; 1, 0], !![0, 1; (tF hζ)⁻¹, 0], by
    have := tF_ne_zero hζ0 h2 hζ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this], by
    have := tF_ne_zero hζ0 h2 hζ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, this]⟩

theorem psiEquiv_neg_one (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ) (h2 : (2 : K) ≠ 0)
    (hμ : unitaryInvolution K p f μ * μ = -1) : psiEquiv hζ0 hζ h2 hμ (-1) = negOneSU K p f := by
  have hμ0 := ne_zero_of_norm_neg_one _ hμ
  apply suMat_injective
  rw [suMat_psiEquiv, suMat_negOneSU, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  have : hypMat ζ (-1 : Matrix (Fin 2) (Fin 2) (fixedSubfield K p f)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hypMat]
  rw [this, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, wittMat_mul_inv h2 hμ0]

theorem suMat_psiEquiv_conj (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ) (h2 : (2 : K) ≠ 0)
    (hμ : unitaryInvolution K p f μ * μ = -1) (s : SL(2, fixedSubfield K p f)) :
    Matrix.diagonal ![(1 : K), -1] * suMat (psiEquiv hζ0 hζ h2 hμ s) *
        Matrix.diagonal ![(1 : K), -1] =
      suMat (psiEquiv hζ0 hζ h2 hμ
        (slConjugation 2 (fixedSubfield K p f) (gSwapGL hζ0 h2 hζ) s)) := by
  have ht0 := tF_ne_zero hζ0 h2 hζ
  rw [suMat_psiEquiv, suMat_psiEquiv, psi_conj_diag hζ0 hζ h2 hμ,
    slConjugation_matrix]
  congr 3
  exact (swap_mul_mul ht0 _).symm

end ChartU

section DiagDataU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}
  {ζ μ : K}

theorem mem_axisSub_chartU_iff (hn : 2 ≤ n) {g : Su K p f n} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (suMat g) τ) {e : Su K p f n} (he : e ∈ signGroupU K p f n) :
    e ∈ axisSub (signGroupU K p f n) ((rootSU2 K p f hn).map (MulAut.conj g).toMonoidHom) ↔
      entU e (τ ⟨0, by omega⟩) = entU e (τ ⟨1, by omega⟩) := by
  obtain ⟨he', hent⟩ := conj_mem_signGroupU hg he
  have hconj : ∀ A : Su K p f 2,
      (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) * e =
          e * (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) ↔
        (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) A * (g⁻¹ * e * g)⁻¹ =
          blockEmb K p f n 2 0 (by omega) A := by
    intro A
    constructor
    · intro h
      have : (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) A =
          blockEmb K p f n 2 0 (by omega) A * (g⁻¹ * e * g) := by
        calc (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) A
            = g⁻¹ * (e * (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) * e) * g := by rw [h]
          _ = blockEmb K p f n 2 0 (by omega) A * (g⁻¹ * e * g) := by group
      rw [this]
      group
    · intro h
      have h' : (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) A =
          blockEmb K p f n 2 0 (by omega) A * (g⁻¹ * e * g) := by
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h
      calc g * blockEmb K p f n 2 0 (by omega) A * g⁻¹ * e
          = g * (blockEmb K p f n 2 0 (by omega) A * (g⁻¹ * e * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) A) * g⁻¹ := by rw [h']
        _ = e * (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) := by group
  rw [mem_axisSub_iff]
  constructor
  · rintro ⟨-, hcomm⟩
    have h1 := (hconj (rotSU _)).mp (hcomm _ ⟨blockEmb K p f n 2 0 (by omega) (rotSU _),
      ⟨rotSU _, rfl⟩, rfl⟩)
    have h2 := congrArg suMat h1
    rw [suMat_conj_blockEmb hn he', suMat_blockEmb] at h2
    have h3 := blockMat_injective (by omega : 0 + 2 ≤ n) h2
    have h5 : entU (g⁻¹ * e * g) ⟨0, by omega⟩ * (-1) * entU (g⁻¹ * e * g) ⟨1, by omega⟩ = -1 := by
      simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, suMat, rotSU, rotMat] using
        congrFun (congrFun h3 0) 1
    rw [← hent, ← hent]
    have hb := entU_mul_self he' ⟨1, by omega⟩
    have h6 : entU (g⁻¹ * e * g) ⟨0, by omega⟩ * entU (g⁻¹ * e * g) ⟨1, by omega⟩ = 1 := by
      linear_combination -h5
    calc entU (g⁻¹ * e * g) ⟨0, by omega⟩
        = entU (g⁻¹ * e * g) ⟨0, by omega⟩ * (entU (g⁻¹ * e * g) ⟨1, by omega⟩ *
            entU (g⁻¹ * e * g) ⟨1, by omega⟩) := by rw [hb, mul_one]
      _ = entU (g⁻¹ * e * g) ⟨1, by omega⟩ := by
        rw [← mul_assoc, h6, one_mul]
  · intro h
    refine ⟨he, fun k hk => ?_⟩
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hk
    show (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹) * e =
      e * (g * blockEmb K p f n 2 0 (by omega) A * g⁻¹)
    rw [hconj]
    apply suMat_injective
    rw [suMat_conj_blockEmb hn he', suMat_blockEmb]
    have hab : entU (g⁻¹ * e * g) ⟨1, by omega⟩ = entU (g⁻¹ * e * g) ⟨0, by omega⟩ := by
      rw [hent, hent]
      exact h.symm
    rw [hab, diagonal_two_conj_self (entU_mul_self he' _)]

theorem diagData_chartU (hn : 3 ≤ n) (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ)
    (h2 : (2 : K) ≠ 0) (hμ : unitaryInvolution K p f μ * μ = -1) {g : Su K p f n}
    {τ : Equiv.Perm (Fin n)} (hg : IsMonomialFor (suMat g) τ) :
    DiagData (chartU (by omega : 2 ≤ n) g (psiEquiv hζ0 hζ h2 hμ)) (signGroupU K p f n) where
  inj := chartU_injective _ g _
  comm := fun x hx y hy => signGroupU_comm hx hy
  sq := fun x hx => signGroupU_sq hx
  neg_mem := by
    rw [mem_signGroupU, chartU_apply, psiEquiv_neg_one, suMat_mul, suMat_mul]
    change IsSignDiag (suMat g * suMat (rootInvSU K p f (by omega : 2 ≤ n)) * suMat g⁻¹)
    rw [suMat_rootInvSU, suMonomial_conj_negBlock hg (by omega : 0 + 2 ≤ n)]
    exact isSignDiag_zMat _
  diag := fun e he => by
    obtain ⟨he', -⟩ := conj_mem_signGroupU hg he
    by_cases hab : entU (g⁻¹ * e * g) ⟨0, by omega⟩ = entU (g⁻¹ * e * g) ⟨1, by omega⟩
    · refine ⟨1, fun s => ?_⟩
      have key : (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) (psiEquiv hζ0 hζ h2 hμ s) *
          (g⁻¹ * e * g)⁻¹ = blockEmb K p f n 2 0 (by omega) (psiEquiv hζ0 hζ h2 hμ s) := by
        apply suMat_injective
        rw [suMat_conj_blockEmb (by omega) he', suMat_blockEmb, ← hab,
          diagonal_two_conj_self (entU_mul_self he' _)]
      rw [chartU_apply, chartU_apply, map_one, MulAut.one_apply]
      conv_rhs => rw [← key]
      group
    · refine ⟨gSwapGL hζ0 h2 hζ, fun s => ?_⟩
      have hb := eq_neg_of_ne_of_sign (entU_cases he' ⟨0, by omega⟩)
        (entU_cases he' ⟨1, by omega⟩) hab
      have key : (g⁻¹ * e * g) * blockEmb K p f n 2 0 (by omega) (psiEquiv hζ0 hζ h2 hμ s) *
          (g⁻¹ * e * g)⁻¹ = blockEmb K p f n 2 0 (by omega) (psiEquiv hζ0 hζ h2 hμ
            (slConjugation 2 (fixedSubfield K p f) (gSwapGL hζ0 h2 hζ) s)) := by
        apply suMat_injective
        rw [suMat_conj_blockEmb (by omega) he', suMat_blockEmb, hb,
          diagonal_two_neg_conj _ (entU_mul_self he' _), suMat_psiEquiv_conj hζ0 hζ h2 hμ]
      rw [chartU_apply, chartU_apply]
      conv_rhs => rw [← key]
      group
  index_two := by
    have hn2 : 2 ≤ n := by omega
    have h02 : τ ⟨0, by omega⟩ ≠ τ ⟨2, by omega⟩ := fun h => by
      have := τ.injective h
      simp [Fin.ext_iff] at this
    have h01 : τ ⟨0, by omega⟩ ≠ τ ⟨1, by omega⟩ := fun h => by
      have := τ.injective h
      simp [Fin.ext_iff] at this
    let T : Pair n := ⟨{τ ⟨0, by omega⟩, τ ⟨2, by omega⟩}, Finset.card_pair h02⟩
    rw [range_chartU, Subgroup.relIndex_eq_two_iff]
    refine ⟨zEltU K p f T, zEltU_mem_signGroupU T, fun b hb => ?_⟩
    have hbT : b * zEltU K p f T ∈ signGroupU K p f n :=
      (signGroupU K p f n).mul_mem hb (zEltU_mem_signGroupU T)
    rw [xor_iff_iff_not, mem_axisSub_chartU_iff hn2 hg hbT, mem_axisSub_chartU_iff hn2 hg hb,
      entU_mul hb (zEltU_mem_signGroupU T), entU_mul hb (zEltU_mem_signGroupU T), zEltU_entU,
      zEltU_entU, ite_eq_left (by simp [T]), ite_eq_right (by simp [T, Ne.symm h01]),
      mul_neg, mul_one, mul_one]
    exact neg_eq_iff_not_eq_of_sign h2 (entU_cases hb _) (entU_cases hb _)

end DiagDataU

section SigmaU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem inSigma_LcU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hn : 3 ≤ n) (T : Pair n) :
    InSigma (fixedSubfield K p f) (signGroupU K p f n) (LcU K p f T) := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨μ, hμ⟩ := exists_norm_eq_neg_one hK
  obtain ⟨g, τ, hg, hT⟩ := exists_suMonomial_of_pair (K := K) (p := p) (f := f) (by omega) T
  refine ⟨chartU (by omega) g (psiEquiv hζ0 hζ h2 hμ), ?_, diagData_chartU hn hζ0 hζ h2 hμ hg⟩
  rw [range_chartU, LcU_eq_map_conj h2 hg (by omega : 0 + 2 ≤ n) hT]
  rfl

theorem exists_pair_of_inSigmaU (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {hn : 2 ≤ n}
    {L : Subgroup (Su K p f n)} {i : Su K p f n} (hL : IsLongRootSU2 K p f hn L i)
    (hS : InSigma (fixedSubfield K p f) (signGroupU K p f n) L) :
    ∃ T : Pair n, L = LcU K p f T := by
  have h2 := two_ne_zero_of_charP_ne_two (K := K) hp
  have h2F : (2 : fixedSubfield K p f) ≠ 0 :=
    CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card _ (odd_natCard_fixedSubfield hK hp)
  obtain ⟨φ, hφ, hD⟩ := hS
  have hmem : φ (-1) ∈ L := hφ ▸ ⟨-1, rfl⟩
  have hord : orderOf (φ (-1)) = 2 := by
    rw [orderOf_injective φ hD.inj (-1)]
    exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf _ h2F
  have hi : φ (-1) = i := hL.eq_of_orderOf_eq_two hK hp hmem hord
  have hiE : i ∈ signGroupU K p f n := hi ▸ hD.neg_mem
  obtain ⟨N, hN⟩ := (mem_signGroupU.mp hiE).exists_zMat
  have hcard : N.card = 2 := by
    have := hL.finrank_minusSpaceSU h2
    rw [minusSpaceSU, hN, finrank_eigSpace_zMat h2] at this
    exact this
  refine ⟨⟨N, hcard⟩, ?_⟩
  rw [hL.eq_longRootGroupSU h2, hN]
  rfl

end SigmaU

end CFSG.ClassicalInvolution.Models
