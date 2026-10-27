module

public import CFSG.Sporadic.Schreier.J4SRank
public import CFSG.Sporadic.Schreier.J4SReal
public import Certificates.Certificate12603
public import CFSG.Sporadic.Schreier.J4SElevenBase

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.J4Schreier
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

def polyOf (es : List ℕ) : Polynomial (ZMod 2) :=
  (es.map fun e => (Polynomial.X : Polynomial (ZMod 2)) ^ e).sum

def polySum (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) (es : List ℕ) :
    Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  (es.map fun e => M ^ e).sum

theorem polyOf_eval_one (es : List ℕ) : (polyOf es).eval 1 = (es.length : ZMod 2) := by
  induction es with
  | nil => simp [polyOf]
  | cons e es ih =>
    simp only [polyOf, List.map_cons, List.sum_cons, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_X, one_pow, List.length_cons, Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [ih]; ring

theorem vecMulLinear_pow (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) (n : ℕ) :
    Matrix.vecMulLinear (M ^ n) = Matrix.vecMulLinear M ^ n := by
  induction n with
  | zero =>
    exact LinearMap.ext fun w => by simp
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih]
    exact LinearMap.ext fun w => by
      simp [Module.End.mul_apply, Matrix.vecMul_vecMul]

theorem aeval_polyOf_vecMulLinear (M : Matrix (Fin 112) (Fin 112) (ZMod 2)) (es : List ℕ) :
    Polynomial.aeval (Matrix.vecMulLinear M : Module.End (ZMod 2) (Fin 112 → ZMod 2))
      (polyOf es) = Matrix.vecMulLinear (polySum M es) := by
  induction es with
  | nil => exact LinearMap.ext fun w => by simp [polyOf, polySum]
  | cons e es ih =>
    simp only [polyOf, polySum, List.map_cons, List.sum_cons, map_add, Polynomial.aeval_X_pow,
      vecMulLinear_pow] at ih ⊢
    rw [ih]

theorem ker_vecMulLinear_eq_rowFix (T : Matrix (Fin 112) (Fin 112) (ZMod 2)) :
    LinearMap.ker (Matrix.vecMulLinear T) = rowFix (T + 1) := by
  ext v
  rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply, mem_rowFix, Matrix.vecMul_add,
    Matrix.vecMul_one]
  exact add_eq_right.symm

theorem rowsMatrix_replicate_zero : rowsMatrix 112 (Array.replicate 112 0) = 0 := by
  ext i j
  rw [CFSG.Sporadic.SmallF2.rowsMatrix_apply]
  simp [toVecD_zero]

theorem rowsMatrix_polyRows {M : Array ℕ} (hM : Sp.WF M) (es : List ℕ) :
    rowsMatrix 112 (polyRows M es) = polySum (rowsMatrix 112 M) es := by
  induction es with
  | nil => rw [polyRows, rowsMatrix_replicate_zero]; simp [polySum]
  | cons e es ih =>
    rw [polyRows, rowsMatrix_xorRows112, ih]
    have h : rowsMatrix 112 (O.pow M e) = rowsMatrix 112 M ^ e := (Sp.pow_spec hM e).2
    simp only [polySum, List.map_cons, List.sum_cons]
    rw [h]

theorem finrank_ker_conjAlgEquiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] V) (G : Module.End (ZMod 2) V) :
    Module.finrank (ZMod 2) (LinearMap.ker (e.conjAlgEquiv (ZMod 2) G)) =
      Module.finrank (ZMod 2) (LinearMap.ker G) := by
  have : LinearMap.ker (e.conjAlgEquiv (ZMod 2) G) = (LinearMap.ker G).map (e : V →ₗ[ZMod 2] V) := by
    ext x
    rw [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.conjAlgEquiv_apply]
    constructor
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      simpa using hx
    · rintro ⟨y, hy, rfl⟩
      simp [LinearMap.mem_ker.1 hy]
  rw [this, LinearEquiv.finrank_map_eq]

theorem finrank_ker_aeval_conj {c0 c' h : J} (hc : h * c' * h⁻¹ = c0) (f : Polynomial (ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval
      (rowLin c0 : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) f)) =
    Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval
      (rowLin c' : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) f)) := by
  have e : (rowLin c0 : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) =
      (rowLin h).conjAlgEquiv (ZMod 2) (rowLin c' : (Fin 112 → ZMod 2) →ₗ[ZMod 2] _) := by
    rw [LinearEquiv.conjAlgEquiv_apply, ← hc, map_mul, map_mul, map_inv]
    exact LinearMap.ext fun w => rfl
  rw [e, Polynomial.aeval_algEquiv, AlgHom.comp_apply]
  exact finrank_ker_conjAlgEquiv _ _

theorem factorization_eq_one_of {N r : ℕ} (hr : r.Prime) (hN : N ≠ 0) (h1 : r ∣ N)
    (h2 : ¬ r ∣ N / r) : N.factorization r = 1 := by
  obtain ⟨m, rfl⟩ := h1
  have hm0 : m ≠ 0 := by rintro rfl; simp at hN
  rw [Nat.mul_div_cancel_left _ hr.pos] at h2
  rw [Nat.factorization_mul hr.ne_zero hm0, Finsupp.add_apply, hr.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd h2]

theorem exists_conj_zpowers {r : ℕ} (hr : r.Prime)
    (hf : (Nat.card J).factorization r = 1) {c0 c : J} (h0 : orderOf c0 = r)
    (hc : orderOf c = r) : ∃ h : J, ∃ c' ∈ Subgroup.zpowers c, h * c' * h⁻¹ = c0 := by
  have := Fact.mk hr
  have hP : IsPGroup r (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  have hcard0 : Nat.card (Subgroup.zpowers c0) = r ^ (Nat.card J).factorization r := by
    rw [Nat.card_zpowers, h0, hf, pow_one]
  obtain ⟨h, hh⟩ := exists_conj_mem_sylow (Sylow.ofCard (Subgroup.zpowers c0) hcard0) hP
  rw [Sylow.coe_ofCard] at hh
  have ho1 : orderOf (h * c * h⁻¹) = r := by
    rw [← hc]
    exact (orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective c)
  have heq : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers c0 := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hh) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, ho1, h0]
  have h0mem : c0 ∈ Subgroup.zpowers (h * c * h⁻¹) := by
    rw [heq]; exact Subgroup.mem_zpowers c0
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h0mem
  refine ⟨h, c ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) i, ?_⟩
  rw [← hi, conj_zpow]

def primeElt (C : PrimeKerCase) : J := signedWord a b C.word ^ C.exp

theorem rep_primeElt (C : PrimeKerCase) :
    Rep Sp φ (primeElt C) (primeKerElt C) :=
  rep_powP (rep_wordP (rep_a j4Facts.mat) (rep_b j4Facts.mat) C.word) C.exp

theorem rowLin_inv_eq (g : J) :
    (rowLin g⁻¹ : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) =
      Matrix.vecMulLinear (φ g) := by
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.coe_coe, rowLin_apply, Matrix.vecMulLinear_apply]
  simp [φ_apply]

theorem primeKerCase_spec {C : PrimeKerCase}
    (hC : primeKerCaseOK C = true) (hk : C.k ≤ 112) :
    primeElt C ^ C.order = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval
        (rowLin (primeElt C)⁻¹ : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2))
        (polyOf C.exps))) = C.k := by
  have hg := rep_primeElt C
  unfold primeKerCaseOK at hC
  rw [Bool.and_eq_true] at hC
  obtain ⟨h1, h2⟩ := hC
  refine ⟨eq_of_rep (rep_powP hg C.order) rep_oneP h1, ?_⟩
  rw [rowLin_inv_eq, aeval_polyOf_vecMulLinear, ker_vecMulLinear_eq_rowFix]
  refine finrank_rowFix_of_ok hk ?_ h2
  rw [rowsMatrix_xorRows112, rowsMatrix_polyRows hg.1,
    CFSG.Sporadic.SmallF2.rowsMatrix_idRows]
  have := hg.2.2.1
  rw [show rowsMatrix 112 (primeKerElt C).1 = φ (primeElt C) from this]

theorem prime_case {C : PrimeKerCase} {r : ℕ}
    (hC : primeKerCaseOK C = true) (hr : r.Prime) (hord : C.order = r)
    (hcard : (Nat.card J).factorization r = 1) (hk : C.k ≤ 112) (hk0 : 0 < C.k)
    (hk10 : ¬ 10 ∣ C.k) (hodd : (C.exps.length : ZMod 2) ≠ 0) {c : J}
    (hc : orderOf c = r) :
    ∃ c' ∈ Subgroup.zpowers c, ∃ f : Polynomial (ZMod 2), f.eval 1 ≠ 0 ∧
      ¬ 10 ∣ Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval
        (rowLin c' : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) f)) := by
  subst hord
  have := Fact.mk hr
  obtain ⟨hpow, hdim⟩ := primeKerCase_spec hC hk
  have hf1 : (polyOf C.exps).eval 1 ≠ 0 := by rw [polyOf_eval_one]; exact hodd
  have hne : (primeElt C)⁻¹ ≠ 1 := by
    intro h1
    rw [h1] at hdim
    have h2 : (polyOf C.exps).eval 1 = 1 := by
      generalize (polyOf C.exps).eval 1 = x at hf1
      revert x; decide
    have h3 : (((1 : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
        (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
        (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) =
        (1 : Module.End (ZMod 2) (Fin 112 → ZMod 2)) := rfl
    rw [map_one, h3, Polynomial.aeval_def, Polynomial.eval₂_at_one, h2] at hdim
    rw [map_one] at hdim
    have h4 : LinearMap.ker (1 : Module.End (ZMod 2) (Fin 112 → ZMod 2)) = ⊥ := LinearMap.ker_id
    rw [h4, finrank_bot] at hdim
    omega
  have h0 : orderOf (primeElt C)⁻¹ = C.order :=
    orderOf_eq_prime (by rw [inv_pow, hpow, inv_one]) hne
  obtain ⟨h, c', hc', hhc⟩ := exists_conj_zpowers hr hcard h0 hc
  refine ⟨c', hc', polyOf C.exps, hf1, ?_⟩
  rw [← finrank_ker_aeval_conj hhc, hdim]
  exact hk10

theorem card_J_factorization_one {r : ℕ} (hr : r.Prime)
    (h1 : r ∣ 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43)
    (h2 : ¬ r ∣ (2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43) / r) :
    (Nat.card J).factorization r = 1 := by
  rw [card_J_eq]
  exact factorization_eq_one_of hr (by norm_num) h1 h2

theorem primeKer_eq : primeKerOK = true :=
  Certificates.certificate12603

theorem exists_prime_kernel_poly
    {r : ℕ} (hr : r ∈ ({5, 7, 23, 29, 31, 37, 43} : Finset ℕ)) {c : J} (hc : orderOf c = r) :
    ∃ c' ∈ Subgroup.zpowers c, ∃ f : Polynomial (ZMod 2), f.eval 1 ≠ 0 ∧
      ¬ 10 ∣ Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval
        (rowLin c' : (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) f)) := by
  have hall := primeKer_eq
  unfold primeKerOK at hall
  simp only [Bool.and_eq_true] at hall
  obtain ⟨⟨⟨⟨⟨⟨h5, h7⟩, h23⟩, h29⟩, h31⟩, h37⟩, h43⟩ := hall
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact prime_case (C := kerCase5) (r := 5) h5 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase7) (r := 7) h7 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase23) (r := 23) h23 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase29) (r := 29) h29 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase31) (r := 31) h31 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase37) (r := 37) h37 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc
  · exact prime_case (C := kerCase43) (r := 43) h43 (by norm_num) rfl
      (card_J_factorization_one (by norm_num) (by norm_num) (by norm_num)) (by decide)
      (by decide) (by decide) (by decide) hc

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
