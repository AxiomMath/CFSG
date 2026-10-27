module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLiftDefs
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.HardMathSupport.Seitz.TrialityEven.PhiPrimePm

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts
open Polynomial Matrix

variable {p f : ℕ} {F : Type} [Field F]

private lemma pow_frob_eq_bar (h : UnitaryFieldData p f F) (a : F) :
    a ^ (p ^ (3 * f)) = h.bar a := by
  haveI : Finite F := h.finite
  letI : Fintype F := Fintype.ofFinite F
  have hq2 : a ^ ((p ^ f) ^ 2) = a := by
    rw [← h.card_eq_sq, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  rw [h.bar_apply]
  calc a ^ (p ^ (3 * f)) = a ^ (((p ^ f) ^ 2) * (p ^ f)) := by
        rw [show p ^ (3 * f) = ((p ^ f) ^ 2) * (p ^ f) by
          rw [show 3 * f = f * 2 + f by omega, pow_add, pow_mul]]
    _ = (a ^ ((p ^ f) ^ 2)) ^ (p ^ f) := by rw [pow_mul]
    _ = a ^ (p ^ f) := by rw [hq2]

private lemma charP_matrix (h : UnitaryFieldData p f F) :
    CharP (Matrix (Fin 3) (Fin 3) F) p := by
  haveI : CharP F p := h.charP
  refine charP_of_injective_algebraMap (R := F) (A := Matrix (Fin 3) (Fin 3) F) ?_ p
  intro a b hab
  have h00 := congrFun (congrFun hab 0) 0
  simpa [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_apply] using h00

private lemma star_pow (h : UnitaryFieldData p f F) (M : Matrix (Fin 3) (Fin 3) F) (n : ℕ) :
    (((M ^ n).map h.bar)ᵀ) = ((M.map h.bar)ᵀ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.map_mul, Matrix.transpose_mul, ih, pow_succ']

private lemma star_algebraMap (h : UnitaryFieldData p f F) (a : F) :
    (((algebraMap F (Matrix (Fin 3) (Fin 3) F) a).map h.bar)ᵀ) =
      algebraMap F (Matrix (Fin 3) (Fin 3) F) (h.bar a) := by
  rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map (map_zero h.bar),
    Matrix.diagonal_transpose, Matrix.algebraMap_eq_diagonal]
  simp [Pi.algebraMap_apply]

private lemma star_aeval (h : UnitaryFieldData p f F) (Bm : Matrix (Fin 3) (Fin 3) F)
    (P : F[X]) :
    (((aeval Bm P).map h.bar)ᵀ) = aeval (((Bm.map h.bar)ᵀ)) (P.map h.bar) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.map_add, Polynomial.aeval_add, Polynomial.aeval_add,
        Matrix.map_add (⇑h.bar) (map_add h.bar), Matrix.transpose_add, hP, hQ]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial,
        Matrix.map_mul, Matrix.transpose_mul, star_pow, star_algebraMap]
      exact (Algebra.commute_algebraMap_left (h.bar a) (((Bm.map h.bar)ᵀ) ^ n)).eq.symm

private lemma commute_aeval_aeval (h : UnitaryFieldData p f F)
    (Bm : Matrix (Fin 3) (Fin 3) F) (P Q : F[X]) :
    Commute (aeval Bm P) (aeval Bm Q) := by
  have h1 : Commute Bm (aeval Bm P) :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute
      (Polynomial.aeval_mem_adjoin_singleton F Bm) (Commute.refl Bm)
  exact Algebra.commute_of_mem_adjoin_singleton_of_commute
    (Polynomial.aeval_mem_adjoin_singleton F Bm) h1.symm

private lemma pow_aeval (h : UnitaryFieldData p f F) (Bm : Matrix (Fin 3) (Fin 3) F)
    (P : F[X]) :
    (aeval Bm P) ^ (p ^ (3 * f)) = aeval (Bm ^ (p ^ (3 * f))) (P.map h.bar) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : CharP (Matrix (Fin 3) (Fin 3) F) p := charP_matrix h
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.map_add, Polynomial.aeval_add, Polynomial.aeval_add,
        add_pow_char_pow_of_commute p (3 * f) (commute_aeval_aeval h Bm P Q), hP, hQ]
  | monomial n a =>
      rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.aeval_monomial,
        (Algebra.commute_algebraMap_left a (Bm ^ n)).mul_pow]
      rw [show (algebraMap F (Matrix (Fin 3) (Fin 3) F) a) ^ (p ^ (3 * f)) =
          algebraMap F (Matrix (Fin 3) (Fin 3) F) (h.bar a) by
        rw [← map_pow, pow_frob_eq_bar h]]
      rw [show (Bm ^ n) ^ (p ^ (3 * f)) = (Bm ^ (p ^ (3 * f))) ^ n by
        rw [pow_right_comm]]

private lemma irreducible_cubic {c : Fˣ} (hcube : ∀ b : F, b ^ 3 ≠ (c : F)) :
    Irreducible (X ^ 3 - C (c : F) : F[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_three hcube

private lemma card_cubicField (h : UnitaryFieldData p f F) (c : Fˣ) :
    Nat.card (AdjoinRoot (X ^ 3 - C (c : F))) = (p ^ f) ^ 6 := by
  have hg0 : (X ^ 3 - C (c : F) : F[X]) ≠ 0 :=
    (monic_X_pow_sub_C (c : F) (by norm_num : (3 : ℕ) ≠ 0)).ne_zero
  let pb := AdjoinRoot.powerBasis (K := F) hg0
  have hdim : pb.dim = 3 := by
    rw [AdjoinRoot.powerBasis_dim]
    simpa using natDegree_X_pow_sub_C (R := F) (n := 3) (r := (c : F))
  let b : Module.Basis (Fin 3) F (AdjoinRoot (X ^ 3 - C (c : F))) :=
    pb.basis.reindex (finCongr hdim)
  have h1 := Nat.card_congr b.equivFun.toEquiv
  rw [h1, Nat.card_fun, h.card_eq_sq]
  simp only [Nat.card_fin]
  ring

private lemma three_dvd_phi6_int {q : ℕ} (h3 : 3 ∣ q + 1) :
    (3 : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := by
    obtain ⟨s, hs⟩ := h3
    exact ⟨s - 1, by omega⟩
  rw [hk]
  push_cast
  have h : (3 * (k : ℤ) + 2) ^ 2 + -1 * (3 * (k : ℤ) + 2) + 1 =
      3 * (3 * (k : ℤ) ^ 2 + 3 * k + 1) := by ring
  rw [h]
  exact dvd_mul_right 3 _

private lemma three_dvd_phi6 {q : ℕ} (h3 : 3 ∣ q + 1) :
    3 ∣ q ^ 2 - q + 1 := by
  obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 2 := by
    obtain ⟨s, hs⟩ := h3
    exact ⟨s - 1, by omega⟩
  rw [hk]
  have h1 : (3 * k + 2) ^ 2 = 9 * k ^ 2 + 12 * k + 4 := by ring
  have h2 : 9 * k ^ 2 + 12 * k + 4 - (3 * k + 2) + 1 =
      3 * (3 * k ^ 2 + 3 * k + 1) := by omega
  rw [h1, h2]
  exact dvd_mul_right 3 _

private lemma cube_add_one_factor {q : ℕ} (hq : 1 ≤ q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  obtain ⟨w, hw⟩ : ∃ w, q = w + 1 := ⟨q - 1, by omega⟩
  rw [hw]
  have h2 : (w + 1) ^ 2 - (w + 1) + 1 = w * (w + 1) + 1 := by
    have e : (w + 1) ^ 2 = (w + 1) + w * (w + 1) := by ring
    omega
  rw [h2]
  ring

private lemma not_dvd_succ_of_dvd_phi6 {r q : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq : 2 ≤ q) (h : r ∣ q ^ 2 - q + 1) : ¬ r ∣ q + 1 := by
  intro hdiv
  have e : q ^ 2 - q + 1 = (q + 1) * (q - 2) + 3 := by
    obtain ⟨w, rfl⟩ : ∃ w, q = w + 2 := ⟨q - 2, by omega⟩
    have h1 : (w + 2) ^ 2 = (w + 2) + ((w + 3) * w + 2) := by ring
    have h2 : (w + 2) ^ 2 - (w + 2) = (w + 3) * w + 2 := by omega
    simp only [h2, Nat.add_sub_cancel]
  have hdvd : r ∣ 3 := (Nat.dvd_add_right (hdiv.mul_right (q - 2))).1 (by
    rw [← e]; exact h)
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

private lemma not_dvd_sub_one_of_dvd_phi6 {r q : ℕ} (hr : r.Prime)
    (hq : 2 ≤ q) (h : r ∣ q ^ 2 - q + 1) : ¬ r ∣ q - 1 := by
  intro hdiv
  have h1 : q ^ 2 - q = (q - 1) * q := by
    obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    rw [ht]
    have e : (t + 1) ^ 2 = (t + 1) + t * (t + 1) := by ring
    have e2 : (t + 1) ^ 2 - (t + 1) = t * (t + 1) := by omega
    rw [show t + 1 - 1 = t by omega]
    exact e2
  have h2 : r ∣ q ^ 2 - q := by rw [h1]; exact hdiv.mul_right q
  have h3 : r ∣ 1 := (Nat.dvd_add_right h2).1 (by
    have e : q ^ 2 - q + 1 = (q ^ 2 - q) + 1 := by omega
    rw [e]; exact h)
  exact hr.one_lt.ne' (Nat.dvd_one.1 h3)

private lemma not_dvd_sq_sub_one_of_dvd_phi6 {r q : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hq : 2 ≤ q) (h : r ∣ q ^ 2 - q + 1) : ¬ r ∣ q ^ 2 - 1 := by
  intro hdiv
  have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨t, ht⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
    rw [ht]
    have hpoly : (t + 1) ^ 2 = 1 + t * ((t + 1) + 1) := by ring
    have h2 : (t + 1) ^ 2 - 1 = t * ((t + 1) + 1) := by omega
    rw [show t + 1 - 1 = t by omega]
    exact h2
  rw [e] at hdiv
  rcases (Nat.Prime.dvd_mul hr).1 hdiv with h1 | h1
  · exact not_dvd_sub_one_of_dvd_phi6 hr hq h h1
  · exact not_dvd_succ_of_dvd_phi6 hr hr5 hq h h1

theorem exists_torusPrime {q : ℕ} (hq : 2 < q) (h3 : 3 ∣ q + 1) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ r ∣ q ^ 2 - q + 1 ∧ ¬ r ∣ q + 1 ∧
      ¬ r ∣ q ^ 3 * (q ^ 2 - 1) := by
  have hq4 : 4 ≤ q := by
    by_contra h
    interval_cases q <;> norm_num at h3
  obtain ⟨r, hrp, hr5, hrdZ, hrq⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityEven.exists_prime_ge_five_dvd_phi_pm hq4
      (ε := -1) (Or.inr rfl) (three_dvd_phi6_int h3)
  have hle : q ≤ q ^ 2 := by nlinarith
  have hcast : ((q ^ 2 - q + 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  have hrd : r ∣ q ^ 2 - q + 1 := by
    rw [← Int.natCast_dvd_natCast, hcast]
    exact hrdZ
  have hrne3 : r ≠ 3 := by omega
  have hqadd := not_dvd_succ_of_dvd_phi6 hrp hr5 (by omega) hrd
  have hqsub := not_dvd_sub_one_of_dvd_phi6 hrp (by omega) hrd
  have hq2m1 := not_dvd_sq_sub_one_of_dvd_phi6 hrp hr5 (by omega) hrd
  have hq3 : ¬ r ∣ q ^ 3 := fun h => hrq (hrp.dvd_of_dvd_pow h)
  refine ⟨r, hrp, hrne3, hrd, hqadd, ?_⟩
  rw [Nat.Prime.dvd_mul hrp]
  rintro (h | h)
  · exact hq3 h
  · exact hq2m1 h

private lemma coe_B_pow_three (h : UnitaryFieldData p f F) (B : unitaryIsom3 h) {c : Fˣ}
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) ^ 3 =
      algebraMap F (Matrix (Fin 3) (Fin 3) F) (c : F) := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  have hbs := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hB
  have hdiag : (diagonal fun _ : Fin 3 => (c : F)) =
      algebraMap F (Matrix (Fin 3) (Fin 3) F) (c : F) := by
    rw [Matrix.algebraMap_eq_diagonal]
    simp [Pi.algebraMap_apply]
  simpa [Bm, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, hdiag] using hbs

private lemma B_pow_q3_add_one (h : UnitaryFieldData p f F)
    (h3 : 3 ∣ p ^ f + 1) (B : unitaryIsom3 h) {c : Fˣ} (hc : h.norm (c : F) = 1)
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) ^ (p ^ (3 * f) + 1) = 1 := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  have hB3 : Bm ^ 3 = algebraMap F (Matrix (Fin 3) (Fin 3) F) (c : F) :=
    coe_B_pow_three h B hB
  have hcq1 : (c : F) ^ (p ^ f + 1) = 1 := by
    rw [← h.norm_eq_pow]
    exact hc
  have hBq1 : (Bm ^ (p ^ f + 1)) ^ 3 = 1 := by
    rw [← pow_mul, show (p ^ f + 1) * 3 = 3 * (p ^ f + 1) by ring, pow_mul, hB3,
      ← map_pow (algebraMap F (Matrix (Fin 3) (Fin 3) F)), hcq1, map_one]
  have hq3exp := cube_add_one_factor (q := p ^ f) (Nat.one_le_pow _ _ h.prime.pos)
  obtain ⟨k, hk⟩ := three_dvd_phi6 h3
  have hq3eq : (p ^ f) ^ 3 = p ^ (3 * f) := by
    rw [← pow_mul]
    ring_nf
  rw [← hq3eq, hq3exp, hk, pow_mul, pow_mul, hBq1, one_pow]

private lemma star_coe_B_eq_pow (h : UnitaryFieldData p f F)
    (h3 : 3 ∣ p ^ f + 1) (B : unitaryIsom3 h) {c : Fˣ} (hc : h.norm (c : F) = 1)
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    (((((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ) =
      (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) ^ (p ^ (3 * f)) := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  have hBmstar : (((Bm.map h.bar)ᵀ) * Bm) = 1 := by
    have hB' := (mem_unitaryIsom3 (h := h)).mp B.2
    simpa [Bm] using hB'
  have hBq3 : Bm ^ (p ^ (3 * f) + 1) = 1 := B_pow_q3_add_one h h3 B hc hB
  let BGL : GL (Fin 3) F := B
  let Bstar : GL (Fin 3) F :=
    Units.mkOfMulEqOne ((Bm.map h.bar)ᵀ) BGL hBmstar
  have hBstar_val : (Bstar : Matrix (Fin 3) (Fin 3) F) = ((Bm.map h.bar)ᵀ) := rfl
  have hBstar_inv : Bstar = BGL⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    apply Units.ext
    rw [Units.val_mul, hBstar_val]
    exact hBmstar
  have hBGLpow' : BGL ^ (p ^ (3 * f)) * BGL = 1 := by
    apply Units.ext
    rw [← pow_succ, Units.val_pow_eq_pow_val]
    exact hBq3
  have hBpow_inv : BGL ^ (p ^ (3 * f)) = BGL⁻¹ :=
    eq_inv_of_mul_eq_one_left hBGLpow'
  have h := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F))
    (hBstar_inv.trans hBpow_inv.symm)
  simpa [hBstar_val, Bm, BGL, Units.val_pow_eq_pow_val] using h

private lemma exists_phi (h : UnitaryFieldData p f F) (B : unitaryIsom3 h) {c : Fˣ}
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hcube : ∀ b : F, b ^ 3 ≠ (c : F)) :
    ∃ φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F,
      (∀ P : F[X], φ (AdjoinRoot.mk (X ^ 3 - C (c : F)) P) =
        aeval (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) P) ∧
      φ (AdjoinRoot.root (X ^ 3 - C (c : F))) =
        (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  have hB3 : Bm ^ 3 = algebraMap F (Matrix (Fin 3) (Fin 3) F) (c : F) :=
    coe_B_pow_three h B hB
  have hroot : aeval Bm (X ^ 3 - C (c : F)) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hB3, sub_self]
  let φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F :=
    Ideal.Quotient.lift (Ideal.span {(X ^ 3 - C (c : F) : F[X])})
      (Polynomial.aeval Bm).toRingHom (by
        intro P hP
        obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hP
        change Polynomial.aeval Bm (y * (X ^ 3 - C (c : F))) = 0
        rw [map_mul, hroot, mul_zero])
  refine ⟨φ, ?_, ?_⟩
  · intro P
    rfl
  · rw [← AdjoinRoot.mk_X]
    exact Polynomial.aeval_X (A := Matrix (Fin 3) (Fin 3) F) Bm

private lemma phi_injective (h : UnitaryFieldData p f F) (B : unitaryIsom3 h) {c : Fˣ}
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hcube : ∀ b : F, b ^ 3 ≠ (c : F))
    (φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F)
    (hφmk : ∀ P : F[X], φ (AdjoinRoot.mk (X ^ 3 - C (c : F)) P) =
      aeval (((B : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) P) :
    Function.Injective φ := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  intro z w hzw
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective w
  rw [hφmk P, hφmk Q] at hzw
  have hirr : Irreducible (X ^ 3 - C (c : F) : F[X]) := irreducible_cubic hcube
  have hB3 : Bm ^ 3 = algebraMap F (Matrix (Fin 3) (Fin 3) F) (c : F) :=
    coe_B_pow_three h B hB
  have hroot : aeval Bm (X ^ 3 - C (c : F)) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hB3, sub_self]
  have hmon : (X ^ 3 - C (c : F) : F[X]).Monic :=
    monic_X_pow_sub_C (c : F) (by norm_num : (3 : ℕ) ≠ 0)
  have hmin : (X ^ 3 - C (c : F) : F[X]) = minpoly F Bm :=
    minpoly.eq_of_irreducible_of_monic hirr hroot hmon
  have hdvd : (X ^ 3 - C (c : F) : F[X]) ∣ P - Q := by
    rw [hmin]
    exact (minpoly.dvd_iff (A := F) (B := Matrix (Fin 3) (Fin 3) F) (x := Bm)).mpr (by
      rw [map_sub, hzw, sub_self])
  have hzero : AdjoinRoot.mk (X ^ 3 - C (c : F)) (P - Q) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr hdvd
  rw [map_sub] at hzero
  exact sub_eq_zero.mp hzero

private lemma star_phi (h : UnitaryFieldData p f F) {c : Fˣ} {Bm : Matrix (Fin 3) (Fin 3) F}
    {φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F}
    (hφmk : ∀ P : F[X], φ (AdjoinRoot.mk (X ^ 3 - C (c : F)) P) = aeval Bm P)
    (hstarB : (((Bm.map h.bar)ᵀ)) = Bm ^ (p ^ (3 * f))) (z : AdjoinRoot (X ^ 3 - C (c : F))) :
    (((φ z).map h.bar)ᵀ) = φ (z ^ (p ^ (3 * f))) := by
  induction z using AdjoinRoot.induction_on with
  | ih P =>
      rw [hφmk P, map_pow, hφmk P, star_aeval h Bm P, hstarB, pow_aeval h Bm P]

private lemma card_units_cubicField (h : UnitaryFieldData p f F) (c : Fˣ)
    (hcube : ∀ b : F, b ^ 3 ≠ (c : F)) :
    Nat.card (AdjoinRoot (X ^ 3 - C (c : F)))ˣ = (p ^ f) ^ 6 - 1 := by
  haveI : Fact (Irreducible (X ^ 3 - C (c : F) : F[X])) := ⟨irreducible_cubic hcube⟩
  haveI : Field (AdjoinRoot (X ^ 3 - C (c : F))) := inferInstance
  rw [Nat.card_units, card_cubicField h c]

private lemma r_dvd_card_units (h : UnitaryFieldData p f F) (c : Fˣ)
    (hcube : ∀ b : F, b ^ 3 ≠ (c : F)) {r : ℕ}
    (hrd : r ∣ (p ^ f) ^ 2 - p ^ f + 1) : r ∣ Nat.card (AdjoinRoot (X ^ 3 - C (c : F)))ˣ := by
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have hq1' : 1 ≤ (p ^ f) ^ 3 := Nat.one_le_pow _ _ hq1
  have hq6 : (p ^ f) ^ 6 - 1 = ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 3 + 1) := by
    have h : ((p ^ f) ^ 3) ^ 2 = (p ^ f) ^ 6 := by ring
    have e : ((p ^ f) ^ 3) ^ 2 - 1 = ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 3 + 1) := by
      obtain ⟨t, ht⟩ : ∃ t, (p ^ f) ^ 3 = t + 1 := ⟨(p ^ f) ^ 3 - 1, by omega⟩
      rw [ht]
      have hpoly : (t + 1) ^ 2 = 1 + t * (t + 1 + 1) := by ring
      have h2 : (t + 1) ^ 2 - 1 = t * (t + 1 + 1) := by omega
      rw [show t + 1 - 1 = t by omega]
      exact h2
    rw [h] at e
    exact e
  have hq3p1 : r ∣ (p ^ f) ^ 3 + 1 := by
    rw [cube_add_one_factor hq1]
    exact hrd.mul_left (p ^ f + 1)
  rw [card_units_cubicField h c hcube, hq6]
  exact hq3p1.mul_left ((p ^ f) ^ 3 - 1)

private lemma exists_unit_orderOf_eq (h : UnitaryFieldData p f F) (c : Fˣ) {r : ℕ}
    (hr : r.Prime) (hrdvd : r ∣ Nat.card (AdjoinRoot (X ^ 3 - C (c : F)))ˣ) :
    ∃ x : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ, orderOf x = r ∧ x ^ r = 1 ∧ x ≠ 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Finite (AdjoinRoot (X ^ 3 - C (c : F))) :=
    Nat.finite_of_card_ne_zero
      (by rw [card_cubicField h c]; exact pow_ne_zero 6 (pow_ne_zero f h.prime.ne_zero))
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' r hrdvd
  refine ⟨x, hxorder, ?_, ?_⟩
  · rw [← hxorder]
    exact pow_orderOf_eq_one x
  · intro h1
    rw [h1, orderOf_one] at hxorder
    have := hr.one_lt
    omega

private lemma unit_power_q3_add_one (h : UnitaryFieldData p f F) {c : Fˣ} {r : ℕ}
    {x : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ} (hxorder : orderOf x = r)
    (hrd : r ∣ (p ^ f) ^ 2 - p ^ f + 1) :
    (x : AdjoinRoot (X ^ 3 - C (c : F))) ^ (p ^ (3 * f) + 1) = 1 := by
  have hq3eq : (p ^ f) ^ 3 = p ^ (3 * f) := by rw [← pow_mul]; ring_nf
  have h1 : r ∣ (p ^ f) ^ 3 + 1 := by
    rw [cube_add_one_factor (Nat.one_le_pow _ _ h.prime.pos)]
    exact hrd.mul_left (p ^ f + 1)
  have h2 : r ∣ p ^ (3 * f) + 1 := by rwa [hq3eq] at h1
  have h3 : orderOf x ∣ p ^ (3 * f) + 1 := by rw [hxorder]; exact h2
  have h4 : x ^ (p ^ (3 * f) + 1) = 1 := (orderOf_dvd_iff_pow_eq_one).1 h3
  have h5 := congrArg (fun u : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ =>
    (u : AdjoinRoot (X ^ 3 - C (c : F)))) h4
  simpa using h5

private lemma det_eq_one_of_isometry (h : UnitaryFieldData p f F) {r : ℕ} (hr : r.Prime)
    (hrq : ¬ r ∣ p ^ f + 1) {M : Matrix (Fin 3) (Fin 3) F}
    (hMstar : (((M.map h.bar)ᵀ)) * M = 1) (hMpow : M ^ r = 1) : M.det = 1 := by
  have hdetnorm : h.norm M.det = 1 := by
    have h := congrArg Matrix.det hMstar
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_one] at h
    rw [UnitaryFieldData.norm, mul_comm]
    exact h
  have hdetpow : M.det ^ r = 1 := by
    have := congrArg Matrix.det hMpow
    rw [Matrix.det_pow, Matrix.det_one] at this
    exact this
  have hdetq1 : M.det ^ (p ^ f + 1) = 1 := by
    rw [← h.norm_eq_pow]
    exact hdetnorm
  have hcop : r.Coprime (p ^ f + 1) := (Nat.Prime.coprime_iff_not_dvd hr).2 hrq
  have hdvd : orderOf M.det ∣ r.gcd (p ^ f + 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hdetpow)
      ((orderOf_dvd_iff_pow_eq_one).2 hdetq1)
  rw [hcop.gcd_eq_one, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.1 hdvd

private lemma exists_GL_of_matrix (h : UnitaryFieldData p f F) {r : ℕ}
    {M : Matrix (Fin 3) (Fin 3) F} (hMstar : (((M.map h.bar)ᵀ)) * M = 1)
    (hMpow : M ^ r = 1) (hdet1 : M.det = 1) :
    ∃ Gx : GL (Fin 3) F, (Gx : Matrix (Fin 3) (Fin 3) F) = M ∧
      Gx ∈ unitaryIsom3 h ∧ Gx ^ r = 1 := by
  let Gx : GL (Fin 3) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet1]; norm_num)
  have hGxval : (Gx : Matrix (Fin 3) (Fin 3) F) = M :=
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  refine ⟨Gx, hGxval, ?_, ?_⟩
  · rw [mem_unitaryIsom3, hGxval]
    exact hMstar
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hGxval, hMpow, Units.val_one]

private lemma commute_phi_B (h : UnitaryFieldData p f F) (B : unitaryIsom3 h) {c : Fˣ}
    (φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F)
    (x : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ)
    (hφroot : φ (AdjoinRoot.root (X ^ 3 - C (c : F))) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    φ (x : AdjoinRoot (X ^ 3 - C (c : F))) *
        ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        φ (x : AdjoinRoot (X ^ 3 - C (c : F))) := by
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  calc φ (x : AdjoinRoot (X ^ 3 - C (c : F))) * Bm =
        φ (x : AdjoinRoot (X ^ 3 - C (c : F))) *
          φ (AdjoinRoot.root (X ^ 3 - C (c : F))) := by rw [hφroot]
    _ = φ ((x : AdjoinRoot (X ^ 3 - C (c : F))) *
          AdjoinRoot.root (X ^ 3 - C (c : F))) := (map_mul φ _ _).symm
    _ = φ (AdjoinRoot.root (X ^ 3 - C (c : F)) *
          (x : AdjoinRoot (X ^ 3 - C (c : F)))) := by rw [mul_comm]
    _ = φ (AdjoinRoot.root (X ^ 3 - C (c : F))) *
          φ (x : AdjoinRoot (X ^ 3 - C (c : F))) := map_mul φ _ _
    _ = Bm * φ (x : AdjoinRoot (X ^ 3 - C (c : F))) := by rw [hφroot]

private lemma ne_one_of_is_image {c : Fˣ}
    {φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F}
    {x : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ} {Gx : GL (Fin 3) F}
    (hφinj : Function.Injective φ)
    (hGxval : (Gx : Matrix (Fin 3) (Fin 3) F) =
      φ (x : AdjoinRoot (X ^ 3 - C (c : F)))) (hxne : x ≠ 1) : Gx ≠ 1 := by
  intro hGx1
  have hM1 : φ (x : AdjoinRoot (X ^ 3 - C (c : F))) = 1 := by
    rw [← hGxval, hGx1]
    rfl
  have hx1 : x = 1 := by
    apply Units.ext
    apply hφinj
    rw [hM1]
    exact (map_one φ).symm
  exact hxne hx1

private lemma exists_fixed_element (h : UnitaryFieldData p f F) (B : unitaryIsom3 h)
    {r : ℕ} (hr : r.Prime) {c : Fˣ} (Gx : GL (Fin 3) F)
    (hGxmem : Gx ∈ unitaryIsom3 h)
    (hGxdet : (Gx : Matrix (Fin 3) (Fin 3) F).det = 1) (hGxpow : Gx ^ r = 1)
    {φ : AdjoinRoot (X ^ 3 - C (c : F)) →+* Matrix (Fin 3) (Fin 3) F}
    {x : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ}
    (hGxval : (Gx : Matrix (Fin 3) (Fin 3) F) =
      φ (x : AdjoinRoot (X ^ 3 - C (c : F))))
    (hφroot : φ (AdjoinRoot.root (X ^ 3 - C (c : F))) =
      ((B : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hφinj : Function.Injective φ) (hxne : x ≠ 1) :
    ∃ y : unitarySU p f F 3, suConj h B y = y ∧ orderOf y = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  have hMcomm := commute_phi_B h B φ x hφroot
  have hcomm : Gx * (B : GL (Fin 3) F) = (B : GL (Fin 3) F) * Gx := by
    apply Units.ext
    change (Gx : Matrix (Fin 3) (Fin 3) F) * Bm =
      Bm * (Gx : Matrix (Fin 3) (Fin 3) F)
    rw [hGxval]
    exact hMcomm
  have hne := ne_one_of_is_image hφinj hGxval hxne
  let y : unitarySU p f F 3 := ⟨Gx, by
    rw [mem_unitarySU_iff h]
    exact ⟨hGxdet, hGxmem⟩⟩
  have hfix : suConj h B y = y := by
    apply Subtype.ext
    rw [coe_suConj]
    have hyGL : (y : GL (Fin 3) F) = Gx := rfl
    rw [hyGL, ← hcomm, mul_assoc]
    simp [Subgroup.coe_inv]
  have hypow : y ^ r = 1 := Subtype.ext hGxpow
  have hyne : y ≠ 1 := fun h1 => hne (congrArg Subtype.val h1)
  exact ⟨y, hfix, orderOf_eq_prime hypow hyne⟩

theorem fixesTorusPrime_of_not_cube {p f : ℕ} {F : Type} [Field F]
    (h : UnitaryFieldData p f F) (hq : 2 < p ^ f) (h3 : 3 ∣ p ^ f + 1) (B : unitaryIsom3 h)
    {c : Fˣ} (hc : h.norm (c : F) = 1)
    (hB : (B : GL (Fin 3) F) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    (hcube : ∀ b : F, b ^ 3 ≠ (c : F)) : FixesTorusPrime (p ^ f) (suConj h B) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨r, hrp, hrne3, hrd, hqadd, hprod⟩ := exists_torusPrime hq h3
  haveI : Fact r.Prime := ⟨hrp⟩
  let Bm : Matrix (Fin 3) (Fin 3) F := (B : GL (Fin 3) F)
  obtain ⟨φ, hφmk, hφroot⟩ := exists_phi h B hB hcube
  have hφinj := phi_injective h B hB hcube φ hφmk
  have hstarB := star_coe_B_eq_pow h h3 B hc hB
  have hstarphi := star_phi h hφmk hstarB
  have hcardE := card_cubicField h c
  haveI : Finite (AdjoinRoot (X ^ 3 - C (c : F))) :=
    Nat.finite_of_card_ne_zero (by rw [hcardE]; positivity)
  have hcard_units := card_units_cubicField h c hcube
  have hrdvdE := r_dvd_card_units h c hcube hrd
  obtain ⟨x, hxorder, hxpow, hxne⟩ := exists_unit_orderOf_eq h c hrp hrdvdE
  have hxE_r : (x : AdjoinRoot (X ^ 3 - C (c : F))) ^ r = 1 := by
    have h := congrArg (fun u : (AdjoinRoot (X ^ 3 - C (c : F)))ˣ =>
      (u : AdjoinRoot (X ^ 3 - C (c : F)))) hxpow
    simpa using h
  have hxE := unit_power_q3_add_one h hxorder hrd
  have hxstar : (((φ (x : AdjoinRoot (X ^ 3 - C (c : F)))).map h.bar)ᵀ) *
      φ (x : AdjoinRoot (X ^ 3 - C (c : F))) = 1 := by
    rw [hstarphi (x : AdjoinRoot (X ^ 3 - C (c : F))), ← map_mul, ← pow_succ, hxE, map_one]
  have hMpow : (φ (x : AdjoinRoot (X ^ 3 - C (c : F)))) ^ r = 1 := by
    rw [← map_pow, hxE_r, map_one]
  have hdet1 := det_eq_one_of_isometry h hrp hqadd hxstar hMpow
  obtain ⟨Gx, hGxval, hGxmem, hGxpow⟩ := exists_GL_of_matrix h hxstar hMpow hdet1
  have hGxdet : (Gx : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [hGxval, hdet1]
  obtain ⟨y, hfix, hyorder⟩ :=
    exists_fixed_element h B hrp Gx hGxmem hGxdet hGxpow hGxval hφroot hφinj hxne
  refine ⟨y, hfix, r, hrp, hrne3, ?_, hyorder⟩
  exact hprod

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CentralLift
