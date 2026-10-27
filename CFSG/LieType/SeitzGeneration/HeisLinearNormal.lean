module

public import CFSG.LieType.SeitzGeneration.HeisLinearDefs
public import CFSG.LieType.SeitzGeneration.NonabLift
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.LieType.SeitzGeneration

open Module Matrix
open scoped commutatorElement

section Charpoly

open Polynomial

variable {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]

theorem charpoly_smul_eq (A : Matrix n n F) {c : F} (hc : c ≠ 0) :
    (c • A).charpoly = C (c ^ Fintype.card n) * A.charpoly.comp (C c⁻¹ * X) := by
  have h : charmatrix (c • A) =
      C c • (Polynomial.compRingHom (C c⁻¹ * X)).mapMatrix (charmatrix A) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [charmatrix_apply_eq, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
        coe_compRingHom_apply, smul_eq_mul, sub_comp, X_comp, C_comp]
      rw [mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul, ← C_mul]
    · simp only [charmatrix_apply_ne _ _ _ hij, Matrix.smul_apply, RingHom.mapMatrix_apply,
        Matrix.map_apply, coe_compRingHom_apply, smul_eq_mul, neg_comp, C_comp]
      rw [mul_neg, ← C_mul, ← C_neg]
  rw [charpoly, h, det_smul, ← RingHom.map_det]
  simp [charpoly]

theorem coeff_charpoly_smul (A : Matrix n n F) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (c • A).charpoly.coeff k * c ^ k = c ^ Fintype.card n * A.charpoly.coeff k := by
  rw [charpoly_smul_eq A hc, coeff_C_mul, comp_C_mul_X_coeff, inv_pow]
  field_simp

theorem charpoly_eq_pow_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : F}
    (hc : IsPrimitiveRoot c p) {A : Matrix (Fin p) (Fin p) F} (hdet : A.det = 1)
    (hch : (c • A).charpoly = A.charpoly) : A.charpoly = X ^ p - 1 := by
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := hc.ne_zero hp.ne_zero
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hdeg : A.charpoly.natDegree = p := by
    simpa using Matrix.charpoly_natDegree_eq_dim A
  refine Polynomial.ext fun k => ?_
  rcases lt_trichotomy k p with hk | rfl | hk
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h1 := Matrix.det_eq_sign_charpoly_coeff A
      rw [hdet, Fintype.card_fin, hodd.neg_one_pow] at h1
      simp only [coeff_sub, coeff_X_pow, coeff_one, if_neg hp.ne_zero.symm, if_true]
      linear_combination h1
    · have h1 := coeff_charpoly_smul A hc0 k
      rw [hch, Fintype.card_fin, hc.pow_eq_one, one_mul] at h1
      have h2 : A.charpoly.coeff k * (c ^ k - 1) = 0 := by linear_combination h1
      have h3 : c ^ k - 1 ≠ 0 := sub_ne_zero.2 (hc.pow_ne_one_of_pos_of_lt hk0.ne' hk)
      rw [(mul_eq_zero.1 h2).resolve_right h3]
      simp [coeff_sub, coeff_X_pow, coeff_one, hk.ne, hk0.ne']
  · have h1 := (Matrix.charpoly_monic A).coeff_natDegree
    rw [hdeg] at h1
    rw [h1]
    simp [coeff_sub, coeff_X_pow, coeff_one, hp.ne_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)]
    simp [coeff_sub, coeff_X_pow, coeff_one, hk.ne', (hp.pos.trans hk).ne']

theorem pow_eq_one_of_mul_eq_smul_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : F}
    (hc : IsPrimitiveRoot c p) {A B B' : Matrix (Fin p) (Fin p) F} (hdet : A.det = 1)
    (hBB' : B * B' = 1) (hB'B : B' * B = 1) (h : B * A = c • (A * B)) : A ^ p = 1 := by
  have h1 : c • A = (B * A) * B' := by
    rw [h, Matrix.smul_mul, Matrix.mul_assoc, hBB', Matrix.mul_one]
  have hch : (c • A).charpoly = A.charpoly := by
    rw [h1, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hB'B, Matrix.one_mul]
  have hCH := Matrix.aeval_self_charpoly A
  rw [charpoly_eq_pow_sub_one hp2 hc hdet hch] at hCH
  simpa [sub_eq_zero] using hCH

theorem pow_eq_one_of_quasi_commute {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {c : F}
    (hc : IsPrimitiveRoot c p) {a b : SpecialLinearGroup (Fin p) F}
    (h : (b : Matrix (Fin p) (Fin p) F) * a = c • ((a : Matrix (Fin p) (Fin p) F) * b)) :
    a ^ p = 1 := by
  have hbb : (b : Matrix (Fin p) (Fin p) F) * ((b⁻¹ : SpecialLinearGroup (Fin p) F) :
      Matrix (Fin p) (Fin p) F) = 1 := by
    have h1 := congrArg Subtype.val (mul_inv_cancel b)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hbb' : ((b⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) *
      (b : Matrix (Fin p) (Fin p) F) = 1 := by
    have h1 := congrArg Subtype.val (inv_mul_cancel b)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact pow_eq_one_of_mul_eq_smul_mul hp2 hc a.2 hbb hbb' h

end Charpoly

section Basis

variable {F : Type*} [Field F]

theorem exists_orbit_basis {p : ℕ} [Fact p.Prime] {ω ξ : F} (hω : IsPrimitiveRoot ω p)
    (hξ : ξ ≠ 0) {Y A : Matrix (Fin p) (Fin p) F} (hA : A.det = 1)
    (hrel : Y * A = ω • (A * Y)) {v : Fin p → F} (hv : v ≠ 0) (hYv : Y.mulVec v = ξ • v) :
    ∃ b : Basis (Fin p) F (Fin p → F), (∀ k : Fin p, b k = (A ^ (k : ℕ)).mulVec v) ∧
      ∀ k : Fin p, Y.mulVec (b k) = (ξ * ω ^ (k : ℕ)) • b k := by
  have hYA : ∀ k : ℕ, Y * A ^ k = ω ^ k • (A ^ k * Y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Y * A ^ (k + 1) = (Y * A ^ k) * A := by rw [pow_succ, Matrix.mul_assoc]
        _ = ω ^ k • (A ^ k * (Y * A)) := by
          rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
        _ = ω ^ (k + 1) • (A ^ (k + 1) * Y) := by
          rw [hrel, Matrix.mul_smul, smul_smul, pow_succ ω k, pow_succ A k, mul_comm (ω ^ k) ω,
            Matrix.mul_assoc]
  let u : Fin p → (Fin p → F) := fun k => (A ^ (k : ℕ)).mulVec v
  have hYu : ∀ k : Fin p, Y.mulVec (u k) = (ξ * ω ^ (k : ℕ)) • u k := by
    intro k
    simp only [u]
    rw [Matrix.mulVec_mulVec, hYA, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_smul, smul_smul, mul_comm]
  have hu0 : ∀ k : Fin p, u k ≠ 0 := by
    intro k hk
    have hdet : (A ^ (k : ℕ)).det = 1 := by rw [Matrix.det_pow, hA, one_pow]
    have h1 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, hk⟩
    rw [hdet] at h1
    exact one_ne_zero h1
  have hinj : Function.Injective (fun k : Fin p => ξ * ω ^ (k : ℕ)) := by
    intro k l h
    have h' : ω ^ (k : ℕ) = ω ^ (l : ℕ) := mul_left_cancel₀ hξ h
    exact Fin.ext (hω.pow_inj k.2 l.2 h')
  have hli : LinearIndependent F u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y)
      (fun k : Fin p => ξ * ω ^ (k : ℕ)) hinj u
      (fun k => ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hYu k, hu0 k⟩)
  let b : Basis (Fin p) F (Fin p → F) :=
    basisOfLinearIndependentOfCardEqFinrank' u hli (by simp)
  have hb : ∀ k, b k = u k := fun k => by simp [b]
  exact ⟨b, hb, fun k => by rw [hb]; exact hYu k⟩

theorem mul_basisUnit_eq_of_mulVec {m : ℕ} (b : Basis (Fin m) F (Fin m → F))
    {M N : Matrix (Fin m) (Fin m) F}
    (h : ∀ k, M.mulVec (b k) =
      (basisUnit b : Matrix (Fin m) (Fin m) F).mulVec (N.mulVec (Pi.single k 1))) :
    M * (basisUnit b : Matrix (Fin m) (Fin m) F) =
      (basisUnit b : Matrix (Fin m) (Fin m) F) * N := by
  ext a k
  have h1 : ∀ X : Matrix (Fin m) (Fin m) F, X.mulVec (Pi.single k 1) a = X a k := fun X => by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [← h1 (M * (basisUnit b : Matrix (Fin m) (Fin m) F)),
    ← h1 ((basisUnit b : Matrix (Fin m) (Fin m) F) * N), ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, basisUnit_mulVec_single, one_smul, h]

theorem units_inv_mul_mul_eq_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] (P : GL n F)
    {M N : Matrix n n F} (h : M * (P : Matrix n n F) = (P : Matrix n n F) * N) :
    ((P⁻¹ : GL n F) : Matrix n n F) * M * (P : Matrix n n F) = N := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

theorem smul_heisDiagMat_mulVec_single {p : ℕ} (ω ξ : F) (k : Fin p) :
    (ξ • heisDiagMat ω).mulVec (Pi.single k 1) = Pi.single k (ξ * ω ^ (k : ℕ)) := by
  ext i
  by_cases h : i = k
  · subst h
    simp [heisDiagMat, Matrix.mulVec_diagonal]
  · simp [heisDiagMat, Matrix.mulVec_diagonal, h]

theorem heisShiftMat_mulVec_single {p : ℕ} (k : Fin p) :
    (heisShiftMat F p).mulVec (Pi.single k 1) = Pi.single ((finRotate p).symm k) 1 := by
  rw [heisShiftMat, Matrix.permMatrix_mulVec]
  ext i
  simp only [Function.comp_apply, Pi.single_apply, Equiv.eq_symm_apply]

private theorem val_finRotate_eq_mod {p : ℕ} (hp : 0 < p) (i : Fin p) :
    ((finRotate p i : Fin p) : ℕ) = ((i : ℕ) + 1) % p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

end Basis

theorem exists_heisenberg_basis_p {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) {x y : SpecialLinearGroup (Fin p) F}
    (hyx : ⁅y, x⁆ ∈ Subgroup.center (SpecialLinearGroup (Fin p) F)) (hne : x * y ≠ y * x) :
    ∃ (P : GL (Fin p) F) (ω ξ : F), IsPrimitiveRoot ω p ∧ ξ ^ p = 1 ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (y : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = ξ • heisDiagMat ω ∧
      ((P⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (x : Matrix (Fin p) (Fin p) F) *
        (P : Matrix (Fin p) (Fin p) F) = heisShiftMat F p := by
  classical
  have hp : p.Prime := Fact.out
  set X : Matrix (Fin p) (Fin p) F := (x : Matrix (Fin p) (Fin p) F)
  set Y : Matrix (Fin p) (Fin p) F := (y : Matrix (Fin p) (Fin p) F) with hY
  set A : Matrix (Fin p) (Fin p) F :=
    ((x⁻¹ : SpecialLinearGroup (Fin p) F) : Matrix (Fin p) (Fin p) F) with hA
  obtain ⟨ω₀, hω₀0, hω₀⟩ := exists_scalar_of_mem_center (n := p) hp.pos hyx
  have hω₀1 : ω₀ ≠ 1 := by
    intro h
    apply hne
    have h1 : ⁅y, x⁆ = 1 := Subtype.ext (by rw [hω₀, h, one_smul]; rfl)
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hω₀p : ω₀ ^ p = 1 := by
    have h1 := (⁅y, x⁆ : SpecialLinearGroup (Fin p) F).2
    rw [hω₀, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact h1
  have hprim₀ : IsPrimitiveRoot ω₀ p := by
    rw [← orderOf_eq_prime hω₀p hω₀1]
    exact IsPrimitiveRoot.orderOf ω₀
  have hrel : Y * X = ω₀ • (X * Y) := by
    have h1 : (⁅y, x⁆ : SpecialLinearGroup (Fin p) F) * (x * y) = y * x := by
      simp only [commutatorElement_def]; group
    have h2 := congrArg Subtype.val h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hω₀,
      Matrix.smul_mul, Matrix.one_mul] at h2
    exact h2.symm
  have hrelinv : X * Y = ω₀⁻¹ • (Y * X) := by
    rw [hrel, smul_smul, inv_mul_cancel₀ hω₀0, one_smul]
  have hxp : x ^ p = 1 := pow_eq_one_of_quasi_commute hp2 hprim₀ hrel
  have hyp : y ^ p = 1 := pow_eq_one_of_quasi_commute hp2 hprim₀.inv hrelinv
  have hYp : Y ^ p = 1 := by
    rw [hY, ← Matrix.SpecialLinearGroup.coe_pow, hyp, Matrix.SpecialLinearGroup.coe_one]
  have hAp : A ^ p = 1 := by
    rw [hA, ← Matrix.SpecialLinearGroup.coe_pow, inv_pow, hxp, inv_one,
      Matrix.SpecialLinearGroup.coe_one]
  have hXA : X * A = 1 := by
    have h1 := congrArg Subtype.val (mul_inv_cancel x)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hAX : A * X = 1 := by
    have h1 := congrArg Subtype.val (inv_mul_cancel x)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h1
  have hrelA : Y * A = ω₀⁻¹ • (A * Y) := by
    have h1 : A * (Y * X) * A = A * (ω₀ • (X * Y)) * A := by rw [hrel]
    have e1 : A * (Y * X) * A = A * Y := by
      calc A * (Y * X) * A = A * Y * (X * A) := by simp only [Matrix.mul_assoc]
        _ = A * Y := by rw [hXA, Matrix.mul_one]
    have e2 : A * (ω₀ • (X * Y)) * A = ω₀ • (Y * A) := by
      calc A * (ω₀ • (X * Y)) * A = ω₀ • ((A * X) * (Y * A)) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
        _ = ω₀ • (Y * A) := by rw [hAX, Matrix.one_mul]
    rw [e1, e2] at h1
    rw [h1, smul_smul, inv_mul_cancel₀ hω₀0, one_smul]
  obtain ⟨ξ, v, hξp, hv0, hYv⟩ :=
    exists_eigenvector_of_pow_eq_one (p := p) hp.pos hζ hp.pos hYp
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp [hp.ne_zero] at hξp
  have hAdet : A.det = 1 := (x⁻¹ : SpecialLinearGroup (Fin p) F).2
  obtain ⟨b, hb, hYb⟩ := exists_orbit_basis hprim₀.inv hξ0 hAdet hrelA hv0 hYv
  have hAb : ∀ m : Fin p, A.mulVec (b m) = b (finRotate p m) := by
    intro m
    rw [hb m, hb (finRotate p m), Matrix.mulVec_mulVec, ← pow_succ', val_finRotate_eq_mod hp.pos,
      ← pow_eq_pow_mod _ hAp]
  have hXb : ∀ k : Fin p, X.mulVec (b k) = b ((finRotate p).symm k) := by
    intro k
    have h1 : b k = A.mulVec (b ((finRotate p).symm k)) := by
      rw [hAb, Equiv.apply_symm_apply]
    rw [h1, Matrix.mulVec_mulVec, hXA, Matrix.one_mulVec]
  refine ⟨basisUnit b, ω₀⁻¹, ξ, hprim₀.inv, hξp, ?_, ?_⟩
  · refine units_inv_mul_mul_eq_of_mul_eq _ (mul_basisUnit_eq_of_mulVec b fun k => ?_)
    rw [smul_heisDiagMat_mulVec_single, basisUnit_mulVec_single, hYb k]
  · refine units_inv_mul_mul_eq_of_mul_eq _ (mul_basisUnit_eq_of_mulVec b fun k => ?_)
    rw [heisShiftMat_mulVec_single, basisUnit_mulVec_single, one_smul, hXb k]

end CFSG.LieType.SeitzGeneration
