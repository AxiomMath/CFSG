module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.ConjugacyNonsplit

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization

section Matrices

variable {F : Type} [Field F]

theorem minusIdentity_val :
    (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F : Matrix (Fin 2) (Fin 2) F) = -1 := by
  rw [CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem matrix_eq_one_or_neg_of_mul_self (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2) (Fin 2) F}
    (hdet : X.det = 1) (hM : X * X = 1) : X = 1 ∨ X = -1 := by
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  rw [Matrix.det_fin_two] at hdet
  have hsum : X 0 0 + X 1 1 ≠ 0 := by
    intro hs
    have hd : X 1 1 = -X 0 0 := by linear_combination hs
    apply h2
    rw [hd] at hdet
    linear_combination -h00 - hdet
  have hb0 : X 0 1 = 0 := by
    have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hsum
  have hc0 : X 1 0 = 0 := by
    have : X 1 0 * (X 0 0 + X 1 1) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hsum
  rw [hb0, hc0] at hdet h00
  have ha : X 0 0 * X 0 0 = 1 := by linear_combination h00
  have hda : X 1 1 = X 0 0 := by
    have : X 0 0 * (X 1 1 - X 0 0) = 0 := by linear_combination hdet - ha
    rcases mul_eq_zero.mp this with h | h
    · rw [h, zero_mul] at ha
      exact absurd ha zero_ne_one
    · linear_combination h
  rcases mul_self_eq_one_iff.mp ha with h1 | h1
  · left
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using hb0
    · simpa using hc0
    · simpa using hda.trans h1
  · right
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using h1
    · simpa using hb0
    · simpa using hc0
    · simpa using hda.trans h1

theorem SL2_eq_one_or_neg_of_mul_self (h2 : (2 : F) ≠ 0) {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * X = 1) : X = 1 ∨ X = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F := by
  have hM : (X : Matrix (Fin 2) (Fin 2) F) * X = 1 := by
    rw [← SL_mul_val, hX, SL_one_val]
  rcases matrix_eq_one_or_neg_of_mul_self h2 X.2 hM with h | h
  · exact Or.inl (SL_eq_of_val F (h.trans (SL_one_val F).symm))
  · right
    apply SL_eq_of_val
    rw [h, minusIdentity_val]

theorem exists_conj_weyl_matrix (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 2) (Fin 2) F}
    (htr : X.trace = 0) (hdet : X.det = 1) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧ X * P = P * !![0, -1; 1, 0] := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have hX : X = !![X 0 0, X 0 1; X 1 0, -X 0 0] := by
    rw [← hd]
    exact Matrix.eta_fin_two X
  rw [hd] at hdet
  set a := X 0 0
  set b' := X 0 1
  set c := X 1 0
  rw [hX]
  by_cases hc : c = 0
  · by_cases hb : b' = 0
    ·
      rw [hb, hc] at hdet
      have ha : a ≠ 0 := by
        intro h0
        rw [h0] at hdet
        simp at hdet
      refine ⟨!![1, a; 1, -a], ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        intro h0
        apply ha
        have : 2 * a = 0 := by linear_combination -h0
        exact (mul_eq_zero.mp this).resolve_left h2
      · rw [hb, hc]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hdet | linear_combination -hdet
    ·
      rw [hc] at hdet
      refine ⟨!![0, b'; 1, -a], ?_, ?_⟩
      · rw [Matrix.det_fin_two_of]
        intro h0
        apply hb
        linear_combination -h0
      · rw [hc]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hdet | linear_combination -hdet
  ·
    refine ⟨!![1, a; 0, c], ?_, ?_⟩
    · rw [Matrix.det_fin_two_of]
      simpa using hc
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hdet | linear_combination -hdet

theorem trace_eq_zero_of_mul_self_eq_neg (X : SpecialLinearGroup (Fin 2) F)
    (hX : X * X = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    (X : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
  have hM : (X : Matrix (Fin 2) (Fin 2) F) * X = -1 := by
    rw [← SL_mul_val, hX, minusIdentity_val]
  have hCH := cayley_hamilton_two (X : Matrix (Fin 2) (Fin 2) F)
  rw [hM, X.2, one_smul] at hCH
  have hzero : (X : Matrix (Fin 2) (Fin 2) F).trace • (X : Matrix (Fin 2) (Fin 2) F) = 0 := by
    rw [eq_sub_iff_add_eq] at hCH
    rw [← hCH, neg_add_cancel]
  by_contra htr
  have hX0 : (X : Matrix (Fin 2) (Fin 2) F) = 0 := by
    have := congrArg (fun M => (X : Matrix (Fin 2) (Fin 2) F).trace⁻¹ • M) hzero
    simpa [smul_smul, inv_mul_cancel₀ htr] using this
  have hdet := X.2
  rw [hX0, Matrix.det_fin_two] at hdet
  simp at hdet

theorem exists_conj_weyl (h2 : (2 : F) ≠ 0) {X : SpecialLinearGroup (Fin 2) F}
    (hX : X * X = CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) :
    ∃ Q : GL (Fin 2) F, Q * SpecialLinearGroup.toGL X * Q⁻¹ = SpecialLinearGroup.toGL (weyl F) := by
  obtain ⟨P, hP, hXP⟩ := exists_conj_weyl_matrix h2 (trace_eq_zero_of_mul_self_eq_neg X hX) X.2
  let P' : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero P hP
  refine ⟨P'⁻¹, ?_⟩
  rw [inv_inv]
  apply Units.ext
  have hP' : (P' : Matrix (Fin 2) (Fin 2) F) = P := rfl
  have hXP' : SpecialLinearGroup.toGL X * P' = P' * SpecialLinearGroup.toGL (weyl F) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hP']
    exact hXP
  rw [mul_assoc, hXP', ← mul_assoc, inv_mul_cancel, one_mul]

end Matrices

section Residues

theorem zmod_eq_zero_or_half {m : ℕ} (hm : 0 < m) (heven : Even m) {t : ZMod m}
    (ht : t + t = 0) : t = 0 ∨ t = ((m / 2 : ℕ) : ZMod m) := by
  have : NeZero m := ⟨hm.ne'⟩
  have hlt := ZMod.val_lt t
  have hval : (t + t).val = (t.val + t.val) % m := ZMod.val_add t t
  rw [ht, ZMod.val_zero] at hval
  obtain ⟨k, hk⟩ := heven
  obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hval.symm
  have hcases : t.val = 0 ∨ t.val = m / 2 := by
    rcases c with _ | _ | c
    · omega
    · omega
    · have : m * 2 ≤ m * (c + 1 + 1) := Nat.mul_le_mul_left m (by omega)
      omega
  rcases hcases with h | h
  · left
    rw [← ZMod.natCast_zmod_val t, h, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val t, h]

end Residues

section Quadratic

theorem exists_quadratic_extension (F : Type) [Field F] [Fintype F] (b : Fˣ)
    (hb : ¬ IsSquare b) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E), Nonempty (Module.Basis (Fin 2) F E) := by
  set f : Polynomial F := Polynomial.X ^ 2 - Polynomial.C (b : F) with hf
  have hirr : Irreducible f := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro c hc
    apply hb
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hc
      exact b.ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_mul, Units.val_mk0, ← hc, sq])⟩
  have : Fact (Irreducible f) := ⟨hirr⟩
  have hf0 : f ≠ 0 := hirr.ne_zero
  set pb := AdjoinRoot.powerBasis hf0 with hpb
  have hdim : pb.dim = 2 := by
    rw [hpb, AdjoinRoot.powerBasis_dim, hf, Polynomial.natDegree_X_pow_sub_C]
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, ⟨pb.basis.reindex (finCongr hdim)⟩⟩

end Quadratic

end CFSG.Wreathed.CentralSL2
