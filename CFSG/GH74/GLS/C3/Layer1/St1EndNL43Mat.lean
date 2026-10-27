module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.GH74.GLS.C3.Layer1.EndN.L43

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def cmatrix : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  !![0, 0, 0, 2; 1, 0, 0, 2; 0, 1, 0, 2; 0, 0, 1, 2]

theorem det_cmatrix : cmatrix.det = 1 := by decide +kernel

@[expose] def cmat : Matrix.SpecialLinearGroup (Fin 4) (ZMod 3) := ⟨cmatrix, det_cmatrix⟩

@[expose] def zStar : projectiveSL 4 (ZMod 3) := proj 4 (ZMod 3) cmat

namespace Mat

abbrev M4 := Matrix (Fin 4) (Fin 4) (ZMod 3)

abbrev SL4 := Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)

abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)

theorem scalar_eq_smul (c : ZMod 3) : scalar (Fin 4) c = c • (1 : M4) := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem mem_scalars_iff (a : SL4) :
    a ∈ scalars 4 (ZMod 3) ↔ (a : M4) = 1 ∨ (a : M4) = (2 : ZMod 3) • (1 : M4) := by
  rw [mem_scalars]
  constructor
  · rintro ⟨c, -, hc⟩
    have hc' : ∀ c : (ZMod 3)ˣ, (c : ZMod 3) = 1 ∨ (c : ZMod 3) = 2 := by decide
    rw [scalar_eq_smul] at hc
    rcases hc' c with h | h
    · left
      rw [hc, h, one_smul]
    · right
      rw [hc, h]
  · rintro (h | h)
    · exact ⟨1, one_pow _, by rw [h, Units.val_one, scalar_eq_smul, one_smul]⟩
    · refine ⟨⟨2, 2, by decide, by decide⟩, by decide, ?_⟩
      rw [h, scalar_eq_smul]

theorem proj_eq_one_iff' (a : SL4) :
    proj 4 (ZMod 3) a = 1 ↔ (a : M4) = 1 ∨ (a : M4) = (2 : ZMod 3) • (1 : M4) := by
  rw [proj_eq_one_iff, mem_scalars_iff]

theorem inv_mul_eq_iff (a : SL4) (x y : M4) :
    ((a⁻¹ : SL4) : M4) * x = y ↔ x = (a : M4) * y := by
  have h1 : (a : M4) * ((a⁻¹ : SL4) : M4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    rfl
  have h2 : ((a⁻¹ : SL4) : M4) * (a : M4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    rfl
  constructor
  · intro h
    rw [← h, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  · intro h
    rw [h, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem proj_eq_iff (a b : SL4) :
    proj 4 (ZMod 3) a = proj 4 (ZMod 3) b ↔
      (b : M4) = a ∨ (b : M4) = (2 : ZMod 3) • (a : M4) := by
  rw [proj_eq_proj_iff, mem_scalars_iff, Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_eq_iff, inv_mul_eq_iff]
  simp

theorem conj_eq_iff (A : GL4) (x y : M4) :
    (A : M4) * x * ((A⁻¹ : GL4) : M4) = y ↔ (A : M4) * x = y * (A : M4) := by
  have h1 : ((A⁻¹ : GL4) : M4) * (A : M4) = 1 := Units.inv_mul A
  have h2 : (A : M4) * ((A⁻¹ : GL4) : M4) = 1 := Units.mul_inv A
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro h
    rw [h, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem conj_proj_iff (A : GL4) (x y : SL4) :
    proj 4 (ZMod 3) y = conjAut 4 (ZMod 3) A (proj 4 (ZMod 3) x) ↔
      ∃ c : ZMod 3, (c = 1 ∨ c = 2) ∧ (A : M4) * x = c • ((y : M4) * A) := by
  rw [conjAut_proj, proj_eq_iff, coe_slConjugation, conj_eq_iff, conj_eq_iff]
  constructor
  · rintro (h | h)
    · exact ⟨1, Or.inl rfl, by rw [one_smul]; exact h⟩
    · exact ⟨2, Or.inr rfl, by rw [← Matrix.smul_mul]; exact h⟩
  · rintro ⟨c, hc | hc, h⟩
    · left
      subst hc
      rwa [one_smul] at h
    · right
      subst hc
      rwa [← Matrix.smul_mul] at h

theorem dual_proj_iff (A : GL4) (x y : SL4) :
    proj 4 (ZMod 3) y = conjAut 4 (ZMod 3) A (dualAut 4 (ZMod 3) (proj 4 (ZMod 3) x)) ↔
      ∃ c : ZMod 3, (c = 1 ∨ c = 2) ∧
        (A : M4) * (x : M4).adjugate.transpose = c • ((y : M4) * A) := by
  rw [dualAut_proj, conj_proj_iff]
  simp only [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]

theorem aut_form (α : MulAut (projectiveSL 4 (ZMod 3))) :
    ∃ (A : GL4) (ε : ℕ), ε ≤ 1 ∧ α = conjAut 4 (ZMod 3) A * dualAut 4 (ZMod 3) ^ ε := by
  obtain ⟨A, σ, ε, hε, h⟩ := (automorphism_generation (K := ZMod 3) (n := 4) (by norm_num)).2 α
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  exact ⟨A, ε, hε, by rw [h, map_one, mul_one]⟩

theorem scalar_of_conj (N : GL4) (h : conjAut 4 (ZMod 3) N = 1) :
    ∃ c : ZMod 3, (N : M4) = c • (1 : M4) := by
  have hcomm : Pairwise fun i j : Fin 4 =>
      Commute (Matrix.single i j (1 : ZMod 3)) (N : M4) := by
    intro i j hij
    set t : SL4 := Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 3) with ht
    have ht' : (t : M4) = 1 + Matrix.single i j (1 : ZMod 3) :=
      Matrix.SpecialLinearGroup.transvection_coe hij 1
    have h1 : proj 4 (ZMod 3) t = conjAut 4 (ZMod 3) N (proj 4 (ZMod 3) t) := by
      rw [h]
      rfl
    rw [conjAut_proj, proj_eq_iff, coe_slConjugation] at h1
    rcases h1 with h1 | h1
    · rw [conj_eq_iff, ht'] at h1
      have h2 : (N : M4) * Matrix.single i j (1 : ZMod 3) =
          Matrix.single i j (1 : ZMod 3) * N := by
        simpa [Matrix.mul_add, Matrix.add_mul] using h1
      exact h2.symm
    · exfalso
      have htr := Matrix.trace_units_conj N (t : M4)
      rw [h1, Matrix.trace_smul, ht', Matrix.trace_add, Matrix.trace_one,
        Matrix.trace_single_eq_of_ne i j 1 hij] at htr
      revert htr
      decide
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  exact ⟨c, by rw [← hc, scalar_eq_smul]⟩

theorem trace_eq_of_mul (A : GL4) (c : ZMod 3) (X Y : M4)
    (h : (A : M4) * X = c • (Y * (A : M4))) : Matrix.trace X = c * Matrix.trace Y := by
  have h1 : ((A⁻¹ : GL4) : M4) * ((A : M4) * X) =
      ((A⁻¹ : GL4) : M4) * (c • (Y * (A : M4))) := by
    rw [h]
  rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc] at h1
  rw [h1, Matrix.trace_smul, Matrix.trace_units_conj' A Y]
  rfl

@[expose] def Cx (w : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![2 * w 3, w 0 + 2 * w 3, w 1 + 2 * w 3, w 2 + 2 * w 3]

theorem cmatrix_mulVec (w : Fin 4 → ZMod 3) : cmatrix *ᵥ w = Cx w := by
  ext i
  fin_cases i <;> simp [cmatrix, Cx, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[expose] def A1 (a b d e : ZMod 3) : M4 :=
  Matrix.of fun i j => (![![a, b, d, e], Cx ![a, b, d, e], Cx (Cx ![a, b, d, e]),
    Cx (Cx (Cx ![a, b, d, e]))] j) i

theorem col_param (M : M4) (h : M * cmatrix = cmatrix * M) :
    ∃ a b d e : ZMod 3, M = A1 a b d e := by
  have key : ∀ w : Fin 4 → ZMod 3, M *ᵥ (cmatrix *ᵥ w) = cmatrix *ᵥ (M *ᵥ w) := by
    intro w
    rw [Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]
  have e1 : cmatrix *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 3) = Pi.single 1 1 := by decide
  have e2 : cmatrix *ᵥ (Pi.single 1 1 : Fin 4 → ZMod 3) = Pi.single 2 1 := by decide
  have e3 : cmatrix *ᵥ (Pi.single 2 1 : Fin 4 → ZMod 3) = Pi.single 3 1 := by decide
  have c1 : M *ᵥ (Pi.single 1 1 : Fin 4 → ZMod 3) = Cx (M *ᵥ Pi.single 0 1) := by
    rw [← e1, key, cmatrix_mulVec]
  have c2 : M *ᵥ (Pi.single 2 1 : Fin 4 → ZMod 3) = Cx (M *ᵥ Pi.single 1 1) := by
    rw [← e2, key, cmatrix_mulVec]
  have c3 : M *ᵥ (Pi.single 3 1 : Fin 4 → ZMod 3) = Cx (M *ᵥ Pi.single 2 1) := by
    rw [← e3, key, cmatrix_mulVec]
  obtain ⟨a, b, d, e, hv⟩ : ∃ a b d e : ZMod 3,
      M *ᵥ (Pi.single 0 1 : Fin 4 → ZMod 3) = ![a, b, d, e] :=
    ⟨_, _, _, _, by ext i; fin_cases i <;> rfl⟩
  refine ⟨a, b, d, e, ?_⟩
  ext i j
  have hj : M *ᵥ (Pi.single j 1 : Fin 4 → ZMod 3) =
      ![![a, b, d, e], Cx ![a, b, d, e], Cx (Cx ![a, b, d, e]),
        Cx (Cx (Cx ![a, b, d, e]))] j := by
    fin_cases j
    · simpa using hv
    · simp [c1, hv]
    · simp [c2, c1, hv]
    · simp [c3, c2, c1, hv]
  have := congrFun hj i
  rw [Matrix.mulVec_single_one] at this
  exact this

@[expose] def B0 : M4 := !![0, 0, 1, 0; 0, 0, 1, 1; 2, 2, 0, 0; 0, 2, 0, 0]

@[expose] def B0i : M4 := !![0, 0, 2, 1; 0, 0, 0, 2; 1, 0, 0, 0; 2, 1, 0, 0]

theorem B0i_mul_B0 : B0i * B0 = 1 := by decide +kernel

theorem B0i_mul_cmatrix : B0i * cmatrix = cmatrix.adjugate.transpose * B0i := by decide +kernel

@[expose] def W : List (M4 × M4) :=
  [(!![0, 0, 1, 0; 2, 1, 1, 2; 1, 0, 0, 0; 0, 0, 0, 2],
    !![0, 0, 1, 0; 2, 1, 1, 2; 1, 0, 0, 0; 0, 0, 0, 2]),
   (!![0, 0, 0, 1; 0, 2, 0, 0; 2, 0, 0, 2; 0, 0, 1, 2],
    !![2, 0, 2, 0; 0, 2, 0, 0; 1, 0, 0, 1; 1, 0, 0, 0]),
   (!![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 0, 0; 2, 2, 2, 2],
    !![0, 0, 1, 0; 2, 2, 2, 2; 0, 1, 0, 0; 1, 0, 0, 0]),
   (!![0, 0, 1, 1; 0, 0, 1, 0; 0, 1, 0, 2; 1, 0, 0, 1],
    !![2, 1, 0, 1; 1, 2, 1, 0; 0, 1, 0, 0; 1, 2, 0, 0]),
   (!![0, 0, 0, 1; 0, 0, 1, 0; 1, 0, 1, 0; 0, 2, 2, 1],
    !![0, 2, 1, 0; 1, 2, 0, 2; 0, 1, 0, 0; 1, 0, 0, 0])]

@[expose] def goodW (p : M4 × M4) : Bool :=
  decide (p.1.det = 1 ∧ p.1 * p.2 = 1 ∧
    ((cmatrix * (p.1 * cmatrix * p.2)) * (cmatrix * (p.1 * cmatrix * p.2)) = 1 ∨
      (cmatrix * (p.1 * cmatrix * p.2)) * (cmatrix * (p.1 * cmatrix * p.2)) =
        (2 : ZMod 3) • (1 : M4)) ∧
    ¬ (cmatrix * (p.1 * cmatrix * p.2) = 1 ∨
      cmatrix * (p.1 * cmatrix * p.2) = (2 : ZMod 3) • (1 : M4)))

theorem W_good : W.all goodW = true := by decide +kernel

theorem W_spec {p : M4 × M4} (hp : p ∈ W) :
    p.1.det = 1 ∧ p.1 * p.2 = 1 ∧
    ((cmatrix * (p.1 * cmatrix * p.2)) * (cmatrix * (p.1 * cmatrix * p.2)) = 1 ∨
      (cmatrix * (p.1 * cmatrix * p.2)) * (cmatrix * (p.1 * cmatrix * p.2)) =
        (2 : ZMod 3) • (1 : M4)) ∧
    ¬ (cmatrix * (p.1 * cmatrix * p.2) = 1 ∨
      cmatrix * (p.1 * cmatrix * p.2) = (2 : ZMod 3) • (1 : M4)) :=
  of_decide_eq_true (List.all_eq_true.1 W_good p hp)

theorem fixed_witness_inner : ∀ a b d e : ZMod 3,
    A1 a b d e ≠ 0 →
    A1 a b d e * A1 a b d e = (A1 a b d e * A1 a b d e) 0 0 • (1 : M4) →
    ∃ p ∈ W, ∃ c'' : ZMod 3, (c'' = 1 ∨ c'' = 2) ∧
      A1 a b d e * p.1 = c'' • (p.1 * A1 a b d e) := by
  decide +kernel

theorem fixed_witness_outer : ∀ a b d e : ZMod 3,
    A1 a b d e ≠ 0 →
    (A1 a b d e * B0 = (A1 a b d e * B0).transpose ∨
      A1 a b d e * B0 = (2 : ZMod 3) • (A1 a b d e * B0).transpose) →
    ∃ p ∈ W, ∃ c'' : ZMod 3, (c'' = 1 ∨ c'' = 2) ∧
      (A1 a b d e * B0) * p.2.transpose = c'' • (p.1 * (A1 a b d e * B0)) := by
  decide +kernel

theorem adjugate_eq_of_mul {w wi : M4} (hdet : w.det = 1) (h : w * wi = 1) :
    w.adjugate = wi := by
  have h1 : w.adjugate * w = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
  calc w.adjugate = w.adjugate * (w * wi) := by rw [h, Matrix.mul_one]
    _ = (w.adjugate * w) * wi := (Matrix.mul_assoc _ _ _).symm
    _ = wi := by rw [h1, Matrix.one_mul]

theorem even_orderOf_proj (Q : SL4)
    (h1 : (Q : M4) * (Q : M4) = 1 ∨ (Q : M4) * (Q : M4) = (2 : ZMod 3) • (1 : M4))
    (h2 : ¬ ((Q : M4) = 1 ∨ (Q : M4) = (2 : ZMod 3) • (1 : M4))) :
    Even (orderOf (proj 4 (ZMod 3) Q)) := by
  have h : orderOf (proj 4 (ZMod 3) Q) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, proj_eq_one_iff', Matrix.SpecialLinearGroup.coe_mul]
      exact h1
    · rw [Ne, proj_eq_one_iff']
      exact h2
  rw [h]
  exact even_two

theorem even_order_W (w : SL4) (wi : M4) (hmul : (w : M4) * wi = 1)
    (h1 : (cmatrix * ((w : M4) * cmatrix * wi)) * (cmatrix * ((w : M4) * cmatrix * wi)) = 1 ∨
      (cmatrix * ((w : M4) * cmatrix * wi)) * (cmatrix * ((w : M4) * cmatrix * wi)) =
        (2 : ZMod 3) • (1 : M4))
    (h2 : ¬ (cmatrix * ((w : M4) * cmatrix * wi) = 1 ∨
      cmatrix * ((w : M4) * cmatrix * wi) = (2 : ZMod 3) • (1 : M4))) :
    Even (orderOf (zStar * (proj 4 (ZMod 3) w * zStar * (proj 4 (ZMod 3) w)⁻¹))) := by
  have hx : zStar * (proj 4 (ZMod 3) w * zStar * (proj 4 (ZMod 3) w)⁻¹) =
      proj 4 (ZMod 3) (cmat * (w * cmat * w⁻¹)) := by
    simp [zStar, map_mul, map_inv]
  have hinv : ((w⁻¹ : SL4) : M4) = wi := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    exact adjugate_eq_of_mul w.2 hmul
  have hQ : (((cmat * (w * cmat * w⁻¹)) : SL4) : M4) =
      cmatrix * ((w : M4) * cmatrix * wi) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, hinv]
    rfl
  rw [hx]
  exact even_orderOf_proj _ (by rw [hQ]; exact h1) (by rw [hQ]; exact h2)

theorem cmatrix_pow_five : cmatrix ^ 5 = 1 := by decide +kernel

theorem cmatrix_not_scalar :
    ¬ (cmatrix = 1 ∨ cmatrix = (2 : ZMod 3) • (1 : M4)) := by decide +kernel

end Mat

open Mat

theorem orderOf_zStar : orderOf zStar = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [zStar, ← map_pow, proj_eq_one_iff', Matrix.SpecialLinearGroup.coe_pow]
    exact Or.inl cmatrix_pow_five
  · rw [zStar, Ne, proj_eq_one_iff']
    exact cmatrix_not_scalar

theorem l43_witness (α : MulAut (projectiveSL 4 (ZMod 3))) (hα : α * α = 1)
    (hz : α zStar = zStar) :
    ∃ g : projectiveSL 4 (ZMod 3), α g = g ∧ Even (orderOf (zStar * (g * zStar * g⁻¹))) := by
  obtain ⟨A, ε, hε, rfl⟩ := aut_form α
  have htrans := standard_automorphism_transport (K := ZMod 3) (n := 4)
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hα hz
    rw [htrans.1] at hα
    obtain ⟨c', hc'⟩ := scalar_of_conj (A * A) hα
    rw [Units.val_mul] at hc'
    obtain ⟨c, hc, hAC⟩ := (conj_proj_iff A cmat cmat).1 hz.symm
    have hAC' : (A : M4) * cmatrix = c • (cmatrix * (A : M4)) := hAC
    have hc1 : c = 1 := by
      have htr := trace_eq_of_mul A c cmatrix cmatrix hAC'
      rcases hc with rfl | rfl
      · rfl
      · exfalso
        revert htr
        decide
    subst hc1
    rw [one_smul] at hAC'
    obtain ⟨a, b, d, e, hA⟩ := col_param (A : M4) hAC'
    have hne : (A : M4) ≠ 0 := Units.ne_zero A
    rw [hA] at hne hc'
    have h2 : A1 a b d e * A1 a b d e = (A1 a b d e * A1 a b d e) 0 0 • (1 : M4) := by
      rw [hc']
      simp
    obtain ⟨p, hpW, c'', hc'', hfix⟩ := fixed_witness_inner a b d e hne h2
    obtain ⟨hdet, hmul, hQ1, hQ2⟩ := W_spec hpW
    refine ⟨proj 4 (ZMod 3) ⟨p.1, hdet⟩, ?_, even_order_W ⟨p.1, hdet⟩ p.2 hmul hQ1 hQ2⟩
    rw [pow_zero, mul_one]
    exact ((conj_proj_iff A ⟨p.1, hdet⟩ ⟨p.1, hdet⟩).2
      ⟨c'', hc'', by rw [hA]; exact hfix⟩).symm
  ·
    rw [pow_one] at hα hz
    have hα' : conjAut 4 (ZMod 3) (A * GeneralLinearGroup.inverseTranspose A) = 1 := by
      rw [← htrans.1, ← htrans.2.2.2.2.1 A, ← hα]
      simp only [mul_assoc]
    obtain ⟨c', hc'⟩ := scalar_of_conj _ hα'
    rw [Units.val_mul, GeneralLinearGroup.coe_inverseTranspose] at hc'
    have hsym : (A : M4) = c' • (A : M4).transpose := by
      have h1 : (A : M4) * ((↑A⁻¹ : M4).transpose * (A : M4).transpose) =
          c' • (A : M4).transpose := by
        rw [← Matrix.mul_assoc, hc', Matrix.smul_mul, Matrix.one_mul]
      rwa [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one] at h1
    have hc'12 : c' = 1 ∨ c' = 2 := by
      have h3 : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2 := by decide
      rcases h3 c' with h | h | h
      · exfalso
        apply Units.ne_zero A
        rw [hsym, h, zero_smul]
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨c, hc, hAD⟩ := (dual_proj_iff A cmat cmat).1 hz.symm
    have hAD' : (A : M4) * cmatrix.adjugate.transpose = c • (cmatrix * (A : M4)) := hAD
    have hc1 : c = 1 := by
      have htr := trace_eq_of_mul A c _ cmatrix hAD'
      rcases hc with rfl | rfl
      · rfl
      · exfalso
        revert htr
        decide
    subst hc1
    rw [one_smul] at hAD'
    have hM : ((A : M4) * B0i) * cmatrix = cmatrix * ((A : M4) * B0i) := by
      calc (A : M4) * B0i * cmatrix = (A : M4) * (B0i * cmatrix) := Matrix.mul_assoc _ _ _
        _ = (A : M4) * (cmatrix.adjugate.transpose * B0i) := by rw [B0i_mul_cmatrix]
        _ = ((A : M4) * cmatrix.adjugate.transpose) * B0i := (Matrix.mul_assoc _ _ _).symm
        _ = (cmatrix * (A : M4)) * B0i := by rw [hAD']
        _ = cmatrix * ((A : M4) * B0i) := Matrix.mul_assoc _ _ _
    obtain ⟨a, b, d, e, hcol⟩ := col_param _ hM
    have hA : (A : M4) = A1 a b d e * B0 := by
      rw [← hcol, Matrix.mul_assoc, B0i_mul_B0, Matrix.mul_one]
    have hne : A1 a b d e ≠ 0 := by
      intro h0
      apply Units.ne_zero A
      rw [hA, h0, Matrix.zero_mul]
    have hsym' : A1 a b d e * B0 = (A1 a b d e * B0).transpose ∨
        A1 a b d e * B0 = (2 : ZMod 3) • (A1 a b d e * B0).transpose := by
      rw [hA] at hsym
      rcases hc'12 with rfl | rfl
      · left
        rw [one_smul] at hsym
        exact hsym
      · right
        exact hsym
    obtain ⟨p, hpW, c'', hc'', hfix⟩ := fixed_witness_outer a b d e hne hsym'
    obtain ⟨hdet, hmul, hQ1, hQ2⟩ := W_spec hpW
    have hadj : p.1.adjugate = p.2 := adjugate_eq_of_mul hdet hmul
    refine ⟨proj 4 (ZMod 3) ⟨p.1, hdet⟩, ?_, even_order_W ⟨p.1, hdet⟩ p.2 hmul hQ1 hQ2⟩
    show conjAut 4 (ZMod 3) A (dualAut 4 (ZMod 3) (proj 4 (ZMod 3) ⟨p.1, hdet⟩)) =
      proj 4 (ZMod 3) ⟨p.1, hdet⟩
    exact ((dual_proj_iff A ⟨p.1, hdet⟩ ⟨p.1, hdet⟩).2
      ⟨c'', hc'', by rw [hA]; exact hadj ▸ hfix⟩).symm

end CFSG.GH74.GLS.C3.Layer1.EndN.L43
