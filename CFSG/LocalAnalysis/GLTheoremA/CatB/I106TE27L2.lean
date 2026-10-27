module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27Lift
public import CFSG.Adapters.LinearCatalog

public section

noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27

open Polynomial Matrix

abbrev cubic3 : (ZMod 3)[X] := X ^ 3 - X - 1

theorem natDegree_cubic3 : cubic3.natDegree = 3 := by
  unfold cubic3
  compute_degree!

theorem monic_cubic3 : cubic3.Monic := by
  unfold cubic3
  monicity!

theorem irreducible_cubic3 : Irreducible cubic3 := by
  refine irreducible_of_degree_le_three_of_not_isRoot (by rw [natDegree_cubic3]; decide) ?_
  intro x
  simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one]
  revert x
  decide

section Field

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

theorem exists_cubic3_root (hK : Fintype.card K = 3 ^ 6) : ∃ μ : K, μ ^ 3 = μ + 1 := by
  letI := ZMod.algebra K 3
  haveI : Fact (Irreducible cubic3) := ⟨irreducible_cubic3⟩
  have hf0 : cubic3 ≠ 0 := irreducible_cubic3.ne_zero
  have h1 : Module.finrank (ZMod 3) (AdjoinRoot cubic3) = 3 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, natDegree_cubic3]
  have h2 : Module.finrank (ZMod 3) K = 6 := by
    have h := Module.card_eq_pow_finrank (K := ZMod 3) (V := K)
    rw [hK, ZMod.card] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 3)
    (K := AdjoinRoot cubic3) (L := K) (by rw [h1, h2]; norm_num)
  refine ⟨φ (AdjoinRoot.root cubic3), ?_⟩
  have h : aeval (φ (AdjoinRoot.root cubic3)) cubic3 = 0 := by
    rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  simp only [cubic3, map_sub, map_pow, aeval_X, map_one] at h
  linear_combination h

theorem cubic3_root_indep {μ : K} (hμ : μ ^ 3 = μ + 1) {a b c : ℤ}
    (h : (a : K) + b * μ + c * μ ^ 2 = 0) :
    (a : ZMod 3) = 0 ∧ (b : ZMod 3) = 0 ∧ (c : ZMod 3) = 0 := by
  letI := ZMod.algebra K 3
  have hroot : aeval μ cubic3 = 0 := by
    simp only [cubic3, map_sub, map_pow, aeval_X, map_one]
    linear_combination hμ
  have hmin := minpoly.eq_of_irreducible_of_monic irreducible_cubic3 hroot monic_cubic3
  by_contra hne
  have hp0 : (C (a : ZMod 3) + C (b : ZMod 3) * X + C (c : ZMod 3) * X ^ 2 : (ZMod 3)[X]) ≠ 0 := by
    intro hp
    apply hne
    have h0 := congrArg (coeff · 0) hp
    have h1 := congrArg (coeff · 1) hp
    have h2 := congrArg (coeff · 2) hp
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X, coeff_zero] at h0 h1 h2
    norm_num at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hpa : aeval μ (C (a : ZMod 3) + C (b : ZMod 3) * X + C (c : ZMod 3) * X ^ 2) = 0 := by
    simp only [map_add, map_mul, aeval_C, aeval_X, map_pow, map_intCast]
    exact h
  have hdeg := natDegree_le_natDegree (minpoly.degree_le_of_ne_zero (ZMod 3) μ hp0 hpa)
  rw [← hmin, natDegree_cubic3] at hdeg
  have h2 : (C (a : ZMod 3) + C (b : ZMod 3) * X + C (c : ZMod 3) * X ^ 2 :
      (ZMod 3)[X]).natDegree ≤ 2 := by
    compute_degree
  omega

end Field

section PSL

variable {K : Type*} [Field K]

def uSL (t : K) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, t; 0, 1], by simp [det_fin_two]⟩

def dSL (s : K) (hs : s ≠ 0) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![s, 0; 0, s⁻¹], by simp [det_fin_two, hs]⟩

theorem uSL_add (s t : K) : uSL (s + t) = uSL s * uSL t := by
  refine Subtype.ext ?_
  change !![1, s + t; 0, 1] = !![1, s; 0, 1] * !![1, t; 0, 1]
  rw [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem uSL_zero : uSL (0 : K) = 1 := by
  refine Subtype.ext ?_
  change !![1, 0; 0, 1] = 1
  exact Matrix.one_fin_two.symm

theorem uSL_pow (t : K) (n : ℕ) : uSL t ^ n = uSL (n * t) := by
  induction n with
  | zero => simp [uSL_zero]
  | succ n ih =>
    rw [pow_succ, ih, ← uSL_add]
    congr 1
    push_cast
    ring

theorem uSL_neg (t : K) : uSL (-t) = (uSL t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← uSL_add, neg_add_cancel, uSL_zero]

theorem dSL_mul_uSL (s : K) (hs : s ≠ 0) (t : K) :
    dSL s hs * uSL t = uSL (s ^ 2 * t) * dSL s hs := by
  refine Subtype.ext ?_
  change !![s, 0; 0, s⁻¹] * !![1, t; 0, 1] = !![1, s ^ 2 * t; 0, 1] * !![s, 0; 0, s⁻¹]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

def uP (t : K) : ProjectiveSpecialLinearGroup (Fin 2) K := QuotientGroup.mk (uSL t)

def dP (s : K) (hs : s ≠ 0) : ProjectiveSpecialLinearGroup (Fin 2) K :=
  QuotientGroup.mk (dSL s hs)

theorem uP_add (s t : K) : uP (s + t) = uP s * uP t := by
  rw [uP, uSL_add, QuotientGroup.mk_mul]
  rfl

theorem uP_zero : uP (0 : K) = 1 := by
  rw [uP, uSL_zero]
  rfl

theorem uP_pow (t : K) (n : ℕ) : uP t ^ n = uP (n * t) := by
  rw [uP, ← QuotientGroup.mk_pow, uSL_pow]
  rfl

theorem uP_neg (t : K) : uP (-t) = (uP t)⁻¹ := by
  rw [uP, uSL_neg, QuotientGroup.mk_inv]
  rfl

theorem dP_conj (s : K) (hs : s ≠ 0) (t : K) :
    dP s hs * uP t * (dP s hs)⁻¹ = uP (s ^ 2 * t) := by
  rw [mul_inv_eq_iff_eq_mul, dP, uP, uP, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    dSL_mul_uSL]

theorem uP_injective : Function.Injective (uP : K → ProjectiveSpecialLinearGroup (Fin 2) K) := by
  intro s t h
  rw [uP, uP, QuotientGroup.eq, ← uSL_neg, ← uSL_add] at h
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have h01 := congrFun (congrFun hr 0) 1
  simp [uSL] at h01
  linear_combination h01

private theorem fin3_eq {i j : Fin 3} (h : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ZMod 3) = 0) :
    i = j := by
  revert i j
  decide

theorem e27Lifts_psl2 [Finite K] (hK : Nat.card K = 3 ^ 6) :
    E27Lifts (ProjectiveSpecialLinearGroup (Fin 2) K) := by
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Fintype.card K = 3 ^ 6 := by rw [← Nat.card_eq_fintype_card, hK]
  haveI : CharP K 3 := charP_of_card_eq_prime_pow hK'
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  obtain ⟨μ, hμ⟩ := exists_cubic3_root hK'
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    norm_num at hμ
  have hμ13 : μ ^ 13 = 1 := by
    linear_combination (7 + 5 * μ + 4 * μ ^ 2 + 3 * μ ^ 3 + 2 * μ ^ 4 + 2 * μ ^ 5 + μ ^ 6 +
      μ ^ 7 + μ ^ 8 + μ ^ 10) * hμ + (2 + 4 * μ + 3 * μ ^ 2) * h3
  have hl0 : μ ^ 7 ≠ 0 := pow_ne_zero _ hμ0
  have hl2 : (μ ^ 7) ^ 2 = μ := by linear_combination μ * hμ13
  obtain ⟨i, hi⟩ : IsSquare (-1 : K) :=
    FiniteField.isSquare_neg_one_iff.mpr (by rw [hK']; norm_num)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  have hinv : ∀ t : K, dP i hi0 * uP t * (dP i hi0)⁻¹ = (uP t)⁻¹ := by
    intro t
    rw [dP_conj, ← uP_neg]
    congr 1
    linear_combination (-t) * hi
  have hcyc : ∀ t : K, dP (μ ^ 7) hl0 * uP t * (dP (μ ^ 7) hl0)⁻¹ = uP (μ * t) := by
    intro t
    rw [dP_conj, hl2]
  have hcomm : ∀ s t : K, uP s * uP t = uP t * uP s := by
    intro s t
    rw [← uP_add, ← uP_add, add_comm]
  have hord : ∀ t : K, uP t ^ 3 = 1 := by
    intro t
    rw [uP_pow]
    push_cast
    rw [h3, zero_mul, uP_zero]
  have hprod : ∀ v : Fin 3 × Fin 3 × Fin 3, prod3 (uP 1) (uP μ) (uP (μ ^ 2)) v =
      uP (((v.1 : ℕ) : K) * 1 + ((v.2.1 : ℕ) : K) * μ + ((v.2.2 : ℕ) : K) * μ ^ 2) := by
    intro v
    simp only [prod3, uP_pow, ← uP_add]
  have hinj : Function.Injective (prod3 (uP 1) (uP μ) (uP (μ ^ 2))) := by
    intro v w hvw
    rw [hprod, hprod] at hvw
    have h' := uP_injective hvw
    obtain ⟨h1, h2, h3⟩ := cubic3_root_indep hμ (a := ((v.1 : ℕ) : ℤ) - ((w.1 : ℕ) : ℤ))
      (b := ((v.2.1 : ℕ) : ℤ) - ((w.2.1 : ℕ) : ℤ)) (c := ((v.2.2 : ℕ) : ℤ) - ((w.2.2 : ℕ) : ℤ))
      (by push_cast; linear_combination h')
    exact Prod.ext (fin3_eq h1) (Prod.ext (fin3_eq h2) (fin3_eq h3))
  refine e27Lifts_of_cycle₃ (n := dP (μ ^ 7) hl0) (hcomm _ _) (hcomm _ _) (hcomm _ _) (hord _)
    (hord _) (hord _) hinj ⟨dP i hi0, hinv _⟩ ⟨dP i hi0, hinv _⟩ ⟨dP i hi0, hinv _⟩ ?_ ?_ ?_
  · rw [hcyc, mul_one]
  · rw [hcyc, ← pow_two]
  · rw [hcyc, ← pow_succ', hμ, add_comm, uP_add]

end PSL

theorem e27Lifts_l2_729 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hq : q.card = 729) : E27Lifts (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩).Group := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hc : q.p ^ q.exponent = 3 ^ 6 := by rw [← TauCeti.PrimePower.card_def, hq]; norm_num
  have hK : Nat.card (GaloisField q.p q.exponent) = 3 ^ 6 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', hc]
  exact E27Lifts.of_mulEquiv (G := ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q.p q.exponent))
    (G' := TauCeti.ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩)
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm (e27Lifts_psl2 hK)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27
