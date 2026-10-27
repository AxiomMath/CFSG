module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Residuals

public section

open CFSG.LieType.Chevalley CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator Polynomial

namespace CFSG.HardMathSupport.Seitz.Proving

section OrderThree

variable {K : Type} [Field K] [Finite K]

theorem orderThreeSL_val (K : Type) [Field K] :
    (orderThreeSL K : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, -1] :=
  rfl

theorem no_root_of_three_dvd (h3 : 3 ∣ Nat.card K + 1) (ω : K) : ω ^ 2 + ω + 1 ≠ 0 := by
  intro h
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at h
  have hcube : ω ^ 3 = 1 := by linear_combination (ω - 1) * h
  have := Fintype.ofFinite K
  have hq : ω ^ (Fintype.card K - 1) = 1 := FiniteField.pow_card_sub_one_eq_one ω hω0
  rw [← Nat.card_eq_fintype_card] at hq
  have hcard : 1 < Nat.card K := Finite.one_lt_card
  have hcop : Nat.gcd 3 (Nat.card K - 1) = 1 := by
    have hnd : ¬ 3 ∣ Nat.card K - 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd
  have hω1 : ω = 1 := by
    have h1 : ω ^ Nat.gcd 3 (Nat.card K - 1) = 1 := pow_gcd_eq_one.2 ⟨hcube, hq⟩
    rwa [hcop, pow_one] at h1
  have h3K : (3 : K) = 0 := by
    subst hω1
    linear_combination h
  have hchar : ringChar K ∣ 3 :=
    (CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by simpa using h3K)
  have hprime : (ringChar K).Prime := (Nat.irreducible_iff_nat_prime _).1 (CharP.char_is_prime K (ringChar K))
  have hchar3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_three).1 hchar
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : 3 ∣ Nat.card K := by
    rw [hchar3, ← Nat.card_eq_fintype_card] at hn
    rw [hn]
    exact dvd_pow_self 3 n.ne_zero
  omega

omit [Finite K] in
theorem trace_core {a b c d : K} (hdet : a * d - b * c = 1)
    (e00 : a * (a * a + b * c) + b * (c * a + d * c) = 1)
    (e01 : a * (a * b + b * d) + b * (c * b + d * d) = 0)
    (e10 : c * (a * a + b * c) + d * (c * a + d * c) = 0)
    (e11 : c * (a * b + b * d) + d * (c * b + d * d) = 1) :
    a + d = -1 ∨ (b = 0 ∧ c = 0 ∧ a = 1 ∧ d = 1) := by
  by_cases hne : a + d = -1
  · exact Or.inl hne
  right
  have E00 : ((a + d) ^ 2 - 1) * a = (a + d) + 1 := by
    linear_combination e00 + (2 * a + d) * hdet
  have E01 : ((a + d) ^ 2 - 1) * b = 0 := by linear_combination e01 + b * hdet
  have E10 : ((a + d) ^ 2 - 1) * c = 0 := by linear_combination e10 + c * hdet
  have E11 : ((a + d) ^ 2 - 1) * d = (a + d) + 1 := by
    linear_combination e11 + (d + (a + d)) * hdet
  have ht2 : (a + d) ^ 2 - 1 ≠ 0 := by
    intro h
    apply hne
    linear_combination -E00 + a * h
  have hb0 : b = 0 := (mul_eq_zero.1 E01).resolve_left ht2
  have hc0 : c = 0 := (mul_eq_zero.1 E10).resolve_left ht2
  have had : a - d = 0 :=
    (mul_eq_zero.1 (show ((a + d) ^ 2 - 1) * (a - d) = 0 by linear_combination E00 - E11)).resolve_left
      ht2
  have hda : d = a := by linear_combination -had
  subst hb0 hc0 hda
  have ha2 : d * d = 1 := by linear_combination hdet
  have ha3 : d ^ 3 = 1 := by linear_combination e00
  have ha1 : d = 1 := by linear_combination ha3 - d * ha2
  exact ⟨rfl, rfl, ha1, ha1⟩

omit [Finite K] in
theorem trace_eq_neg_one_of_cube {A : SL2 K} (hA : A ^ 3 = 1) (hA1 : A ≠ 1) :
    (A : Matrix (Fin 2) (Fin 2) K) 0 0 + (A : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have hM3 : (A : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hA, Matrix.SpecialLinearGroup.coe_one]
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM3 0) 0
  have e01 := congrFun (congrFun hM3 0) 1
  have e10 := congrFun (congrFun hM3 1) 0
  have e11 := congrFun (congrFun hM3 1) 1
  simp [pow_three, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rcases trace_core hdet (by linear_combination e00) (by linear_combination e01)
      (by linear_combination e10) (by linear_combination e11) with h | ⟨hb, hc, ha, hd⟩
  · exact h
  · exfalso
    apply hA1
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, ha, hd]

theorem exists_intertwiner (h3 : 3 ∣ Nat.card K + 1) (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 1) (htr : A 0 0 + A 1 1 = -1) :
    ∃ S : Matrix (Fin 2) (Fin 2) K, S.det ≠ 0 ∧
      S * A = (orderThreeSL K : Matrix (Fin 2) (Fin 2) K) * S := by
  rw [Matrix.det_fin_two] at hdet
  rw [orderThreeSL_val]
  by_cases hc : A 1 0 = 0
  · by_cases hb : A 0 1 = 0
    · exfalso
      apply no_root_of_three_dvd h3 (A 0 0)
      have hd : A 1 1 = -1 - A 0 0 := by linear_combination htr
      rw [hc, hb, hd] at hdet
      linear_combination -hdet
    · refine ⟨!![A 1 1, -A 0 1; 1, 0], ?_, ?_⟩
      · simp [Matrix.det_fin_two, hb]
      · ext i j
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          first | ring1 | linear_combination hdet | linear_combination htr
  · refine ⟨!![-A 1 0, A 0 0; 0, 1], ?_, ?_⟩
    · simp [Matrix.det_fin_two, hc]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        first | ring1 | linear_combination hdet | linear_combination htr

theorem exists_norm_form (h3 : 3 ∣ Nat.card K + 1) (ε : K) :
    ∃ x y : K, x ^ 2 - x * y + y ^ 2 = ε := by
  obtain ⟨f, hf⟩ : ∃ f : K[X], f = X ^ 2 + X + 1 := ⟨_, rfl⟩
  have hmonic : f.Monic := by rw [hf]; monicity!
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have hdeg : f.natDegree = 2 := by rw [hf]; compute_degree!
  have hnot : ∀ x : K, ¬ f.IsRoot x := by
    intro x hx
    apply no_root_of_three_dvd h3 x
    simpa [hf, Polynomial.IsRoot] using hx
  have hirr : Irreducible f :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) hnot
  have : Fact (Irreducible f) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot f) := hmonic.finite_adjoinRoot
  have : Finite (AdjoinRoot f) := Module.finite_of_finite K
  obtain ⟨z, hz⟩ := FiniteField.norm_surjective K (AdjoinRoot f) ε
  let pb := AdjoinRoot.powerBasis hf0
  have hdim : pb.dim = 2 := hdeg
  let b : Module.Basis (Fin 2) K (AdjoinRoot f) := pb.basis.reindex (finCongr hdim)
  have hb0 : b 0 = 1 := by
    simp [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm]
  have hgen : pb.gen = AdjoinRoot.root f := rfl
  have hb1 : b 1 = AdjoinRoot.root f := by
    simp [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, finCongr_symm, hgen]
  have hθ : AdjoinRoot.root f ^ 2 + AdjoinRoot.root f + 1 = 0 := by
    have := AdjoinRoot.eval₂_root f
    simpa [hf] using this
  obtain ⟨x, y, hzxy⟩ : ∃ x y : K, z = x • (1 : AdjoinRoot f) + y • AdjoinRoot.root f := by
    refine ⟨b.repr z 0, b.repr z 1, ?_⟩
    have hsum := b.sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1] at hsum
    exact hsum.symm
  refine ⟨x, y, ?_⟩
  have hzb0 : z * b 0 = x • b 0 + y • b 1 := by
    rw [hb0, hb1, hzxy, mul_one]
  have hzb1 : z * b 1 = (-y) • b 0 + (x - y) • b 1 := by
    rw [hb0, hb1, hzxy]
    simp only [Algebra.smul_def, map_sub, map_neg]
    linear_combination (algebraMap K (AdjoinRoot f) y) * hθ
  have hdetz : Algebra.norm K z = x * (x - y) - (-y) * y := by
    rw [Algebra.norm_eq_matrix_det b z, Matrix.det_fin_two]
    simp only [Algebra.leftMulMatrix_eq_repr_mul, hzb0, hzb1, map_add, map_smul,
      Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
    simp
  rw [← hz, hdetz]
  ring

theorem exists_conj_eq_orderThreeSL (h3 : 3 ∣ Nat.card K + 1)
    {A : SL2 K} (hA : A ^ 3 = 1) (hA1 : A ≠ 1) :
    ∃ S : SL2 K, S * A * S⁻¹ = orderThreeSL K := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = 1 := Matrix.SpecialLinearGroup.det_coe A
  have htr := trace_eq_neg_one_of_cube hA hA1
  obtain ⟨S₀, hS₀det, hS₀⟩ := exists_intertwiner h3 (A : Matrix (Fin 2) (Fin 2) K) hdet htr
  obtain ⟨x, y, hxy⟩ := exists_norm_form h3 (S₀.det)⁻¹
  let T : Matrix (Fin 2) (Fin 2) K := !![x, y; -y, x - y]
  have hTdet : T.det = (S₀.det)⁻¹ := by
    rw [← hxy]
    simp only [T, Matrix.det_fin_two_of]
    ring
  have hTM : T * (orderThreeSL K : Matrix (Fin 2) (Fin 2) K) =
      (orderThreeSL K : Matrix (Fin 2) (Fin 2) K) * T := by
    rw [orderThreeSL_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hS1det : (T * S₀).det = 1 := by
    rw [Matrix.det_mul, hTdet, inv_mul_cancel₀ hS₀det]
  let S1 : SL2 K := ⟨T * S₀, hS1det⟩
  have key : S1 * A = orderThreeSL K * S1 := by
    refine Subtype.ext ?_
    show (T * S₀) * (A : Matrix (Fin 2) (Fin 2) K) =
      (orderThreeSL K : Matrix (Fin 2) (Fin 2) K) * (T * S₀)
    rw [Matrix.mul_assoc, hS₀, ← Matrix.mul_assoc, hTM, Matrix.mul_assoc]
  exact ⟨S1, by rw [key, mul_inv_cancel_right]⟩

end OrderThree

end CFSG.HardMathSupport.Seitz.Proving
