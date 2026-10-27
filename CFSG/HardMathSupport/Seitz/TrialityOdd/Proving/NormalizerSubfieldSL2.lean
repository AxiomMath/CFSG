module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SpanOneCInv

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Matrix

theorem mem_range_of_sq_mem_range {F K : Type*} [Field F] [Field K] [Algebra F K] {μ : K} {c : F}
    (h3 : Module.finrank F K = 3) (hc : μ ^ 2 = algebraMap F K c) :
    μ ∈ (algebraMap F K).range := by
  by_contra hμ
  exact not_quadratic_of_finrank_three h3 hμ (a := 0) (b := 1) (d := -c) one_ne_zero
    (by simp [hc])

def IsFMat (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K]
    (m : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∃ y : Matrix (Fin 2) (Fin 2) F, m = y.map (algebraMap F K)

theorem isFMat_mul {F K : Type*} [Field F] [Field K] [Algebra F K]
    {m n : Matrix (Fin 2) (Fin 2) K} (hm : IsFMat F m) (hn : IsFMat F n) :
    IsFMat F (m * n) := by
  obtain ⟨y, rfl⟩ := hm
  obtain ⟨z, rfl⟩ := hn
  exact ⟨y * z, by ext i j; simp [Matrix.mul_apply]⟩

theorem entry_single_conj {K : Type*} [Field K] (G A : Matrix (Fin 2) (Fin 2) K) (i j k l : Fin 2) :
    (G * Matrix.single i j (1 : K) * A) k l = G k i * A j l := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]

theorem isFMat_conj_sub_one {F K : Type*} [Field F] [Field K] [Algebra F K]
    (G A : Matrix (Fin 2) (Fin 2) K) (hGA : G * A = 1)
    (hnorm : ∀ x : Matrix (Fin 2) (Fin 2) F, x.det = 1 →
      ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧
        G * x.map (algebraMap F K) = y.map (algebraMap F K) * G)
    (x : Matrix (Fin 2) (Fin 2) F) (hx : x.det = 1) :
    IsFMat F (G * (x.map (algebraMap F K) - 1) * A) := by
  obtain ⟨y, -, hy⟩ := hnorm x hx
  have h1 : G * (x.map (algebraMap F K) - 1) * A = G * x.map (algebraMap F K) * A - 1 := by
    rw [mul_sub, mul_one, sub_mul, hGA]
  have h2 : G * x.map (algebraMap F K) * A = y.map (algebraMap F K) := by
    rw [hy, mul_assoc, hGA, mul_one]
  refine ⟨y - 1, ?_⟩
  rw [h1, h2]
  ext i j
  by_cases h : i = j <;> simp [h]

theorem isFMat_conj_mul {F K : Type*} [Field F] [Field K] [Algebra F K]
    (G A X Y : Matrix (Fin 2) (Fin 2) K) (hAG : A * G = 1)
    (hX : IsFMat F (G * X * A)) (hY : IsFMat F (G * Y * A)) :
    IsFMat F (G * (X * Y) * A) := by
  have h := isFMat_mul hX hY
  have e : G * X * A * (G * Y * A) = G * (X * Y) * A := by
    calc G * X * A * (G * Y * A) = G * X * (A * G) * Y * A := by simp only [mul_assoc]
      _ = G * (X * Y) * A := by rw [hAG]; simp only [mul_assoc, mul_one]
  rwa [e] at h

theorem isFMat_single_conj {F K : Type*} [Field F] [Field K] [Algebra F K]
    (G A : Matrix (Fin 2) (Fin 2) K) (hGA : G * A = 1) (hAG : A * G = 1)
    (hnorm : ∀ x : Matrix (Fin 2) (Fin 2) F, x.det = 1 →
      ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧
        G * x.map (algebraMap F K) = y.map (algebraMap F K) * G)
    : ∀ i j : Fin 2, IsFMat F (G * Matrix.single i j (1 : K) * A) := by
  have hdu : (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  have hdv : (!![(1 : F), 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_fin_two]
  have hu : (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K) - 1
      = Matrix.single 0 1 (1 : K) := by
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have hv : (!![(1 : F), 0; 1, 1] : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K) - 1
      = Matrix.single 1 0 (1 : K) := by
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have E01 : IsFMat F (G * Matrix.single 0 1 (1 : K) * A) := by
    have h := isFMat_conj_sub_one G A hGA hnorm _ hdu
    rwa [hu] at h
  have E10 : IsFMat F (G * Matrix.single 1 0 (1 : K) * A) := by
    have h := isFMat_conj_sub_one G A hGA hnorm _ hdv
    rwa [hv] at h
  have s00 : (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : K)) =
      Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : K) * Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : K) := by
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have s11 : (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : K)) =
      Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : K) * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : K) := by
    ext a b; fin_cases a <;> fin_cases b <;> simp
  have E00 : IsFMat F (G * Matrix.single 0 0 (1 : K) * A) := by
    rw [s00]; exact isFMat_conj_mul G A _ _ hAG E01 E10
  have E11 : IsFMat F (G * Matrix.single 1 1 (1 : K) * A) := by
    rw [s11]; exact isFMat_conj_mul G A _ _ hAG E10 E01
  intro i j
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  have hj : j = 0 ∨ j = 1 := by fin_cases j <;> simp
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact E00
  · exact E01
  · exact E10
  · exact E11

theorem mem_SL2_of_inverse {F K : Type*} [Field F] [Field K] [Algebra F K]
    (h3 : Module.finrank F K = 3) (g A : Matrix (Fin 2) (Fin 2) K) (hg : g.det = 1)
    (hGA : g * A = 1) (hAG : A * g = 1)
    (hnorm : ∀ x : Matrix (Fin 2) (Fin 2) F, x.det = 1 →
      ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧
        g * x.map (algebraMap F K) = y.map (algebraMap F K) * g) :
    ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧ g = y.map (algebraMap F K) := by
  have hA0 : A ≠ 0 := by
    intro h; rw [h, mul_zero] at hGA; exact zero_ne_one hGA
  obtain ⟨j, l, hjl⟩ : ∃ j l, A j l ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hA0 (by ext j l; simp [h j l])
  have hent : ∀ k i, ∃ c : F, algebraMap F K c = A j l * g k i := by
    intro k i
    obtain ⟨y, hy⟩ := isFMat_single_conj (F := F) g A hGA hAG hnorm i j
    refine ⟨y k l, ?_⟩
    have h := congrFun (congrFun hy k) l
    rw [entry_single_conj, Matrix.map_apply] at h
    rw [mul_comm]
    exact h.symm
  choose w hw using hent
  obtain ⟨W, hWdef⟩ : ∃ W : Matrix (Fin 2) (Fin 2) F, ∀ k i, W k i = w k i :=
    ⟨Matrix.of w, fun _ _ => rfl⟩
  have hW : W.map (algebraMap F K) = A j l • g := by
    ext k i
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hWdef]
    exact hw k i
  have h2 : (A j l) ^ 2 = (W.map (algebraMap F K)).det := by
    rw [hW, Matrix.det_smul, hg, Fintype.card_fin, mul_one]
  have h1 : (W.map (algebraMap F K)).det = algebraMap F K W.det := by
    rw [RingHom.map_det]; rfl
  have hμ : A j l ∈ (algebraMap F K).range :=
    mem_range_of_sq_mem_range (c := W.det) h3 (by rw [h2, h1])
  obtain ⟨c0, hc0⟩ := hμ
  have hμne : A j l ≠ 0 := hjl
  have hc0ne : c0 ≠ 0 := by
    rintro rfl
    apply hjl
    rw [← hc0, map_zero]
  have hyg : (c0⁻¹ • W).map (algebraMap F K) = g := by
    ext k i
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hWdef]
    rw [map_mul, map_inv₀, hc0, hw k i, inv_mul_cancel_left₀ hμne]
  refine ⟨c0⁻¹ • W, ?_, hyg.symm⟩
  have hdy : algebraMap F K (c0⁻¹ • W).det = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hyg, hg]
  exact (algebraMap F K).injective (hdy.trans (map_one _).symm)

theorem mem_SL2_of_normalizes_SL2 {F K : Type*} [Field F] [Field K] [Algebra F K]
    (h3 : Module.finrank F K = 3) (g : Matrix (Fin 2) (Fin 2) K) (hg : g.det = 1)
    (hnorm : ∀ x : Matrix (Fin 2) (Fin 2) F, x.det = 1 →
      ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧
        g * x.map (algebraMap F K) = y.map (algebraMap F K) * g) :
    ∃ y : Matrix (Fin 2) (Fin 2) F, y.det = 1 ∧ g = y.map (algebraMap F K) := by
  refine mem_SL2_of_inverse h3 g g.adjugate hg ?_ ?_ hnorm
  · rw [Matrix.mul_adjugate, hg, one_smul]
  · rw [Matrix.adjugate_mul, hg, one_smul]

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
