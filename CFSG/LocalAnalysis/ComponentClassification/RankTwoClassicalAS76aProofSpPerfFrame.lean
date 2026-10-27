module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthDual

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap
open scoped Matrix

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

structure SpFrame (Q : QuadraticForm K (ι → K)) (u u'' : Fin 2 → ι → K) : Prop where
  uu : ∀ i j, Q.polarBilin (u i) (u j) = 0
  vv : ∀ i j, Q.polarBilin (u'' i) (u'' j) = 0
  uv : ∀ i j, Q.polarBilin (u i) (u'' j) = if i = j then 1 else 0

@[expose] def frCol (w : Fin 2 → ι → K) : Matrix ι (Fin 2) K := Matrix.of fun r k => w k r

@[expose] noncomputable def frRow (Q : QuadraticForm K (ι → K)) (w : Fin 2 → ι → K) :
    Matrix (Fin 2) ι K :=
  LinearMap.toMatrix' (LinearMap.pi fun i => Q.polarBilin.flip (w i))

omit [Fintype ι] [DecidableEq ι] in
theorem frCol_mulVec (w : Fin 2 → ι → K) (c : Fin 2 → K) : frCol w *ᵥ c = ∑ k, c k • w k := by
  ext r
  simp [frCol, mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem frRow_mulVec (Q : QuadraticForm K (ι → K)) (w : Fin 2 → ι → K) (v : ι → K) :
    frRow Q w *ᵥ v = fun i => Q.polarBilin v (w i) := by
  rw [frRow, LinearMap.toMatrix'_mulVec]
  ext i
  simp

variable {Q : QuadraticForm K (ι → K)}

theorem polarBilin_frCol_mulVec_left (w : Fin 2 → ι → K) (c : Fin 2 → K) (x : ι → K) :
    Q.polarBilin (frCol w *ᵥ c) x = c ⬝ᵥ (frRow Q w *ᵥ x) := by
  rw [frCol_mulVec, frRow_mulVec, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun k _ => by rw [polarBilin_comm]

theorem polarBilin_frCol_mulVec_right (w : Fin 2 → ι → K) (c : Fin 2 → K) (x : ι → K) :
    Q.polarBilin x (frCol w *ᵥ c) = c ⬝ᵥ (frRow Q w *ᵥ x) := by
  rw [polarBilin_comm, polarBilin_frCol_mulVec_left]

namespace SpFrame

variable {u u'' : Fin 2 → ι → K} (hF : SpFrame Q u u'')
include hF

omit [Fintype ι] [DecidableEq ι] in
theorem vu (i j : Fin 2) : Q.polarBilin (u'' i) (u j) = if i = j then 1 else 0 := by
  rw [polarBilin_comm, hF.uv]
  exact if_congr eq_comm rfl rfl

theorem frRow_mul_frCol_dual : frRow Q u'' * frCol u = 1 :=
  Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, frRow_mulVec, one_mulVec]
    ext i
    rw [polarBilin_frCol_mulVec_left, frRow_mulVec]
    simp only [dotProduct, Fin.sum_univ_two, hF.vu]
    fin_cases i <;> simp

theorem frRow_mul_frCol_dual' : frRow Q u * frCol u'' = 1 :=
  Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, frRow_mulVec, one_mulVec]
    ext i
    rw [polarBilin_frCol_mulVec_left, frRow_mulVec]
    simp only [dotProduct, Fin.sum_univ_two, hF.uv]
    fin_cases i <;> simp

theorem frRow_mul_frCol_self : frRow Q u * frCol u = 0 :=
  Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, frRow_mulVec, zero_mulVec]
    ext i
    rw [polarBilin_frCol_mulVec_left, frRow_mulVec]
    simp only [dotProduct, Fin.sum_univ_two, hF.uu, mul_zero, add_zero, Pi.zero_apply]

theorem frRow_mul_frCol_self' : frRow Q u'' * frCol u'' = 0 :=
  Matrix.ext_iff_mulVec.mpr fun c => by
    rw [← mulVec_mulVec, frRow_mulVec, zero_mulVec]
    ext i
    rw [polarBilin_frCol_mulVec_left, frRow_mulVec]
    simp only [dotProduct, Fin.sum_univ_two, hF.vv, mul_zero, add_zero, Pi.zero_apply]

end SpFrame

variable (Q) (u u'' : Fin 2 → ι → K)

@[expose] noncomputable def frP (A : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  frCol u * A * frRow Q u''

@[expose] noncomputable def frQ (A : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  frCol u'' * A * frRow Q u

@[expose] noncomputable def frR (T : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  frCol u * T * frRow Q u

@[expose] noncomputable def frD (a b : Matrix (Fin 2) (Fin 2) K) : Matrix ι ι K :=
  1 + frP Q u u'' a + frQ Q u u'' b

variable {Q u u''}

theorem frP_add (A A' : Matrix (Fin 2) (Fin 2) K) :
    frP Q u u'' (A + A') = frP Q u u'' A + frP Q u u'' A' := by
  rw [frP, frP, frP, Matrix.mul_add, Matrix.add_mul]

theorem frQ_add (A A' : Matrix (Fin 2) (Fin 2) K) :
    frQ Q u u'' (A + A') = frQ Q u u'' A + frQ Q u u'' A' := by
  rw [frQ, frQ, frQ, Matrix.mul_add, Matrix.add_mul]

theorem frR_add (T T' : Matrix (Fin 2) (Fin 2) K) :
    frR Q u (T + T') = frR Q u T + frR Q u T' := by
  rw [frR, frR, frR, Matrix.mul_add, Matrix.add_mul]

theorem frP_zero : frP Q u u'' 0 = 0 := by rw [frP, Matrix.mul_zero, Matrix.zero_mul]

theorem frQ_zero : frQ Q u u'' 0 = 0 := by rw [frQ, Matrix.mul_zero, Matrix.zero_mul]

namespace SpFrame

variable (hF : SpFrame Q u u'')
include hF

theorem frP_mul_frP (A A' : Matrix (Fin 2) (Fin 2) K) :
    frP Q u u'' A * frP Q u u'' A' = frP Q u u'' (A * A') := by
  rw [frP, frP, frP, show frCol u * A * frRow Q u'' * (frCol u * A' * frRow Q u'') =
    frCol u * A * (frRow Q u'' * frCol u) * A' * frRow Q u'' by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_dual, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem frQ_mul_frQ (A A' : Matrix (Fin 2) (Fin 2) K) :
    frQ Q u u'' A * frQ Q u u'' A' = frQ Q u u'' (A * A') := by
  rw [frQ, frQ, frQ, show frCol u'' * A * frRow Q u * (frCol u'' * A' * frRow Q u) =
    frCol u'' * A * (frRow Q u * frCol u'') * A' * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_dual', Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem frP_mul_frQ (A A' : Matrix (Fin 2) (Fin 2) K) :
    frP Q u u'' A * frQ Q u u'' A' = 0 := by
  rw [frP, frQ, show frCol u * A * frRow Q u'' * (frCol u'' * A' * frRow Q u) =
    frCol u * A * (frRow Q u'' * frCol u'') * A' * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_self', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem frQ_mul_frP (A A' : Matrix (Fin 2) (Fin 2) K) :
    frQ Q u u'' A * frP Q u u'' A' = 0 := by
  rw [frP, frQ, show frCol u'' * A * frRow Q u * (frCol u * A' * frRow Q u'') =
    frCol u'' * A * (frRow Q u * frCol u) * A' * frRow Q u'' by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem frP_mul_frR (A T : Matrix (Fin 2) (Fin 2) K) :
    frP Q u u'' A * frR Q u T = frR Q u (A * T) := by
  rw [frP, frR, frR, show frCol u * A * frRow Q u'' * (frCol u * T * frRow Q u) =
    frCol u * A * (frRow Q u'' * frCol u) * T * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_dual, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem frR_mul_frQ (T A : Matrix (Fin 2) (Fin 2) K) :
    frR Q u T * frQ Q u u'' A = frR Q u (T * A) := by
  rw [frQ, frR, frR, show frCol u * T * frRow Q u * (frCol u'' * A * frRow Q u) =
    frCol u * T * (frRow Q u * frCol u'') * A * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_dual', Matrix.mul_one]
  simp only [Matrix.mul_assoc]

theorem frR_mul_frP (T A : Matrix (Fin 2) (Fin 2) K) :
    frR Q u T * frP Q u u'' A = 0 := by
  rw [frP, frR, show frCol u * T * frRow Q u * (frCol u * A * frRow Q u'') =
    frCol u * T * (frRow Q u * frCol u) * A * frRow Q u'' by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem frQ_mul_frR (A T : Matrix (Fin 2) (Fin 2) K) :
    frQ Q u u'' A * frR Q u T = 0 := by
  rw [frQ, frR, show frCol u'' * A * frRow Q u * (frCol u * T * frRow Q u) =
    frCol u'' * A * (frRow Q u * frCol u) * T * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem frR_mul_frR (T T' : Matrix (Fin 2) (Fin 2) K) : frR Q u T * frR Q u T' = 0 := by
  rw [frR, frR, show frCol u * T * frRow Q u * (frCol u * T' * frRow Q u) =
    frCol u * T * (frRow Q u * frCol u) * T' * frRow Q u by simp only [Matrix.mul_assoc],
    hF.frRow_mul_frCol_self, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

theorem frD_mul (a b c d : Matrix (Fin 2) (Fin 2) K) :
    frD Q u u'' a b * frD Q u u'' c d = frD Q u u'' (a + c + a * c) (b + d + b * d) := by
  simp only [frD, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    hF.frP_mul_frP, hF.frQ_mul_frQ, hF.frP_mul_frQ, hF.frQ_mul_frP, frP_add, frQ_add, add_zero]
  abel

theorem frD_mul_frR (a b T : Matrix (Fin 2) (Fin 2) K) :
    frD Q u u'' a b * frR Q u T = frR Q u ((1 + a) * T) := by
  rw [frD, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, hF.frP_mul_frR, hF.frQ_mul_frR,
    add_zero, Matrix.add_mul, Matrix.one_mul, frR_add]

theorem frR_mul_frD (a b T : Matrix (Fin 2) (Fin 2) K) :
    frR Q u T * frD Q u u'' a b = frR Q u (T * (1 + b)) := by
  rw [frD, Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, hF.frR_mul_frP, hF.frR_mul_frQ,
    add_zero, Matrix.mul_add, Matrix.mul_one, frR_add]

end SpFrame

theorem polarBilin_frP_mulVec (A : Matrix (Fin 2) (Fin 2) K) (v w : ι → K) :
    Q.polarBilin (frP Q u u'' A *ᵥ v) w = Q.polarBilin v (frQ Q u u'' Aᵀ *ᵥ w) := by
  rw [frP, frQ, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    polarBilin_frCol_mulVec_left, polarBilin_frCol_mulVec_right, dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem polarBilin_frQ_mulVec (A : Matrix (Fin 2) (Fin 2) K) (v w : ι → K) :
    Q.polarBilin (frQ Q u u'' A *ᵥ v) w = Q.polarBilin v (frP Q u u'' Aᵀ *ᵥ w) := by
  rw [frP, frQ, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    polarBilin_frCol_mulVec_left, polarBilin_frCol_mulVec_right, dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem polarBilin_frR_mulVec (T : Matrix (Fin 2) (Fin 2) K) (v w : ι → K) :
    Q.polarBilin (frR Q u T *ᵥ v) w = Q.polarBilin v (frR Q u Tᵀ *ᵥ w) := by
  rw [frR, frR, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    polarBilin_frCol_mulVec_left, polarBilin_frCol_mulVec_right, dotProduct_comm,
    Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

theorem polarBilin_frD_mulVec (a b : Matrix (Fin 2) (Fin 2) K) (v w : ι → K) :
    Q.polarBilin (frD Q u u'' a b *ᵥ v) w = Q.polarBilin v (frD Q u u'' bᵀ aᵀ *ᵥ w) := by
  rw [frD, frD, add_mulVec, add_mulVec, one_mulVec, map_add, map_add, LinearMap.add_apply,
    LinearMap.add_apply, polarBilin_frP_mulVec, polarBilin_frQ_mulVec, add_mulVec, add_mulVec,
    one_mulVec, map_add, map_add]
  abel

@[expose] noncomputable def frLeviMat (Q : QuadraticForm K (ι → K)) (u u'' : Fin 2 → ι → K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix ι ι K :=
  frD Q u u'' ((g : Matrix (Fin 2) (Fin 2) K) - 1)
    (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ - 1)

theorem frLeviMat_one : frLeviMat Q u u'' 1 = 1 := by
  simp only [frLeviMat, inv_one, Matrix.SpecialLinearGroup.coe_one, transpose_one, sub_self, frD,
    frP_zero, frQ_zero, add_zero]

theorem SpFrame.frLeviMat_mul (hF : SpFrame Q u u'') (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    frLeviMat Q u u'' (g * h) = frLeviMat Q u u'' g * frLeviMat Q u u'' h := by
  rw [frLeviMat, frLeviMat, frLeviMat, hF.frD_mul, _root_.mul_inv_rev]
  simp only [Matrix.SpecialLinearGroup.coe_mul, transpose_mul]
  congr 1 <;> noncomm_ring

@[expose] noncomputable def SpFrame.frLevi (hF : SpFrame Q u u'') :
    Matrix.SpecialLinearGroup (Fin 2) K →* GL ι K where
  toFun g := ⟨frLeviMat Q u u'' g, frLeviMat Q u u'' g⁻¹,
    by rw [← hF.frLeviMat_mul, mul_inv_cancel, frLeviMat_one],
    by rw [← hF.frLeviMat_mul, inv_mul_cancel, frLeviMat_one]⟩
  map_one' := Units.ext frLeviMat_one
  map_mul' g h := Units.ext (hF.frLeviMat_mul g h)

theorem SpFrame.coe_frLevi (hF : SpFrame Q u u'') (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (hF.frLevi g : Matrix ι ι K) = frLeviMat Q u u'' g := rfl

theorem SpFrame.coe_frLevi_inv (hF : SpFrame Q u u'') (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((hF.frLevi g)⁻¹ : GL ι K) = (frLeviMat Q u u'' g⁻¹ : Matrix ι ι K) := by
  rw [← map_inv]
  rfl

theorem SpFrame.polarBilin_frLevi_mulVec (hF : SpFrame Q u u'')
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (v w : ι → K) :
    Q.polarBilin ((hF.frLevi g : Matrix ι ι K) *ᵥ v) ((hF.frLevi g : Matrix ι ι K) *ᵥ w) =
      Q.polarBilin v w := by
  obtain ⟨G, hG⟩ : ∃ G, G = (g : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  obtain ⟨Gi, hGi⟩ : ∃ Gi,
      Gi = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    ⟨_, rfl⟩
  have hgg : Gi * G = 1 := by
    rw [hG, hGi]
    simp only [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hgg' : Gᵀ * Giᵀ = 1 := by rw [← transpose_mul, hgg, transpose_one]
  rw [SpFrame.coe_frLevi, frLeviMat, ← hGi, ← hG, polarBilin_frD_mulVec, mulVec_mulVec,
    hF.frD_mul]
  have h1 : (Giᵀ - 1)ᵀ + (G - 1) + (Giᵀ - 1)ᵀ * (G - 1) = 0 := by
    rw [transpose_sub, transpose_transpose, transpose_one]
    calc Gi - 1 + (G - 1) + (Gi - 1) * (G - 1) = Gi * G - 1 := by noncomm_ring
      _ = 0 := by rw [hgg, sub_self]
  have h2 : (G - 1)ᵀ + (Giᵀ - 1) + (G - 1)ᵀ * (Giᵀ - 1) = 0 := by
    rw [transpose_sub, transpose_one]
    calc Gᵀ - 1 + (Giᵀ - 1) + (Gᵀ - 1) * (Giᵀ - 1) = Gᵀ * Giᵀ - 1 := by noncomm_ring
      _ = 0 := by rw [hgg', sub_self]
  rw [h1, h2, frD, frP_zero, frQ_zero, add_zero, add_zero, one_mulVec]

theorem SpFrame.frLevi_mul_frR_mul_frLevi_inv (hF : SpFrame Q u u'')
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (T : Matrix (Fin 2) (Fin 2) K) :
    (hF.frLevi g : Matrix ι ι K) * frR Q u T * ((hF.frLevi g)⁻¹ : GL ι K) =
      frR Q u ((g : Matrix (Fin 2) (Fin 2) K) * T * (g : Matrix (Fin 2) (Fin 2) K)ᵀ) := by
  rw [SpFrame.coe_frLevi_inv, SpFrame.coe_frLevi, frLeviMat, frLeviMat, hF.frD_mul_frR,
    hF.frR_mul_frD, _root_.inv_inv, add_sub_cancel, add_sub_cancel]

@[expose] def frH (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem mul_frH [CharP K 2] (g : Matrix (Fin 2) (Fin 2) K) :
    g * frH K = frH K * (adjugate g)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frH, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem SpFrame.frLevi_mul_frR_frH [CharP K 2] (hF : SpFrame Q u u'')
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (hF.frLevi g : Matrix ι ι K) * frR Q u (frH K) = frR Q u (frH K) * hF.frLevi g := by
  rw [SpFrame.coe_frLevi, frLeviMat, hF.frD_mul_frR, hF.frR_mul_frD, add_sub_cancel,
    add_sub_cancel, mul_frH]
  simp only [Matrix.SpecialLinearGroup.coe_inv]

end CFSG.ComponentClassification.RankTwoClassical
