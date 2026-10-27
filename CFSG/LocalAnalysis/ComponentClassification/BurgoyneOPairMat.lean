module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOPairNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEAlg
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFamily
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneORes

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

variable {K : Type} [Field K] {d : ℕ}

@[expose] def plVec (A : Matrix (Fin d) (Fin d) K) (v : Fin d → K) (a : Fin 2) : Fin d → K :=
  if a = 0 then v else A *ᵥ v

@[expose] def plGram (R A : Matrix (Fin d) (Fin d) K) (v : Fin d → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun a b => plVec A v a ⬝ᵥ R *ᵥ plVec A v b

theorem plGram_det (R A : Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    (plGram R A v).det = (v ⬝ᵥ R *ᵥ v) * ((A *ᵥ v) ⬝ᵥ R *ᵥ (A *ᵥ v)) -
      (v ⬝ᵥ R *ᵥ (A *ᵥ v)) * ((A *ᵥ v) ⬝ᵥ R *ᵥ v) := by
  rw [det_fin_two]
  simp [plGram, plVec]

@[expose] def pairMat {n : ℕ} (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
    (u : Fin n → Fin (2 * n) → K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K :=
  Matrix.of fun r q => plVec A (u ((pairEquiv n).symm q).1) ((pairEquiv n).symm q).2 r

theorem pairMat_apply {n : ℕ} (A : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
    (u : Fin n → Fin (2 * n) → K) (r : Fin (2 * n)) (i : Fin n) (a : Fin 2) :
    pairMat A u r (pairEquiv n (i, a)) = plVec A (u i) a r := by
  simp [pairMat]

theorem pairMat_gram {n : ℕ} (R A : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
    (u : Fin n → Fin (2 * n) → K) (i k : Fin n) (a b : Fin 2) :
    ((pairMat A u)ᵀ * R * pairMat A u) (pairEquiv n (i, a)) (pairEquiv n (k, b)) =
      plVec A (u i) a ⬝ᵥ R *ᵥ plVec A (u k) b := by
  simp only [Matrix.mul_apply, transpose_apply, pairMat_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable {n : ℕ} {R A : Matrix (Fin (2 * n)) (Fin (2 * n)) K} {c ε : K}

theorem pairMat_gram_eq (hR : Rᵀ = R) (hA2 : A * A = c • 1) (hAR : Aᵀ * R = ε • (R * A))
    {u : Fin n → Fin (2 * n) → K} (hu : PairFam R A u) :
    (pairMat A u)ᵀ * R * pairMat A u = blkEquiv K n (diagonal fun i => plGram R A (u i)) := by
  ext p q
  obtain ⟨⟨i, a⟩, rfl⟩ := (pairEquiv n).surjective p
  obtain ⟨⟨k, b⟩, rfl⟩ := (pairEquiv n).surjective q
  rw [pairMat_gram, blkEquiv_apply, diagonal_apply]
  split_ifs with hik
  · subst hik
    rfl
  · change _ = 0
    fin_cases a <;> fin_cases b <;> simp only [plVec, Fin.zero_eta, Fin.mk_one, ↓reduceIte,
      one_ne_zero]
    · exact hu.orth i k hik
    · exact hu.orthA i k hik
    · rw [dot_symm hR]
      exact hu.orthA k i (Ne.symm hik)
    · rw [dot_adj hAR, mulVec_mulVec_self hA2, mulVec_smul, dotProduct_smul, smul_eq_mul,
        hu.orth i k hik, mul_zero, mul_zero]

theorem mul_pairMat (hA2 : A * A = c • 1) (u : Fin n → Fin (2 * n) → K) :
    A * pairMat A u = pairMat A u * blkDiag n (jMat c) := by
  ext r q
  obtain ⟨⟨i, b⟩, rfl⟩ := (pairEquiv n).surjective q
  have hL : (A * pairMat A u) r (pairEquiv n (i, b)) = (A *ᵥ plVec A (u i) b) r := by
    simp only [Matrix.mul_apply, pairMat_apply, mulVec, dotProduct]
  have hR' : (pairMat A u * blkDiag n (jMat c)) r (pairEquiv n (i, b)) =
      ∑ a : Fin 2, plVec A (u i) a r * jMat c a b := by
    rw [Matrix.mul_apply, ← (pairEquiv n).sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single i]
    · simp only [pairMat_apply, blkDiag_apply, ↓reduceIte]
    · intro k _ hk
      simp [blkDiag_apply, hk]
    · simp
  rw [hL, hR', Fin.sum_univ_two]
  fin_cases b <;> simp [plVec, jMat, mulVec_mulVec_self hA2, mul_comm]

theorem pairMat_det_ne_zero (hR : Rᵀ = R) (hA2 : A * A = c • 1) (hAR : Aᵀ * R = ε • (R * A))
    {u : Fin n → Fin (2 * n) → K} (hu : PairFam R A u)
    (hpair : ∀ i, (plGram R A (u i)).det ≠ 0) : (pairMat A u).det ≠ 0 := by
  have hmul : blkEquiv K n (diagonal fun i => plGram R A (u i)) *
      blkEquiv K n (diagonal fun i => (plGram R A (u i))⁻¹) = 1 := by
    rw [← map_mul, diagonal_mul_diagonal]
    have : (fun i => plGram R A (u i) * (plGram R A (u i))⁻¹) = fun _ => 1 := by
      funext i
      exact mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hpair i))
    rw [this, diagonal_one, map_one]
  have hdet : (blkEquiv K n (diagonal fun i => plGram R A (u i))).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  rw [← pairMat_gram_eq hR hA2 hAR hu, det_mul, det_mul] at hdet
  intro h0
  rw [h0, mul_zero] at hdet
  exact hdet rfl

theorem exists_transport_of_gram {R R' H : GL (Fin d) K}
    (hgram : (H : Matrix (Fin d) (Fin d) K)ᵀ * R * H = R') {g : similarityPairs (oQ R)}
    (hg1 : g.val.right = 1) :
    ∃ hS : ∀ v, oQ R' (((H⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
        ((1 : Kˣ) : K) * oQ R v,
      (transPair H⁻¹ 1 hS g).val.left = H⁻¹ * g.val.left * H ∧
        (transPair H⁻¹ 1 hS g).val.right = 1 := by
  have hHHi : (H : Matrix (Fin d) (Fin d) K) * ((H⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hS : ∀ v, oQ R' (((H⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ v) =
      ((1 : Kˣ) : K) * oQ R v := by
    intro v
    rw [oQ_apply, oQ_apply, ← hgram, dotProduct_transpose_mul_mul, mulVec_mulVec, hHHi,
      one_mulVec, Units.val_one, one_mul]
  refine ⟨hS, ?_, ?_⟩
  · rw [transPair_left, hg1, map_one, MulAut.one_apply, inv_inv]
  · exact hg1

end CFSG.ComponentClassification.Burgoyne.O
