module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open Matrix

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private theorem sum_interval_eq_sum_fin {n k b : ℕ} (hbk : b + k ≤ n)
    (f : Fin n → K) (hf : ∀ p : Fin n, (p.val < b ∨ b + k ≤ p.val) → f p = 0) :
    ∑ p : Fin n, f p = ∑ t : Fin k, f (⟨b + t.val, by omega⟩ : Fin n) := by
  let emb : Fin k → Fin n := fun t => ⟨b + t.val, by omega⟩
  have hemb : Function.Injective emb := by
    intro s t h
    apply Fin.ext
    have := congrArg Fin.val h
    simp [emb] at this
    omega
  have hzero : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      p ∉ Finset.univ.image emb → f p = 0 := by
    intro p _ hp
    apply hf p
    by_contra h
    apply hp
    have hge : b ≤ p.val := by omega
    have hlt : p.val < b + k := by omega
    let t : Fin k := ⟨p.val - b, by omega⟩
    refine Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [emb, t]
    omega
  calc ∑ p : Fin n, f p
      = ∑ p ∈ Finset.univ.image emb, f p := by
          rw [Finset.sum_subset (s₁ := Finset.univ.image emb) (s₂ := Finset.univ)
            (Finset.subset_univ _) hzero]
    _ = ∑ t : Fin k, f (emb t) := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          exact hemb hab

private theorem interval_submatrix_unitary {n k b : ℕ} (hbk : b + k ≤ n)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : conjTr (unitaryInvolution K 2 1) A * A = 1)
    (hoff : ∀ (i : Fin n) (j : Fin k),
      (i.val < b ∨ b + k ≤ i.val) → A i ⟨b + j.val, by omega⟩ = 0) :
    conjTr (unitaryInvolution K 2 1)
        (Matrix.of fun i j : Fin k => A ⟨b + i.val, by omega⟩ ⟨b + j.val, by omega⟩) *
      (Matrix.of fun i j : Fin k => A ⟨b + i.val, by omega⟩ ⟨b + j.val, by omega⟩) = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  have hglobal := congrFun (congrFun hA (⟨b + i.val, by omega⟩ : Fin n))
    (⟨b + j.val, by omega⟩ : Fin n)
  rw [Matrix.mul_apply] at hglobal
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply] at hglobal
  have hone : (1 : Matrix (Fin k) (Fin k) K) i j =
      (1 : Matrix (Fin n) (Fin n) K)
        (⟨b + i.val, by omega⟩ : Fin n) (⟨b + j.val, by omega⟩ : Fin n) := by
    simp [Matrix.one_apply, Fin.ext_iff]
  rw [hone, ← hglobal]
  exact (sum_interval_eq_sum_fin (b := b) (k := k) hbk
    (fun p => unitaryInvolution K 2 1 (A p ⟨b + i.val, by omega⟩) *
      A p ⟨b + j.val, by omega⟩)
    (fun p hp => by rw [hoff p j hp, mul_zero])).symm


private theorem matrix_diag_mul_SU_factor {k : ℕ} (hk : 0 < k)
    {B : Matrix (Fin k) (Fin k) K}
    (hB : conjTr (unitaryInvolution K 2 1) B * B = 1) :
    ∃ (d : Fin k → normOne (unitaryInvolution K 2 1)) (u : SUid (unitaryInvolution K 2 1) k),
      ∀ i j : Fin k,
        B i j = (((d i : normOne (unitaryInvolution K 2 1)) : Kˣ) : K) *
          (((u : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) i j) := by
  classical
  let σ := unitaryInvolution K 2 1
  have hdetconj : (conjTr σ B).det = σ B.det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (σ : K →+* K) B).symm
  have hσdet : σ B.det * B.det = 1 := by
    have h := congrArg Matrix.det hB
    rw [Matrix.det_mul, hdetconj, Matrix.det_one] at h
    exact h
  have hdet_ne : B.det ≠ 0 := by
    have h : B.det * σ B.det = 1 := by
      rw [mul_comm]
      exact hσdet
    exact left_ne_zero_of_mul_eq_one h
  let d0 : normOne σ :=
    ⟨Units.mk0 B.det hdet_ne, (mem_normOne σ).mpr (by simpa using hσdet)⟩
  have hd0_val : (((d0 : normOne σ) : Kˣ) : K) = B.det := Units.val_mk0 hdet_ne
  let k0 : Fin k := ⟨0, hk⟩
  let d : Fin k → normOne σ := Pi.mulSingle k0 d0
  have hdk : d k0 = d0 := by simp [d]
  let D : Matrix (Fin k) (Fin k) K :=
    Matrix.diagonal fun i => (((d i : normOne σ) : Kˣ) : K)
  let Dinv : Matrix (Fin k) (Fin k) K :=
    Matrix.diagonal fun i => ((((d i : normOne σ) : Kˣ) : K))⁻¹
  let S : Matrix (Fin k) (Fin k) K := Dinv * B
  have hDmul : D * Dinv = 1 := by
    show Matrix.diagonal (fun i => (((d i : normOne σ) : Kˣ) : K)) *
        Matrix.diagonal (fun i => ((((d i : normOne σ) : Kˣ) : K))⁻¹) = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Units.ne_zero ((d i : normOne σ) : Kˣ))
  have hDinvuni : conjTr σ Dinv * Dinv = 1 := by
    show conjTr σ (Matrix.diagonal (fun i => ((((d i : normOne σ) : Kˣ) : K))⁻¹)) *
        Matrix.diagonal (fun i => ((((d i : normOne σ) : Kˣ) : K))⁻¹) = 1
    rw [conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h0 : σ ((((d i : normOne σ) : Kˣ) : K)) *
        ((((d i : normOne σ) : Kˣ) : K)) = 1 :=
      (mem_normOne σ).mp (d i).2
    rw [map_inv₀, ← mul_inv, h0, inv_one]
  have huniS : conjTr σ S * S = 1 := by
    have hcalc : conjTr σ B * (conjTr σ Dinv * Dinv) * B = 1 := by
      rw [hDinvuni, Matrix.mul_one, hB]
    show conjTr σ (Dinv * B) * (Dinv * B) = 1
    rw [conjTr_mul]
    calc conjTr σ B * conjTr σ Dinv * (Dinv * B)
        = conjTr σ B * (conjTr σ Dinv * (Dinv * B)) := Matrix.mul_assoc _ _ _
      _ = conjTr σ B * ((conjTr σ Dinv * Dinv) * B) := by
            rw [← Matrix.mul_assoc (conjTr σ Dinv) Dinv B]
      _ = conjTr σ B * (conjTr σ Dinv * Dinv) * B := by
            rw [Matrix.mul_assoc (conjTr σ B) (conjTr σ Dinv * Dinv) B]
      _ = 1 := hcalc
  have hdetDinv : Dinv.det = (B.det)⁻¹ := by
    show (Matrix.diagonal (fun i => ((((d i : normOne σ) : Kˣ) : K))⁻¹)).det = (B.det)⁻¹
    rw [Matrix.det_diagonal, Finset.prod_eq_single k0]
    · rw [hdk, hd0_val]
    · intro i _ hi
      have hdi : d i = 1 := by
        simp [d, Pi.mulSingle_eq_of_ne hi]
      rw [hdi]
      simp
    · intro h
      exact absurd (Finset.mem_univ k0) h
  have hdetS : S.det = 1 := by
    show (Dinv * B).det = 1
    rw [Matrix.det_mul, hdetDinv]
    exact inv_mul_cancel₀ hdet_ne
  have hisoS : ∀ x y : Fin k → K,
      herm σ (S *ᵥ x) (S *ᵥ y) = herm σ x y := by
    intro x y
    rw [herm_mulVec, huniS, Matrix.one_mulVec]
  let u : SUid σ k := mkSU σ S hdetS hisoS
  have hDS : D * S = B := by
    show D * (Dinv * B) = B
    rw [← Matrix.mul_assoc, hDmul, Matrix.one_mul]
  refine ⟨d, u, fun i j => ?_⟩
  have hBentry : B i j = (D * S) i j := by rw [hDS]
  rw [hBentry]
  change (Matrix.diagonal (fun i => (((d i : normOne σ) : Kˣ) : K)) * S) i j = _
  rw [Matrix.diagonal_mul]
  rfl


theorem qTwo_unitary_interval_factor (n k b : ℕ) (hk : 0 < k) (hbk : b + k ≤ n)
    (A : Matrix (Fin n) (Fin n) K)
    (hA : conjTr (unitaryInvolution K 2 1) A * A = 1)
    (hoff : ∀ (i : Fin n) (j : Fin k),
      (i.val < b ∨ b + k ≤ i.val) → A i ⟨b + j.val, by omega⟩ = 0) :
    ∃ (d : Fin k → normOne (unitaryInvolution K 2 1)) (u : Su K 2 1 k),
      ∀ i j : Fin k,
        A (⟨b + i.val, by omega⟩ : Fin n) (⟨b + j.val, by omega⟩ : Fin n) =
          (((d i : Kˣ) : K) *
            (((u : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) i j)) := by
  classical
  let B : Matrix (Fin k) (Fin k) K :=
    Matrix.of fun i j => A ⟨b + i.val, by omega⟩ ⟨b + j.val, by omega⟩
  have hB : conjTr (unitaryInvolution K 2 1) B * B = 1 := by
    simpa [B] using interval_submatrix_unitary (K := K) hbk A hA hoff
  obtain ⟨d, u, hfac⟩ := matrix_diag_mul_SU_factor (K := K) hk hB
  exact ⟨d, u, fun i j => by simpa [B] using hfac i j⟩


end CFSG.ClassicalInvolution.PhanDn.QTwo
