module

public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K}

theorem herm_map_of_isKLinear (E : QuadExt F K σ) {n : ℕ}
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (hK : ∀ (a : K) x, g (a • x) = a • g x) (x y : Fin n → K) :
    herm σ (g x) (g y) = herm σ x y := by
  have hσ : ∀ c, σ (σ c) = c := E.isUnitary.invol
  have hpolar : ∀ u v : Fin n → K,
      algebraMap F K (polar (Qn E n) u v) = herm σ v u + herm σ u v := by
    intro u v
    rw [algebraMap_polar_Qn]
    have h1 : (∑ i, u i * σ (v i)) = herm σ v u := by
      rw [herm_def]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : herm σ u v = σ (herm σ v u) := herm_conj σ hσ v u
    rw [h1, h2]
  have hmain : ∀ u : Fin n → K,
      herm σ (g u) (g y) + σ (herm σ (g u) (g y)) =
        herm σ u y + σ (herm σ u y) := by
    intro u
    have h := hpolar (g u) (g y)
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg u y, hpolar u y] at h
    have h' := h
    rw [herm_conj σ hσ (g u) (g y), herm_conj σ hσ u y] at h'
    rw [add_comm (herm σ (g u) (g y)) (σ (herm σ (g u) (g y))),
      add_comm (herm σ u y) (σ (herm σ u y))]
    exact h'.symm
  have hscale : ∀ a : K,
      σ a * (herm σ (g x) (g y) - herm σ x y) +
        σ (σ a * (herm σ (g x) (g y) - herm σ x y)) = 0 := by
    intro a
    have h := hmain (a • x)
    have hga : herm σ (g (a • x)) (g y) - herm σ (a • x) y =
        σ a * (herm σ (g x) (g y) - herm σ x y) := by
      rw [hK a x, herm_smul_left, herm_smul_left, mul_sub]
    have hzero : (herm σ (g (a • x)) (g y) - herm σ (a • x) y) +
        σ (herm σ (g (a • x)) (g y) - herm σ (a • x) y) = 0 := by
      rw [map_sub]
      linear_combination h
    rwa [hga] at hzero
  have hd0 : (herm σ (g x) (g y) - herm σ x y) +
      σ (herm σ (g x) (g y) - herm σ x y) = 0 := by
    have h := hmain x
    rw [map_sub]
    linear_combination h
  have hd' : σ (herm σ (g x) (g y) - herm σ x y) =
      -(herm σ (g x) (g y) - herm σ x y) := by
    linear_combination hd0
  have hkey : ∀ a : K,
      (σ a - a) * (herm σ (g x) (g y) - herm σ x y) = 0 := by
    intro a
    have h := hscale a
    rw [map_mul, hσ, hd'] at h
    linear_combination h
  obtain ⟨a, ha⟩ := E.isUnitary.exists_ne
  rcases mul_eq_zero.mp (hkey a) with h | h
  · exact absurd h (sub_ne_zero.mpr ha)
  · exact sub_eq_zero.mp h

theorem exists_diagHom_mul_suEndN_eq (E : QuadExt F K σ) {n : ℕ} (hn : 1 ≤ n)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    (hK : ∀ (a : K) x, g (a • x) = a • g x) :
    ∃ (t : Fin n → normOne σ) (s : SUid σ n),
      diagHom F σ n t * suEndN (F := F) σ n s = g := by
  classical
  let gK : (Fin n → K) →ₗ[K] (Fin n → K) :=
    { toFun := g, map_add' := g.map_add, map_smul' := hK }
  let A : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix' gK
  have hA_apply : ∀ v : Fin n → K, Matrix.mulVec A v = g v := fun v =>
    LinearMap.toMatrix'_mulVec gK v
  have hAherm : ∀ v w : Fin n → K,
      herm σ (Matrix.mulVec A v) (Matrix.mulVec A w) = herm σ v w := by
    intro v w
    rw [hA_apply, hA_apply]
    exact herm_map_of_isKLinear E hg hK v w
  have huni : conjTr σ A * A = 1 := conjTr_mul_self_of_isometry σ hAherm
  have hdetconj : (conjTr σ A).det = σ A.det := by
    rw [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (σ : K →+* K) A).symm
  have hσdet : σ A.det * A.det = 1 := by
    have h := congrArg Matrix.det huni
    rw [Matrix.det_mul, hdetconj, Matrix.det_one] at h
    exact h
  have hdetA_ne : A.det ≠ 0 := by
    have h : A.det * σ A.det = 1 := by
      rw [mul_comm]
      exact hσdet
    exact left_ne_zero_of_mul_eq_one h
  let u : normOne σ :=
    ⟨Units.mk0 A.det hdetA_ne, (mem_normOne σ).mpr (by simpa using hσdet)⟩
  have hu_val : (((u : normOne σ) : Kˣ) : K) = A.det := Units.val_mk0 hdetA_ne
  let k : Fin n := ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
  let t : Fin n → normOne σ := Pi.mulSingle k u
  have ht_def : t = Pi.mulSingle k u := rfl
  have htk : t k = u := by
    rw [ht_def, Pi.mulSingle_eq_same]
  let D : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal fun i => (((t i : normOne σ) : Kˣ) : K)
  let Dinv : Matrix (Fin n) (Fin n) K :=
    Matrix.diagonal fun i => ((((t i : normOne σ) : Kˣ) : K))⁻¹
  let S : Matrix (Fin n) (Fin n) K := Dinv * A
  have hD_def : D = Matrix.diagonal (fun i => (((t i : normOne σ) : Kˣ) : K)) := rfl
  have hDinv_def : Dinv =
      Matrix.diagonal (fun i => ((((t i : normOne σ) : Kˣ) : K))⁻¹) := rfl
  have hS_def : S = Dinv * A := rfl
  have hDmul : D * Dinv = 1 := by
    rw [hD_def, hDinv_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Units.ne_zero ((t i : normOne σ) : Kˣ))
  have hDinvuni : conjTr σ Dinv * Dinv = 1 := by
    rw [hDinv_def, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h0 : σ ((((t i : normOne σ) : Kˣ) : K)) *
        ((((t i : normOne σ) : Kˣ) : K)) = 1 :=
      (mem_normOne σ).mp (t i).2
    rw [map_inv₀, ← mul_inv, h0, inv_one]
  have huniS : conjTr σ S * S = 1 := by
    have hcalc : conjTr σ A * (conjTr σ Dinv * Dinv) * A = 1 := by
      rw [hDinvuni, Matrix.mul_one, huni]
    rw [hS_def, conjTr_mul]
    calc conjTr σ A * conjTr σ Dinv * (Dinv * A)
        = conjTr σ A * (conjTr σ Dinv * (Dinv * A)) := Matrix.mul_assoc _ _ _
      _ = conjTr σ A * ((conjTr σ Dinv * Dinv) * A) := by
            rw [← Matrix.mul_assoc (conjTr σ Dinv) Dinv A]
      _ = conjTr σ A * (conjTr σ Dinv * Dinv) * A := by
            rw [Matrix.mul_assoc (conjTr σ A) (conjTr σ Dinv * Dinv) A]
      _ = 1 := hcalc
  have hdetDinv : Dinv.det = (A.det)⁻¹ := by
    rw [hDinv_def, Matrix.det_diagonal, Finset.prod_eq_single k]
    · rw [htk, hu_val]
    · intro i _ hi
      rw [ht_def, Pi.mulSingle_eq_of_ne hi]
      simp
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hdetS : S.det = 1 := by
    rw [hS_def, Matrix.det_mul, hdetDinv]
    exact inv_mul_cancel₀ hdetA_ne
  have hisoS : ∀ v w : Fin n → K,
      herm σ (Matrix.mulVec S v) (Matrix.mulVec S w) = herm σ v w := by
    intro v w
    rw [herm_mulVec, huniS, Matrix.one_mulVec]
  have hdiagD : ∀ w : Fin n → K, diagHom F σ n t w = Matrix.mulVec D w := by
    intro w
    funext i
    rw [diagHom_apply, hD_def, Matrix.mulVec_diagonal]
  have hDS : D * S = A := by
    rw [hS_def, ← Matrix.mul_assoc, hDmul, Matrix.one_mul]
  refine ⟨t, mkSU σ S hdetS hisoS, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply]
  calc diagHom F σ n t (suEndN (F := F) σ n (mkSU σ S hdetS hisoS) v)
      = diagHom F σ n t (Matrix.mulVec S v) := by
          rw [suEndN_apply (F := F) σ n, mkSU_smul]
    _ = Matrix.mulVec D (Matrix.mulVec S v) := hdiagD _
    _ = Matrix.mulVec (D * S) v := by rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec A v := by rw [hDS]
    _ = g v := hA_apply v

end CFSG.ClassicalInvolution.PhanDn
