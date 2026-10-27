module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODEigen
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.Charpoly.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

namespace I294OD

open Polynomial Matrix

theorem minpoly_eq_of_pow_eq {K A : Type*} [Field K] [Ring A] [Algebra K A] [Nontrivial A]
    {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : ∀ b : K, b ^ p ≠ ζ) {M : A}
    (hM : M ^ p = algebraMap K A ζ) : minpoly K M = X ^ p - C ζ := by
  refine (minpoly.eq_of_irreducible_of_monic (X_pow_sub_C_irreducible_of_prime hp hζ) ?_
    (monic_X_pow_sub_C ζ hp.ne_zero)).symm
  simp only [map_sub, map_pow, aeval_X, aeval_C, hM, sub_self]

theorem det_eq_of_pow_eq {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : K}
    (hζ : ∀ b : K, b ^ p ≠ ζ) {M : Matrix (Fin p) (Fin p) K}
    (hM : M ^ p = scalar (Fin p) ζ) : M.det = ζ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hM' : M ^ p = algebraMap K (Matrix (Fin p) (Fin p) K) ζ := by
    rw [hM]; rfl
  have hmin := minpoly_eq_of_pow_eq hp hζ hM'
  have hdvd : X ^ p - C ζ ∣ M.charpoly := by
    rw [← hmin]
    exact minpoly.dvd K M (Matrix.aeval_self_charpoly M)
  have hdeg : M.charpoly.natDegree = p := by simp
  have heq : M.charpoly = X ^ p - C ζ :=
    eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow_sub_C ζ hp.ne_zero) (Matrix.charpoly_monic M)
      hdvd (by rw [hdeg, natDegree_X_pow_sub_C])
  have h0 : (X ^ p - C ζ).coeff 0 = -ζ := by
    rw [coeff_sub, coeff_X_pow, coeff_C_zero, if_neg hp.ne_zero.symm, zero_sub]
  rw [Matrix.det_eq_sign_charpoly_coeff, heq, h0, Fintype.card_fin,
    Odd.neg_one_pow (hp.odd_of_ne_two hp2), neg_mul, one_mul, neg_neg]

theorem scalar_of_commute {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K - 1) {ζ : K} (hζ : ∀ b : K, b ^ p ≠ ζ)
    {A M : Matrix (Fin p) (Fin p) K} (hM : M ^ p = scalar (Fin p) ζ) (hA : A ^ p = 1)
    (hAM : A * M = M * A) : ∃ μ : K, A = scalar (Fin p) μ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ωu, hωu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  have hprimU : IsPrimitiveRoot ωu p := by
    rw [← hωu]
    exact IsPrimitiveRoot.orderOf ωu
  have hprim : IsPrimitiveRoot (ωu : K) p :=
    hprimU.map_of_injective (f := Units.coeHom K) Units.val_injective
  haveI : NeZero (p : K) := hprim.neZero'
  obtain ⟨P, Q, u, hPQ, hQP, hAP⟩ := exists_eigenbasis_matrix A
    (top_le_span_eigenvectors A hprim hp.pos (NeZero.ne _) hA)
  set i0 : Fin p := ⟨0, hp.pos⟩ with hi0
  set μ : K := u i0 with hμ
  set v : Fin p → K := fun i => P i i0 with hvdef
  have hv : A *ᵥ v = μ • v := by
    funext i
    have h := congrFun (congrFun hAP i) i0
    rw [Matrix.mul_diagonal] at h
    have e : (A *ᵥ v) i = (A * P) i i0 := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hvdef]
    rw [e, h]
    simp [hvdef, hμ, mul_comm]
  have hv0 : v ≠ 0 := by
    intro h
    have h1 := congrFun (congrFun hQP i0) i0
    have h2 : (Q * P) i0 i0 = 0 := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : P k i0 = 0 := congrFun h k
      rw [this, mul_zero]
    rw [h1] at h2
    simp at h2
  let W : Submodule K (Fin p → K) := LinearMap.ker (Matrix.toLin' A - μ • LinearMap.id)
  have hmemW : ∀ w, w ∈ W ↔ A *ᵥ w = μ • w := by
    intro w
    simp [W, LinearMap.mem_ker, sub_eq_zero, Matrix.toLin'_apply]
  have hvW : v ∈ W := (hmemW v).2 hv
  have hinv : ∀ w ∈ W, (Matrix.toLin' M) w ∈ W := by
    intro w hw
    rw [hmemW] at hw ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hAM, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_smul]
  haveI : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  let BW : Module.End K W := (Matrix.toLin' M).restrict hinv
  have hBW : BW ^ p = algebraMap K (Module.End K W) ζ := by
    have h1 : (Matrix.toLin' M) ^ p = algebraMap K (Module.End K (Fin p → K)) ζ := by
      have hc := AlgEquiv.commutes (Matrix.toLinAlgEquiv' (R := K) (n := Fin p)) ζ
      rw [show (Matrix.toLin' M) = Matrix.toLinAlgEquiv' M from rfl, ← map_pow, hM]
      exact hc
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    have h2 := Module.End.pow_restrict (f' := Matrix.toLin' M) p hinv
    have h4 : ((BW ^ p) w : Fin p → K) = ((Matrix.toLin' M) ^ p) (w : Fin p → K) := by
      rw [show BW = (Matrix.toLin' M).restrict hinv from rfl, h2]
      rfl
    rw [h4, h1]
    simp
  have hmin := minpoly_eq_of_pow_eq (A := Module.End K W) hp hζ hBW
  have hdvd : X ^ p - C ζ ∣ BW.charpoly := by
    rw [← hmin]
    exact minpoly.dvd K BW (LinearMap.aeval_self_charpoly BW)
  have hle : p ≤ Module.finrank K W := by
    have h1 := Polynomial.natDegree_le_of_dvd hdvd (LinearMap.charpoly_monic BW).ne_zero
    rwa [natDegree_X_pow_sub_C, LinearMap.charpoly_natDegree] at h1
  have hfin : Module.finrank K W ≤ p := by
    have := Submodule.finrank_le W
    simpa using this
  have htop : W = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by simpa using le_antisymm hfin hle)
  refine ⟨μ, Matrix.ext fun i j => ?_⟩
  have h1 := (hmemW (Pi.single j 1)).1 (htop ▸ Submodule.mem_top)
  have h2 := congrFun h1 i
  rw [Matrix.mulVec_single_one] at h2
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simpa using h2
  · simp only [hij, if_false]
    simpa [Pi.single_apply, hij] using h2

end I294OD

end CFSG.LocalAnalysis.RankFourTheoremC
