module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAlpha
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOrthSplitCType

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap CFSG.Assembly.LowTwoRank CFSG.RankThree.OrthogonalInvolutions
open CFSG.LieType.Universal.Spin
open scoped Matrix

section Forms

variable {ι K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_quadraticForm_eq_zero_on (Q₀ : QuadraticForm K (ι → K))
    (U : Submodule K (ι → K)) (hU : ∀ x ∈ U, ∀ y ∈ U, Q₀.polarBilin x y = 0) :
    ∃ Q : QuadraticForm K (ι → K), Q.polarBilin = Q₀.polarBilin ∧ ∀ x ∈ U, Q x = 0 := by
  set s := (frobeniusEquiv K 2).symm with hs
  have hss : ∀ x : K, s x * s x = x := fun x => by
    have h := frobenius_apply_frobeniusEquiv_symm K 2 x
    rwa [frobenius_def, pow_two] at h
  have hsc : ∀ c : K, s (c * c) = c := fun c => by
    have h := frobeniusEquiv_symm_apply_frobenius K 2 c
    rwa [frobenius_def, pow_two] at h
  let lam₀ : U →ₗ[K] K :=
    { toFun := fun x => s (Q₀ x)
      map_add' := fun x y => by
        rw [Submodule.coe_add, quad_add, hU x x.2 y y.2, add_zero, map_add]
      map_smul' := fun c x => by
        rw [Submodule.coe_smul, QuadraticMap.map_smul, smul_eq_mul, map_mul, hsc,
          RingHom.id_apply, smul_eq_mul] }
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend lam₀
  refine ⟨Q₀ + QuadraticMap.linMulLin lam lam, LinearMap.ext₂ fun x y => ?_, fun x hx => ?_⟩
  · rw [polarBilin_apply_apply, polarBilin_apply_apply, FunLike.coe_add,
      QuadraticMap.polar_add, add_eq_left]
    simp only [QuadraticMap.polar, QuadraticMap.linMulLin_apply, map_add]
    linear_combination (lam x * lam y) * CharTwo.two_eq_zero (R := K)
  · have h1 : lam x = s (Q₀ x) := by
      have h := LinearMap.congr_fun hlam ⟨x, hx⟩
      simpa [lam₀] using h
    rw [FunLike.coe_add, Pi.add_apply, QuadraticMap.linMulLin_apply, h1, hss,
      CharTwo.add_self_eq_zero]

end Forms

section Symplectic

variable {n : ℕ} {K : Type} [Field K]

theorem polarBilin_quadPlus [CharP K 2] (v w : Fin n ⊕ Fin n → K) :
    (quadPlus n K).polarBilin v w = sympForm n K v w := by
  rw [polarBilin_apply_apply, polar_quadPlus]
  simp only [sympForm, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add,
    add_zero, Matrix.neg_mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.neg_apply, Finset.sum_add_distrib, CharTwo.neg_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem mem_statedSp_of_sympForm {X : GL (Fin n ⊕ Fin n) K}
    (h : ∀ v w, sympForm n K ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)
      ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w) = sympForm n K v w) :
    X ∈ StatedSp n K := by
  apply Subgroup.subset_closure
  show (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0
  refine Matrix.ext_iff_mulVec.mpr fun w => funext fun i => ?_
  have key : ∀ v u : Fin n ⊕ Fin n → K,
      ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) ⬝ᵥ u =
        v ⬝ᵥ ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ *ᵥ u) := fun v u => by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have h1 := h (Pi.single i 1) w
  rw [sympForm, sympForm, key, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, single_dotProduct,
    single_dotProduct, one_mul, one_mul] at h1
  exact h1

theorem mem_statedSp_of_polarBilin [CharP K 2] {X : GL (Fin n ⊕ Fin n) K}
    (h : ∀ v w, (quadPlus n K).polarBilin ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)
      ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w) = (quadPlus n K).polarBilin v w) :
    X ∈ StatedSp n K :=
  mem_statedSp_of_sympForm fun v w => by
    rw [← polarBilin_quadPlus, ← polarBilin_quadPlus]
    exact h v w

theorem polarBilin_mulVec_of_mem_statedSp [CharP K 2] {X : GL (Fin n ⊕ Fin n) K}
    (hX : X ∈ StatedSp n K) (v w : Fin n ⊕ Fin n → K) :
    (quadPlus n K).polarBilin ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v)
      ((X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ w) = (quadPlus n K).polarBilin v w := by
  rw [polarBilin_quadPlus, polarBilin_quadPlus]
  exact statedSp_isometry hX v w

end Symplectic

section Involutions

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {B : LinearMap.BilinForm K (ι → K)} {M : GL ι K}
  (hM : ∀ u v, B ((M : Matrix ι ι K) *ᵥ u) ((M : Matrix ι ι K) *ᵥ v) = B u v)
  (hM2 : orderOf M = 2)
include hM hM2

theorem polarBilin_sub_one_adj (u v : ι → K) :
    B (((M : Matrix ι ι K) - 1) *ᵥ u) v = B u (((M : Matrix ι ι K) - 1) *ᵥ v) := by
  have hMM : (M : Matrix ι ι K) * M = 1 := by
    rw [← Units.val_mul, ← _root_.sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
  have h1 : B ((M : Matrix ι ι K) *ᵥ u) v = B u ((M : Matrix ι ι K) *ᵥ v) := by
    conv_lhs => rw [show v = (M : Matrix ι ι K) *ᵥ ((M : Matrix ι ι K) *ᵥ v) by
      rw [mulVec_mulVec, hMM, one_mulVec]]
    exact hM u _
  rw [sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, map_sub, map_sub, LinearMap.sub_apply, h1]

theorem polarBilin_sub_one_sub_one [CharP K 2] (u v : ι → K) :
    B (((M : Matrix ι ι K) - 1) *ᵥ u) (((M : Matrix ι ι K) - 1) *ᵥ v) = 0 := by
  rw [polarBilin_sub_one_adj hM hM2, mulVec_mulVec, sub_one_mul_self_eq_zero hM2, zero_mulVec,
    map_zero]

end Involutions

section Sqrt

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {B : LinearMap.BilinForm K (ι → K)} {N : Matrix ι ι K}

omit [DecidableEq ι] in
theorem exists_sqrt_vector_of_adj (hB : B.Nondegenerate) (hBs : ∀ x y, B x y = B y x)
    (hadj : ∀ u v, B (N *ᵥ u) v = B u (N *ᵥ v)) : ∃ z, ∀ v, B v z ^ 2 = B v (N *ᵥ v) := by
  set s := (frobeniusEquiv K 2).symm with hs
  have hss : ∀ x : K, s x ^ 2 = x := fun x => by
    have h := frobenius_apply_frobeniusEquiv_symm K 2 x
    rwa [frobenius_def] at h
  have hsc : ∀ c : K, s (c * c) = c := fun c => by
    have h := frobeniusEquiv_symm_apply_frobenius K 2 c
    rwa [frobenius_def, pow_two] at h
  let lam : (ι → K) →ₗ[K] K :=
    { toFun := fun v => s (B v (N *ᵥ v))
      map_add' := fun u v => by
        have h2 : B v (N *ᵥ u) = B u (N *ᵥ v) := by rw [hBs, hadj]
        have h1 : B (u + v) (N *ᵥ (u + v)) = B u (N *ᵥ u) + B v (N *ᵥ v) := by
          simp only [mulVec_add, map_add, LinearMap.add_apply, h2]
          linear_combination B u (N *ᵥ v) * CharTwo.two_eq_zero (R := K)
        rw [h1, map_add]
      map_smul' := fun c v => by
        have h1 : B (c • v) (N *ᵥ (c • v)) = (c * c) * B v (N *ᵥ v) := by
          simp only [mulVec_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
          ring
        rw [h1, map_mul, hsc, RingHom.id_apply, smul_eq_mul] }
  refine ⟨(LinearMap.BilinForm.toDual B hB).symm lam, fun v => ?_⟩
  rw [hBs, ← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]
  exact hss _

omit [DecidableEq ι] [Finite K] [CharP K 2] in
theorem mulVec_sqrt_vector_of_adj (hB : B.Nondegenerate) (hN : N * N = 0)
    (hadj : ∀ u v, B (N *ᵥ u) v = B u (N *ᵥ v)) {z : ι → K}
    (hz : ∀ v, B v z ^ 2 = B v (N *ᵥ v)) : N *ᵥ z = 0 := by
  refine hB.2 _ fun w => ?_
  rw [← hadj]
  have h := hz (N *ᵥ w)
  rw [mulVec_mulVec, hN, zero_mulVec, map_zero] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

omit [Finite K] in
theorem mulVec_sqrt_vector_of_commute_adj (hB : B.Nondegenerate) {z : ι → K}
    (hz : ∀ v, B v z ^ 2 = B v (N *ᵥ v)) {X : GL ι K}
    (hX : ∀ u v, B ((X : Matrix ι ι K) *ᵥ u) ((X : Matrix ι ι K) *ᵥ v) = B u v)
    (hXN : (X : Matrix ι ι K) * N = N * X) : (X : Matrix ι ι K) *ᵥ z = z := by
  have hfrob : Function.Injective fun x : K => x ^ 2 := by
    intro a b hab
    simp only at hab
    have h : (a + b) ^ 2 = 0 := by rw [CharTwo.add_sq, hab, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  have h1 : ∀ v, B ((X : Matrix ι ι K) *ᵥ v) z = B v z := fun v => by
    apply hfrob
    simp only
    rw [hz, hz, mulVec_mulVec, ← hXN, ← mulVec_mulVec, hX]
  have hsurj : ∀ w, ∃ v, (X : Matrix ι ι K) *ᵥ v = w := fun w =>
    ⟨((X⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w, by rw [mulVec_mulVec, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mulVec]⟩
  have h3 : ∀ w, B w ((X : Matrix ι ι K) *ᵥ z - z) = 0 := fun w => by
    obtain ⟨v, rfl⟩ := hsurj w
    rw [map_sub, hX, h1, sub_self]
  exact sub_eq_zero.mp (hB.2 _ h3)

end Sqrt

section TypeA

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_quadraticForm_sub_one {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2) :
    ∃ Q : QuadraticForm K (Fin n ⊕ Fin n → K), Q.polarBilin = (quadPlus n K).polarBilin ∧
      ∀ v, Q (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0 := by
  obtain ⟨Q, hpol, hQ⟩ := exists_quadraticForm_eq_zero_on (quadPlus n K)
    (LinearMap.range ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1).mulVecLin) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact polarBilin_sub_one_sub_one (polarBilin_mulVec_of_mem_statedSp hM) hM2 u v)
  exact ⟨Q, hpol, fun v => hQ _ ⟨v, rfl⟩⟩

theorem even_commRank_of_sympForm_eq_zero {M : GL (Fin n ⊕ Fin n) K} (hM : M ∈ StatedSp n K)
    (hM2 : orderOf M = 2)
    (h0 : ∀ v, sympForm n K v ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = 0) :
    Even (commRank M) := by
  obtain ⟨Q, hpol, hQ0⟩ := exists_quadraticForm_sub_one hM hM2
  have hQ : Q.polarBilin.Nondegenerate := by
    rw [hpol]
    exact nondegenerate_polarBilin_quadPlus n K
  have hMQ : ∀ v, Q ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v) = Q v := fun v => by
    have h1 : (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ v =
        v + ((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v := by
      rw [sub_mulVec, one_mulVec, add_sub_cancel]
    have h2 : Q.polarBilin v (((M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) - 1) *ᵥ v) = 0 := by
      rw [hpol, polarBilin_quadPlus, sub_mulVec, one_mulVec]
      simp only [sympForm, dotProduct_sub, mulVec_sub] at h0 ⊢
      rw [h0 v, zero_sub, neg_eq_zero]
      exact sympForm_self v
    rw [h1, quad_add, hQ0, h2, add_zero, add_zero]
  have htt : glToLin M * glToLin M = 1 := by
    rw [← map_mul, ← _root_.sq, ← hM2, pow_orderOf_eq_one, map_one]
  have h := even_finrank_commSpace_of_forall_eq_zero hQ (glToLin_mem_orthogonalGroup hMQ) htt
    (fun x hx => by
      rw [commSpace_glToLin] at hx
      obtain ⟨v, rfl⟩ := hx
      exact hQ0 v)
  rwa [finrank_commSpace_glToLin] at h

end TypeA

end CFSG.ComponentClassification.RankTwoClassical
