module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Reflection
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K]

section Commutant

@[expose] def lmulEquiv (A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (Frame.rhoL A) (Frame.rhoL A⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem lmulEquiv_apply (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    lmulEquiv A X = (A : Matrix (Fin 2) (Fin 2) K) * X :=
  rfl

theorem lmulEquiv_mem_leftGrp (A : SL(2, K)) : lmulEquiv A ∈ leftGrp := ⟨A, fun _ => rfl⟩

@[expose] def rmulEquiv (B : SL(2, K)) : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (LinearMap.mulRight K (B : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.mulRight K ((B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply]
      rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp)
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply]
      rw [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp)

theorem rmulEquiv_apply (B : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K) :
    rmulEquiv B X = X * (B : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem rmulEquiv_mem_rightGrp (B : SL(2, K)) : rmulEquiv B ∈ rightGrp := ⟨B, fun _ => rfl⟩

theorem leftGrp_ne_rightGrp : (leftGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
    Matrix (Fin 2) (Fin 2) K)) ≠ rightGrp := by
  intro h
  let t : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hmem : lmulEquiv t ∈ (rightGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K]
      Matrix (Fin 2) (Fin 2) K)) := by
    rw [← h]
    exact lmulEquiv_mem_leftGrp t
  obtain ⟨B, hB⟩ := hmem
  have h1 : (t : Matrix (Fin 2) (Fin 2) K) = (B : Matrix (Fin 2) (Fin 2) K) := by
    simpa [lmulEquiv_apply] using hB 1
  have h2 := hB !![0, 0; 1, 0]
  rw [lmulEquiv_apply, ← h1] at h2
  have h3 := congrFun (congrFun h2 1) 1
  simp [t, Matrix.mul_apply, Fin.sum_univ_two] at h3

theorem eq_mulRight_of_commute_left {T : Module.End K (Matrix (Fin 2) (Fin 2) K)}
    (hT : ∀ (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      T ((A : Matrix (Fin 2) (Fin 2) K) * X) = (A : Matrix (Fin 2) (Fin 2) K) * T X)
    (X : Matrix (Fin 2) (Fin 2) K) : T X = X * T 1 := by
  let t₁ : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let t₂ : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  have h1 : ∀ Y, T (!![0, 1; 0, 0] * Y) = !![0, 1; 0, 0] * T Y := by
    intro Y
    have := hT t₁ Y
    have e : (t₁ : Matrix (Fin 2) (Fin 2) K) * Y = Y + !![0, 1; 0, 0] * Y := by
      change !![1, 1; 0, 1] * Y = _
      rw [show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + !![0, 1; 0, 0] by
        ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.add_mul, Matrix.one_mul]
    rw [e, map_add, show (t₁ : Matrix (Fin 2) (Fin 2) K) * T Y = T Y + !![0, 1; 0, 0] * T Y by
      change !![1, 1; 0, 1] * T Y = _
      rw [show (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + !![0, 1; 0, 0] by
        ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.add_mul, Matrix.one_mul]] at this
    exact add_left_cancel this
  have h2 : ∀ Y, T (!![0, 0; 1, 0] * Y) = !![0, 0; 1, 0] * T Y := by
    intro Y
    have := hT t₂ Y
    have e : (t₂ : Matrix (Fin 2) (Fin 2) K) * Y = Y + !![0, 0; 1, 0] * Y := by
      change !![1, 0; 1, 1] * Y = _
      rw [show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + !![0, 0; 1, 0] by
        ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.add_mul, Matrix.one_mul]
    rw [e, map_add, show (t₂ : Matrix (Fin 2) (Fin 2) K) * T Y = T Y + !![0, 0; 1, 0] * T Y by
      change !![1, 0; 1, 1] * T Y = _
      rw [show (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) = 1 + !![0, 0; 1, 0] by
        ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.add_mul, Matrix.one_mul]] at this
    exact add_left_cancel this
  have e12 : T !![0, 1; 0, 0] = !![0, 1; 0, 0] * T 1 := by
    simpa using h1 1
  have e21 : T !![0, 0; 1, 0] = !![0, 0; 1, 0] * T 1 := by
    simpa using h2 1
  have e11 : T !![1, 0; 0, 0] = !![1, 0; 0, 0] * T 1 := by
    have := h1 !![0, 0; 1, 0]
    rw [show (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 1, 0] = !![1, 0; 0, 0] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      e21, ← Matrix.mul_assoc,
      show (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 1, 0] = !![1, 0; 0, 0] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]] at this
    exact this
  have e22 : T !![0, 0; 0, 1] = !![0, 0; 0, 1] * T 1 := by
    have := h2 !![0, 1; 0, 0]
    rw [show (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 0, 0] = !![0, 0; 0, 1] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
      e12, ← Matrix.mul_assoc,
      show (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 0, 0] = !![0, 0; 0, 1] by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]] at this
    exact this
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two X
  have hX : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K) =
      a • !![1, 0; 0, 0] + b • !![0, 1; 0, 0] + c • !![0, 0; 1, 0] + d • !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [hX, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, e11, e12, e21, e22]
  simp only [Matrix.add_mul, Matrix.smul_mul]

theorem eq_one_or_eq_neg_one_of_mul_self (h2 : (2 : K) ≠ 0) {c : Matrix (Fin 2) (Fin 2) K}
    (hc : c * c = 1) (hdet : c.det = 1) : c = 1 ∨ c = -1 := by
  obtain ⟨a, b, d, e, rfl⟩ := exists_eq_of_fin_two c
  have h00 := congrFun (congrFun hc 0) 0
  have h01 := congrFun (congrFun hc 0) 1
  have h10 := congrFun (congrFun hc 1) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  simp only [Matrix.det_fin_two_of] at hdet
  have hae : a + e ≠ 0 := by
    intro h
    have he : e = -a := by linear_combination h
    subst he
    apply h2
    linear_combination -h00 - hdet
  have hb : b = 0 := by
    have : b * (a + e) = 0 := by linear_combination h01
    exact (mul_eq_zero.mp this).resolve_right hae
  have hd : d = 0 := by
    have : d * (a + e) = 0 := by linear_combination h10
    exact (mul_eq_zero.mp this).resolve_right hae
  subst hb hd
  have ha : a * a = 1 := by linear_combination h00
  have hae1 : a * e = 1 := by linear_combination hdet
  rcases mul_self_eq_one_iff.mp ha with rfl | rfl
  · left
    have : e = 1 := by linear_combination hae1
    subst this
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    have : e = -1 := by linear_combination -hae1
    subst this
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem eq_one_or_eq_neg_one_of_commute_left (h2 : (2 : K) ≠ 0)
    {T : Module.End K (Matrix (Fin 2) (Fin 2) K)}
    (hT : ∀ (A : SL(2, K)) (X : Matrix (Fin 2) (Fin 2) K),
      T ((A : Matrix (Fin 2) (Fin 2) K) * X) = (A : Matrix (Fin 2) (Fin 2) K) * T X)
    (hT2 : ∀ X, T (T X) = X) (hdet : ∀ X, (T X).det = X.det) :
    T = 1 ∨ T = -1 := by
  have hR := eq_mulRight_of_commute_left hT
  have hc2 : T 1 * T 1 = 1 := by
    have := hT2 1
    rwa [hR (T 1), ] at this
  have hc : (T 1).det = 1 := by simpa using hdet 1
  rcases eq_one_or_eq_neg_one_of_mul_self h2 hc2 hc with h | h
  · left
    ext X : 1
    rw [hR X, h]
    simp
  · right
    ext X : 1
    rw [hR X, h]
    simp

end Commutant

section Determinant

variable {X : Type*} [AddCommGroup X] [Module K X]

theorem isCompl_eigenspace_of_mul_self (h2 : (2 : K) ≠ 0) {T : Module.End K X} (hT : T * T = 1) :
    IsCompl (T.eigenspace 1) (T.eigenspace (-1)) := by
  have hTT : ∀ x, T (T x) = x := fun x => by simpa using LinearMap.congr_fun hT x
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [Module.End.mem_eigenspace_iff] at hx hx'
    have h : x = -x := by simpa only [one_smul, neg_smul] using hx.symm.trans hx'
    have : (2 : K) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      exact neg_add_cancel x
    exact (smul_eq_zero.mp this).resolve_left h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    refine ⟨(2 : K)⁻¹ • (x + T x), ?_, (2 : K)⁻¹ • (x - T x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_add, hTT, one_smul, add_comm]
    · rw [Module.End.mem_eigenspace_iff, map_smul, map_sub, hTT]
      module
    · rw [← smul_add, add_add_sub_cancel, ← two_smul K x, smul_smul, inv_mul_cancel₀ h2,
        one_smul]

theorem det_eq_neg_one_pow_finrank [FiniteDimensional K X] (h2 : (2 : K) ≠ 0)
    {T : Module.End K X} (hT : T * T = 1) :
    LinearMap.det T = (-1 : K) ^ Module.finrank K (T.eigenspace (-1)) := by
  have hc := isCompl_eigenspace_of_mul_self h2 hT
  let e : (T.eigenspace 1 × T.eigenspace (-1)) ≃ₗ[K] X := Submodule.prodEquivOfIsCompl _ _ hc
  let f : Module.End K (T.eigenspace 1 × T.eigenspace (-1)) :=
    LinearMap.prodMap LinearMap.id (-LinearMap.id)
  have hTe : ∀ z : T.eigenspace 1 × T.eigenspace (-1), T (e z) = e (f z) := by
    rintro ⟨p, q⟩
    have hp := Module.End.mem_eigenspace_iff.mp p.2
    have hq := Module.End.mem_eigenspace_iff.mp q.2
    simp [e, f, Submodule.coe_prodEquivOfIsCompl', hp, hq]
  have hTf : T = (e : _ →ₗ[K] X) ∘ₗ f ∘ₗ (e.symm : X →ₗ[K] _) := by
    refine LinearMap.ext fun x => ?_
    have := hTe (e.symm x)
    simpa using this
  have hdet : LinearMap.det T = LinearMap.det f := by
    conv_lhs => rw [hTf]
    rw [LinearMap.det_conj]
  rw [hdet, LinearMap.det_prodMap]
  have h1 : LinearMap.det (LinearMap.id : Module.End K (T.eigenspace 1)) = 1 := LinearMap.det_id
  have h2' : LinearMap.det (-LinearMap.id : Module.End K (T.eigenspace (-1))) =
      (-1 : K) ^ Module.finrank K (T.eigenspace (-1)) := by
    rw [show (-LinearMap.id : Module.End K (T.eigenspace (-1))) = (-1 : K) • LinearMap.id from
      (neg_one_smul K _).symm, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [h1, h2', one_mul]

end Determinant

section Parity

theorem neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)

theorem even_finrank_of_det_eq_one (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} (hS2 : ∀ X, S (S X) = X)
    (hd : LinearEquiv.det S = 1) :
    Even (Module.finrank K (Module.End.eigenspace (S : Module.End K (Matrix (Fin 2) (Fin 2) K))
      (-1))) := by
  have hSS : (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) *
      (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 :=
    LinearMap.ext fun X => hS2 X
  have h1 := det_eq_neg_one_pow_finrank h2 hSS
  have h3 : LinearMap.det (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hd
    simpa using this
  rw [h3] at h1
  exact (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp h1.symm

theorem odd_finrank_of_det_eq_neg_one (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} (hS2 : ∀ X, S (S X) = X)
    (hd : LinearEquiv.det S = -1) :
    Odd (Module.finrank K (Module.End.eigenspace (S : Module.End K (Matrix (Fin 2) (Fin 2) K))
      (-1))) := by
  have hSS : (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) *
      (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) = 1 :=
    LinearMap.ext fun X => hS2 X
  have h1 := det_eq_neg_one_pow_finrank h2 hSS
  have h3 : LinearMap.det (S : Module.End K (Matrix (Fin 2) (Fin 2) K)) = -1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hd
    simpa using this
  rw [h3] at h1
  rw [← Nat.not_even_iff_odd]
  intro he
  rw [he.neg_one_pow] at h1
  exact neg_one_ne_one h2 h1

theorem even_finrank_of_normalizes (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hS : S ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) (hS2 : ∀ X, S (S X) = X)
    (hn : conjSubgroup S leftGrp = leftGrp) :
    Even (Module.finrank K (Module.End.eigenspace (S : Module.End K (Matrix (Fin 2) (Fin 2) K))
      (-1))) := by
  rcases isometry_trichotomy h2 hS with ⟨hd, -, -⟩ | ⟨-, hl, -⟩
  · exact even_finrank_of_det_eq_one h2 hS2 hd
  · exact absurd (hn.symm.trans hl) leftGrp_ne_rightGrp

theorem odd_finrank_of_swaps (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hS : S ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) (hS2 : ∀ X, S (S X) = X)
    (hn : conjSubgroup S leftGrp = rightGrp) :
    Odd (Module.finrank K (Module.End.eigenspace (S : Module.End K (Matrix (Fin 2) (Fin 2) K))
      (-1))) := by
  rcases isometry_trichotomy h2 hS with ⟨-, hl, -⟩ | ⟨hd, -, -⟩
  · exact absurd (hl.symm.trans hn) leftGrp_ne_rightGrp
  · exact odd_finrank_of_det_eq_neg_one h2 hS2 hd

end Parity

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
