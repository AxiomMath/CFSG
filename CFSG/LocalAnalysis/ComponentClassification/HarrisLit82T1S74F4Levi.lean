module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F4Lin
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74F2b

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def leviSet (K : Type) [Field K] : Set (VEnd K) :=
  {ℓ | (∀ v, quadOdd 3 K (ℓ v) = quadOdd 3 K v) ∧
    ℓ * (frame01 K).La (-1) = (frame01 K).La (-1) * ℓ ∧
    (∃ μ : K, μ * μ = 1 ∧ ∀ v, (frame01 K).La (-1) v = v → ℓ v = μ • v) ∧
    ℓ * eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) =
      eichler (quadOdd 3 K) (oddVec 3 K 1 true) (oddVec 3 K 0 true) * ℓ}

noncomputable abbrev matL (ℓ : VEnd K) : Matrix (Fin 2) (Fin 2) K :=
  !![polar (quadOdd 3 K) (ℓ (oddVec 3 K 1 false)) (oddVec 3 K 1 true),
    -polar (quadOdd 3 K) (ℓ (oddVec 3 K 0 false)) (oddVec 3 K 1 true);
    -polar (quadOdd 3 K) (ℓ (oddVec 3 K 1 false)) (oddVec 3 K 0 true),
    polar (quadOdd 3 K) (ℓ (oddVec 3 K 0 false)) (oddVec 3 K 0 true)]

theorem det_matL {ℓ : VEnd K} (hℓ : ℓ ∈ leviSet K) : (matL ℓ).det = 1 := by
  obtain ⟨-, -, hd⟩ := apply_planeL_of_commute_eichOne hℓ.1 hℓ.2.2.2
  rw [Matrix.det_fin_two_of]
  linear_combination hd

noncomputable abbrev slL {ℓ : VEnd K} (hℓ : ℓ ∈ leviSet K) : SL(2, K) :=
  ⟨matL ℓ, det_matL hℓ⟩

noncomputable abbrev rhoJ (A : SL(2, K)) : VEnd K :=
  spinAction (quadOdd 3 K) ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false A)

theorem rhoJ_eq (A : SL(2, K)) : rhoJ A = (frame01 K).swap.La A := by
  rw [rhoJ, spinAction_longSL2]
  rfl

theorem rhoJ_commute_La (A : SL(2, K)) :
    rhoJ A * (frame01 K).La (-1) = (frame01 K).La (-1) * rhoJ A := by
  rw [rhoJ_eq]
  exact ((frame01 K).La_swap_neg_one_comm A).symm

theorem rhoJ_apply_of_fix (h2 : (2 : K) ≠ 0) (A : SL(2, K)) {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : (frame01 K).La (-1) v = v) : rhoJ A v = v := by
  have hc : (frame01 K).coords v = 0 :=
    (Frame.mem_perp_iff (frame01 K)).mp (((frame01 K).mem_perp_iff_fix h2).mpr hv)
  rw [rhoJ_eq]
  refine (frame01 K).swap.La_apply_of_coords_eq_zero A ?_
  rw [Frame.coords_swap, hc, map_zero]

theorem rhoJ_mem_orthogonalGroup (A : SL(2, K)) :
    rhoJ A ∈ TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ _)

noncomputable abbrev leviRest {ℓ : VEnd K} (hℓ : ℓ ∈ leviSet K) : VEnd K :=
  (rhoJ (slL hℓ))⁻¹ * ℓ

section Rest

variable {ℓ : VEnd K} (hℓ : ℓ ∈ leviSet K)
include hℓ

theorem rhoJ_slL_apply :
    rhoJ (slL hℓ) (oddVec 3 K 0 true) = ℓ (oddVec 3 K 0 true) ∧
      rhoJ (slL hℓ) (oddVec 3 K 1 true) = ℓ (oddVec 3 K 1 true) := by
  obtain ⟨he0, he1, -⟩ := apply_planeL_of_commute_eichOne hℓ.1 hℓ.2.2.2
  obtain ⟨h0, h1⟩ := spinAction_JThree_apply (slL hℓ)
  refine ⟨?_, ?_⟩
  · rw [rhoJ, h0, he0]
    simp [neg_smul, sub_eq_add_neg]
  · rw [rhoJ, h1, he1]
    simp

theorem leviRest_apply_eZero : leviRest hℓ (oddVec 3 K 0 true) = oddVec 3 K 0 true := by
  rw [leviRest, LinearEquiv.mul_apply, ← (rhoJ_slL_apply hℓ).1]
  exact LinearEquiv.symm_apply_apply _ _

theorem leviRest_apply_eOne : leviRest hℓ (oddVec 3 K 1 true) = oddVec 3 K 1 true := by
  rw [leviRest, LinearEquiv.mul_apply, ← (rhoJ_slL_apply hℓ).2]
  exact LinearEquiv.symm_apply_apply _ _

theorem leviRest_map (v : Fin 3 ⊕ Fin 3 ⊕ Unit → K) :
    quadOdd 3 K (leviRest hℓ v) = quadOdd 3 K v := by
  rw [leviRest, LinearEquiv.mul_apply,
    map_of_mem (inv_mem (rhoJ_mem_orthogonalGroup (slL hℓ))), hℓ.1]

theorem leviRest_commute_La :
    leviRest hℓ * (frame01 K).La (-1) = (frame01 K).La (-1) * leviRest hℓ := by
  have h := Frame.inv_commute_La (rhoJ_commute_La (slL hℓ))
  rw [leviRest, mul_assoc, hℓ.2.1, ← mul_assoc, h, mul_assoc]

theorem leviRest_apply_of_fix (h2 : (2 : K) ≠ 0) {μ : K}
    (hμ : ∀ v, (frame01 K).La (-1) v = v → ℓ v = μ • v) {v : Fin 3 ⊕ Fin 3 ⊕ Unit → K}
    (hv : (frame01 K).La (-1) v = v) : leviRest hℓ v = μ • v := by
  have hfix : ∀ w, (frame01 K).La (-1) w = w → (rhoJ (slL hℓ))⁻¹ w = w := fun w hw =>
    (LinearEquiv.symm_apply_eq _).mpr (rhoJ_apply_of_fix h2 _ hw).symm
  have hμv : (frame01 K).La (-1) (μ • v) = μ • v := by rw [map_smul, hv]
  rw [leviRest, LinearEquiv.mul_apply, hμ v hv, hfix _ hμv]

end Rest

theorem eq_of_mem_span {x : Fin 3 ⊕ Fin 3 ⊕ Unit → K} (hx : x ∈ (frame01 K).span) :
    x = polar (quadOdd 3 K) x (oddVec 3 K 0 false) • oddVec 3 K 0 true +
      polar (quadOdd 3 K) x (oddVec 3 K 0 true) • oddVec 3 K 0 false +
      polar (quadOdd 3 K) x (oddVec 3 K 1 false) • oddVec 3 K 1 true +
      polar (quadOdd 3 K) x (oddVec 3 K 1 true) • oddVec 3 K 1 false := by
  conv_lhs => rw [(Frame.mem_span_iff (frame01 K)).mp hx]
  have hv : (frame01 K).e₁ = oddVec 3 K 0 true ∧ (frame01 K).f₁ = oddVec 3 K 0 false ∧
      (frame01 K).e₂ = oddVec 3 K 1 true ∧ (frame01 K).f₂ = oddVec 3 K 1 false :=
    ⟨rfl, rfl, rfl, rfl⟩
  rw [coords_frame01, Frame.incl_apply, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, neg_neg]

theorem quadOdd_frameVec (a c b d : K) :
    quadOdd 3 K (a • oddVec 3 K 0 true + c • oddVec 3 K 0 false + b • oddVec 3 K 1 true +
      d • oddVec 3 K 1 false) = a * c + b * d := by
  rw [quadOdd_apply, Fin.sum_univ_three]
  simp

theorem fZero_mem_span : oddVec 3 K 0 false ∈ (frame01 K).span :=
  ⟨!![0, 0; 0, 1], (CFSG.ClassicalInvolution.ModelFacts.Frame.f₁_eq_incl (frame01 K)).symm⟩

theorem fOne_mem_span : oddVec 3 K 1 false ∈ (frame01 K).span :=
  ⟨!![0, 0; 1, 0], (CFSG.ClassicalInvolution.ModelFacts.Frame.f₂_eq_incl (frame01 K)).symm⟩

section Rest

variable {ℓ : VEnd K} (hℓ : ℓ ∈ leviSet K)
include hℓ

theorem leviRest_apply_f (h2 : (2 : K) ≠ 0) :
    leviRest hℓ (oddVec 3 K 0 false) = oddVec 3 K 0 false -
        polar (quadOdd 3 K) (leviRest hℓ (oddVec 3 K 1 false)) (oddVec 3 K 0 false) •
          oddVec 3 K 1 true ∧
      leviRest hℓ (oddVec 3 K 1 false) = oddVec 3 K 1 false +
        polar (quadOdd 3 K) (leviRest hℓ (oddVec 3 K 1 false)) (oddVec 3 K 0 false) •
          oddVec 3 K 0 true := by
  have hO := leviRest_map hℓ
  have hc := leviRest_commute_La hℓ
  have he0 := leviRest_apply_eZero hℓ
  have he1 := leviRest_apply_eOne hℓ
  have hb : ∀ (i j : Fin 3) (s t : Bool), polar (quadOdd 3 K) (oddVec 3 K i s)
      (oddVec 3 K j t) = if i = j ∧ s = !t then 1 else 0 := polar_quadOdd_oddVec 3 K
  have hp : ∀ (i j : Fin 3) (s : Bool), j ≠ 2 → polar (quadOdd 3 K) (leviRest hℓ
      (oddVec 3 K i s)) (oddVec 3 K j true) = polar (quadOdd 3 K) (oddVec 3 K i s)
        (oddVec 3 K j true) := by
    intro i j s hj
    have hej : leviRest hℓ (oddVec 3 K j true) = oddVec 3 K j true := by
      fin_cases j
      · exact he0
      · exact he1
      · exact absurd rfl hj
    rw [← hej, polar_apply_of_map hO, hej]
  set v := leviRest hℓ (oddVec 3 K 0 false) with hvdef
  set w := leviRest hℓ (oddVec 3 K 1 false) with hwdef
  have hv := eq_of_mem_span (Frame.map_mem_span h2 hc fZero_mem_span)
  have hw := eq_of_mem_span (Frame.map_mem_span h2 hc fOne_mem_span)
  rw [← hvdef] at hv
  rw [← hwdef] at hw
  have v0 : polar (quadOdd 3 K) v (oddVec 3 K 0 true) = 1 := by
    rw [hvdef, hp 0 0 false (by decide), hb]; simp
  have v1 : polar (quadOdd 3 K) v (oddVec 3 K 1 true) = 0 := by
    rw [hvdef, hp 0 1 false (by decide), hb]; simp
  have w0 : polar (quadOdd 3 K) w (oddVec 3 K 0 true) = 0 := by
    rw [hwdef, hp 1 0 false (by decide), hb]; simp
  have w1 : polar (quadOdd 3 K) w (oddVec 3 K 1 true) = 1 := by
    rw [hwdef, hp 1 1 false (by decide), hb]; simp
  rw [v0, v1, one_smul, zero_smul, add_zero] at hv
  rw [w0, w1, one_smul, zero_smul, add_zero] at hw
  have hQv : polar (quadOdd 3 K) v (oddVec 3 K 0 false) = 0 := by
    have h := hO (oddVec 3 K 0 false)
    rw [← hvdef, quadOdd_oddVec] at h
    have h' := quadOdd_frameVec (K := K) (polar (quadOdd 3 K) v (oddVec 3 K 0 false)) 1
      (polar (quadOdd 3 K) v (oddVec 3 K 1 false)) 0
    rw [one_smul, zero_smul, add_zero, ← hv, h] at h'
    linear_combination -h'
  have hQw : polar (quadOdd 3 K) w (oddVec 3 K 1 false) = 0 := by
    have h := hO (oddVec 3 K 1 false)
    rw [← hwdef, quadOdd_oddVec] at h
    have h' := quadOdd_frameVec (K := K) (polar (quadOdd 3 K) w (oddVec 3 K 0 false)) 0
      (polar (quadOdd 3 K) w (oddVec 3 K 1 false)) 1
    rw [zero_smul, add_zero, one_smul, ← hw, h] at h'
    linear_combination -h'
  rw [hQv, zero_smul, zero_add] at hv
  rw [hQw, zero_smul, add_zero] at hw
  obtain ⟨σ, hσ⟩ : ∃ σ, polar (quadOdd 3 K) w (oddVec 3 K 0 false) = σ := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, polar (quadOdd 3 K) v (oddVec 3 K 1 false) = τ := ⟨_, rfl⟩
  rw [hσ] at hw ⊢
  rw [hτ] at hv
  have hvw : τ = -σ := by
    have h := polar_apply_of_map hO (oddVec 3 K 0 false) (oddVec 3 K 1 false)
    rw [← hvdef, ← hwdef, hv, hw] at h
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, hb] at h
    simp at h
    linear_combination h
  refine ⟨?_, ?_⟩
  · rw [hv, hvw, neg_smul, sub_eq_add_neg]
  · rw [hw]
    abel

end Rest

end CFSG.ComponentClassification.HarrisLit.T1.S74
