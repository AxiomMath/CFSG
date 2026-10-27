module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryShearCalculus
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryShearReflection
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearHermGram

public section

namespace CFSG.SeitzReduction

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace UnitaryShear

variable {f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem gl_mulVec_inv_mulVec (g : GL (Fin n) K) (v : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      v := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem gl_inv_mulVec_mulVec (g : GL (Fin n) K) (v : Fin n → K) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      v := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mem_ker_sub_one {S : Matrix (Fin n) (Fin n) K} {v : Fin n → K} :
    v ∈ LinearMap.ker (S - 1).mulVecLin ↔ S *ᵥ v = v := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec, sub_eq_zero]

theorem mulVec_mem_range_of_commute {S Y : Matrix (Fin n) (Fin n) K} (hSY : S * Y = Y * S)
    {x : Fin n → K} (hx : x ∈ LinearMap.range (S - 1).mulVecLin) :
    Y *ᵥ x ∈ LinearMap.range (S - 1).mulVecLin := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨Y *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply, mulVec_mulVec, Matrix.sub_mul, Matrix.mul_sub, hSY,
    Matrix.one_mul, Matrix.mul_one]

theorem mulVec_mem_ker_of_commute {S Y : Matrix (Fin n) (Fin n) K} (hSY : S * Y = Y * S)
    {x : Fin n → K} (hx : x ∈ LinearMap.ker (S - 1).mulVecLin) :
    Y *ᵥ x ∈ LinearMap.ker (S - 1).mulVecLin := by
  rw [mem_ker_sub_one] at hx ⊢
  rw [mulVec_mulVec, hSY, ← mulVec_mulVec, hx]

theorem inv_commute_of_commute {S Y : GL (Fin n) K}
    (hSY : (S : Matrix (Fin n) (Fin n) K) * Y = Y * S) :
    (S : Matrix (Fin n) (Fin n) K) * ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S := by
  have h1 : S * Y = Y * S := Units.ext (by rw [Units.val_mul, Units.val_mul, hSY])
  have h2 : S * Y⁻¹ = Y⁻¹ * S := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, h1, inv_mul_cancel_left]
  rw [← Units.val_mul, h2, Units.val_mul]

section Commutator

variable {σ : K →+* K} {B : (Fin n → K) →ₛₗ[σ] (Fin n → K) →ₗ[K] K}
  {W L : Submodule K (Fin n → K)}

theorem isShear_commutator_of_fix (hWL : W ≤ L) (hL : L = W.orthogonalBilin B)
    (hW : W = L.orthogonalBilin B) {w u : Fin n → K} (hw : w ∈ W) (hu : u ∈ L)
    (R Y : GL (Fin n) K) (hR : IsShear B W L w u ((R : Matrix (Fin n) (Fin n) K) *ᵥ ·))
    (hY : ∀ x y, B ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x) ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      B x y)
    (hYW : ∀ x ∈ W, (Y : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W)
    (hY'L : ∀ x ∈ L, ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ L)
    (hYw : (Y : Matrix (Fin n) (Fin n) K) *ᵥ w = w)
    (hYu : (Y : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ L) :
    IsShear B W L w (u - (Y : Matrix (Fin n) (Fin n) K) *ᵥ u)
      (((R * Y * R⁻¹ * Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
  have h1 := hR.inverse hWL hL hW hw hu (gl_mulVec_inv_mulVec R) (gl_inv_mulVec_mulVec R)
  have h2 := h1.conj (Y : Matrix (Fin n) (Fin n) K).mulVecLin hY hYW (gl_mulVec_inv_mulVec Y)
    hY'L
  simp only [Matrix.mulVecLin_apply, mulVec_neg, hYw] at h2
  have h3 := hR.comp_left hWL hL hW hw hu (L.neg_mem hYu) h2.neg_right
  rw [← sub_eq_add_neg] at h3
  have e : ((R : Matrix (Fin n) (Fin n) K) *ᵥ ·) ∘ (fun v => (Y : Matrix (Fin n) (Fin n) K) *ᵥ
      (((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v))) =
      (((R * Y * R⁻¹ * Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
    funext v
    simp only [Function.comp_apply, Units.val_mul, ← mulVec_mulVec]
  rwa [e] at h3

theorem isShear_commutator_of_sub_mem (hWL : W ≤ L) (hL : L = W.orthogonalBilin B)
    (hW : W = L.orthogonalBilin B) {w u : Fin n → K} (hw : w ∈ W) (hu : u ∈ L)
    (R Y : GL (Fin n) K) (hR : IsShear B W L w u ((R : Matrix (Fin n) (Fin n) K) *ᵥ ·))
    (hY : ∀ x y, B ((Y : Matrix (Fin n) (Fin n) K) *ᵥ x) ((Y : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      B x y)
    (hYW : ∀ x ∈ W, (Y : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W)
    (hY'L : ∀ x ∈ L, ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ L)
    (hYu : (Y : Matrix (Fin n) (Fin n) K) *ᵥ u - u ∈ W) :
    IsShear B W L (w - (Y : Matrix (Fin n) (Fin n) K) *ᵥ w) u
      (((R * Y * R⁻¹ * Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
  have h1 := hR.inverse hWL hL hW hw hu (gl_mulVec_inv_mulVec R) (gl_inv_mulVec_mulVec R)
  have h2 := h1.conj (Y : Matrix (Fin n) (Fin n) K).mulVecLin hY hYW (gl_mulVec_inv_mulVec Y)
    hY'L
  simp only [Matrix.mulVecLin_apply, mulVec_neg] at h2
  have h3 := h2.of_sub_mem hL (u' := u) (by
    rw [show u - (Y : Matrix (Fin n) (Fin n) K) *ᵥ u =
      -((Y : Matrix (Fin n) (Fin n) K) *ᵥ u - u) by abel]
    exact W.neg_mem hYu)
  have h4 := hR.comp_right hWL hL hW hw (W.neg_mem (hYW w hw)) hu h3
  rw [← sub_eq_add_neg] at h4
  have e : ((R : Matrix (Fin n) (Fin n) K) *ᵥ ·) ∘ (fun v => (Y : Matrix (Fin n) (Fin n) K) *ᵥ
      (((R⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v))) =
      (((R * Y * R⁻¹ * Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
    funext v
    simp only [Function.comp_apply, Units.val_mul, ← mulVec_mulVec]
  rwa [e] at h4

end Commutator

section Elements

variable (h : UnitaryFieldData 2 f K) {G : Matrix (Fin n) (Fin n) K}
  (hH : (gramForm h G).IsSymm) {S : Matrix (Fin n) (Fin n) K}
  (hS : ∀ x y, gramForm h G (S *ᵥ x) (S *ᵥ y) = gramForm h G x y) {ζ : K} (hζ : h.norm ζ = 1)

theorem ne_zero_of_norm_eq_one {c : K} (hc : h.norm c = 1) : c ≠ 0 := by
  rintro rfl
  rw [UnitaryFieldData.norm, zero_mul] at hc
  exact zero_ne_one hc

theorem norm_inv_eq_one {c : K} (hc : h.norm c = 1) : h.norm c⁻¹ = 1 := by
  rw [norm_inv_eq, hc, inv_one]

theorem pow_eq_one_of_norm_eq_one {c : K} (hc : h.norm c = 1) : c ^ (2 ^ f + 1) = 1 := by
  rw [← h.norm_eq_pow, hc]

include hH in
theorem commute_quasiRefl {u u' : Fin n → K} (huu' : gramForm h G u u' = 0) (c c' : K) :
    Commute (quasiRefl h G u c) (quasiRefl h G u' c') :=
  quasiRefl_mul_comm hH huu' c c'

include hH hζ in
theorem quasiRefl_pair {e₁ e₂ : Fin n → K} (he₁ : gramForm h G e₁ e₁ ≠ 0)
    (he₂ : gramForm h G e₂ e₂ ≠ 0) (h12 : gramForm h G e₁ e₂ = 0) :
    (∀ x y, gramForm h G ((quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹) *ᵥ x)
      ((quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹) *ᵥ y) = gramForm h G x y) ∧
    (quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹).det = 1 ∧
    (quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹) ^ (2 ^ f + 1) = 1 ∧
    (quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹) *ᵥ e₁ = ζ • e₁ ∧
    ∀ v, gramForm h G e₁ v = 0 → gramForm h G e₂ v = 0 →
      (quasiRefl h G e₁ ζ * quasiRefl h G e₂ ζ⁻¹) *ᵥ v = v := by
  have hζ0 := ne_zero_of_norm_eq_one h hζ
  have hζ' := norm_inv_eq_one h hζ
  have h21 : gramForm h G e₂ e₁ = 0 := by rw [← hH.eq e₁ e₂, h12, map_zero]
  refine ⟨fun x y => ?_, ?_, ?_, ?_, fun v hv1 hv2 => ?_⟩
  · rw [← mulVec_mulVec, ← mulVec_mulVec, quasiRefl_isometry hH he₁ hζ,
      quasiRefl_isometry hH he₂ hζ']
  · rw [det_mul, det_quasiRefl he₁, det_quasiRefl he₂, mul_inv_cancel₀ hζ0]
  · rw [(commute_quasiRefl h hH h12 ζ ζ⁻¹).mul_pow, quasiRefl_pow he₁, quasiRefl_pow he₂,
      pow_eq_one_of_norm_eq_one h hζ, pow_eq_one_of_norm_eq_one h hζ', quasiRefl_one,
      quasiRefl_one, Matrix.mul_one]
  · rw [← mulVec_mulVec, quasiRefl_mulVec_of_orth _ h21, quasiRefl_mulVec_self he₁]
  · rw [← mulVec_mulVec, quasiRefl_mulVec_of_orth _ hv2, quasiRefl_mulVec_of_orth _ hv1]

include hS in
theorem quasiRefl_pair_commute {e₁ e₂ : Fin n → K} (hSe₁ : S *ᵥ e₁ = e₁) (hSe₂ : S *ᵥ e₂ = e₂)
    (c c' : K) :
    S * (quasiRefl h G e₁ c * quasiRefl h G e₂ c') =
      (quasiRefl h G e₁ c * quasiRefl h G e₂ c') * S := by
  rw [← Matrix.mul_assoc, mul_quasiRefl hS, hSe₁, Matrix.mul_assoc, mul_quasiRefl hS, hSe₂,
    Matrix.mul_assoc]

variable (hS2 : S * S = 1)

include hH hζ hS hS2 in
theorem quasiRefl_quad {e₁ e₂ : Fin n → K} (he₁ : gramForm h G e₁ e₁ ≠ 0)
    (he₂ : gramForm h G e₂ e₂ ≠ 0) (h11 : gramForm h G e₁ (S *ᵥ e₁) = 0)
    (h22 : gramForm h G e₂ (S *ᵥ e₂) = 0) (h12 : gramForm h G e₁ e₂ = 0)
    (h12' : gramForm h G e₁ (S *ᵥ e₂) = 0) :
    (∀ x y, gramForm h G (((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) *ᵥ x)
      (((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
        (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) *ᵥ y) = gramForm h G x y) ∧
    ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)).det = 1 ∧
    S * ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) =
      ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
        (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) * S ∧
    ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) ^ (2 ^ f + 1) = 1 ∧
    ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) *ᵥ (S *ᵥ e₁ - e₁) =
      ζ • (S *ᵥ e₁ - e₁) ∧
    ∀ u, S *ᵥ u = u → ((quasiRefl h G e₁ ζ * quasiRefl h G (S *ᵥ e₁) ζ) *
      (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (S *ᵥ e₂) ζ⁻¹)) *ᵥ u - u ∈
        LinearMap.range (S - 1).mulVecLin := by
  have : CharP K 2 := h.charP
  have hζ0 := ne_zero_of_norm_eq_one h hζ
  have hζ' := norm_inv_eq_one h hζ
  have hSS : ∀ v, S *ᵥ (S *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hS2, one_mulVec]
  have sym : ∀ {x y : Fin n → K}, gramForm h G x y = 0 → gramForm h G y x = 0 := fun hxy => by
    rw [← hH.eq, hxy, map_zero]
  have o1 : gramForm h G e₁ (S *ᵥ e₁) = 0 := h11
  have o2 : gramForm h G e₂ (S *ᵥ e₂) = 0 := h22
  have o3 : gramForm h G e₁ e₂ = 0 := h12
  have o4 : gramForm h G e₁ (S *ᵥ e₂) = 0 := h12'
  have o5 : gramForm h G (S *ᵥ e₁) e₂ = 0 := by rw [← hS, hSS]; exact h12'
  have o6 : gramForm h G (S *ᵥ e₁) (S *ᵥ e₂) = 0 := by rw [hS]; exact h12
  have he₁' : gramForm h G (S *ᵥ e₁) (S *ᵥ e₁) ≠ 0 := by rw [hS]; exact he₁
  have he₂' : gramForm h G (S *ᵥ e₂) (S *ᵥ e₂) ≠ 0 := by rw [hS]; exact he₂
  set ρ₁ := quasiRefl h G e₁ ζ with hρ₁
  set ρ₂ := quasiRefl h G (S *ᵥ e₁) ζ with hρ₂
  set ρ₃ := quasiRefl h G e₂ ζ⁻¹ with hρ₃
  set ρ₄ := quasiRefl h G (S *ᵥ e₂) ζ⁻¹ with hρ₄
  have c12 : Commute ρ₁ ρ₂ := commute_quasiRefl h hH o1 _ _
  have c34 : Commute ρ₃ ρ₄ := commute_quasiRefl h hH o2 _ _
  have c13 : Commute ρ₁ ρ₃ := commute_quasiRefl h hH o3 _ _
  have c14 : Commute ρ₁ ρ₄ := commute_quasiRefl h hH o4 _ _
  have c23 : Commute ρ₂ ρ₃ := commute_quasiRefl h hH o5 _ _
  have c24 : Commute ρ₂ ρ₄ := commute_quasiRefl h hH o6 _ _
  have cP : Commute (ρ₁ * ρ₂) (ρ₃ * ρ₄) :=
    (c13.mul_right c14).mul_left (c23.mul_right c24)
  refine ⟨fun x y => ?_, ?_, ?_, ?_, ?_, fun u hu => ?_⟩
  · simp only [← mulVec_mulVec]
    rw [quasiRefl_isometry hH he₁ hζ, quasiRefl_isometry hH he₁' hζ,
      quasiRefl_isometry hH he₂ hζ', quasiRefl_isometry hH he₂' hζ']
  · rw [det_mul, det_mul, det_mul, det_quasiRefl he₁, det_quasiRefl he₁', det_quasiRefl he₂,
      det_quasiRefl he₂']
    field_simp
  · have e1 : S * ρ₁ = ρ₂ * S := mul_quasiRefl hS e₁ ζ
    have e2 : S * ρ₂ = ρ₁ * S := by rw [hρ₂, mul_quasiRefl hS, hSS]
    have e3 : S * ρ₃ = ρ₄ * S := mul_quasiRefl hS e₂ ζ⁻¹
    have e4 : S * ρ₄ = ρ₃ * S := by rw [hρ₄, mul_quasiRefl hS, hSS]
    calc S * (ρ₁ * ρ₂ * (ρ₃ * ρ₄)) = ρ₂ * ρ₁ * (ρ₄ * ρ₃) * S := by
          simp only [← Matrix.mul_assoc, e1]
          simp only [Matrix.mul_assoc, e2, e3, e4]
      _ = ρ₁ * ρ₂ * (ρ₃ * ρ₄) * S := by rw [c12.eq, c34.eq]
  · rw [cP.mul_pow, c12.mul_pow, c34.mul_pow, quasiRefl_pow he₁, quasiRefl_pow he₁',
      quasiRefl_pow he₂, quasiRefl_pow he₂', pow_eq_one_of_norm_eq_one h hζ,
      pow_eq_one_of_norm_eq_one h hζ', quasiRefl_one, quasiRefl_one, quasiRefl_one, quasiRefl_one,
      Matrix.mul_one, Matrix.mul_one]
  · have hy1 : (ρ₁ * ρ₂ * (ρ₃ * ρ₄)) *ᵥ e₁ = ζ • e₁ := by
      simp only [← mulVec_mulVec]
      rw [hρ₄, quasiRefl_mulVec_of_orth _ (sym o4), hρ₃, quasiRefl_mulVec_of_orth _ (sym o3),
        hρ₂, quasiRefl_mulVec_of_orth _ (sym o1), hρ₁, quasiRefl_mulVec_self he₁]
    have hy2 : (ρ₁ * ρ₂ * (ρ₃ * ρ₄)) *ᵥ (S *ᵥ e₁) = ζ • (S *ᵥ e₁) := by
      simp only [← mulVec_mulVec]
      rw [hρ₄, quasiRefl_mulVec_of_orth _ (sym o6), hρ₃, quasiRefl_mulVec_of_orth _ (sym o5),
        hρ₂, quasiRefl_mulVec_self he₁', hρ₁, mulVec_smul, quasiRefl_mulVec_of_orth _ o1]
    rw [mulVec_sub, hy1, hy2, smul_sub]
  ·
    have hu1 : gramForm h G (S *ᵥ e₁) u = gramForm h G e₁ u := by rw [← hu, hS, hu]
    have hu2 : gramForm h G (S *ᵥ e₂) u = gramForm h G e₂ u := by rw [← hu, hS, hu]
    have hS1 : gramForm h G (S *ᵥ e₁) (S *ᵥ e₁) = gramForm h G e₁ e₁ := hS e₁ e₁
    have hS2' : gramForm h G (S *ᵥ e₂) (S *ᵥ e₂) = gramForm h G e₂ e₂ := hS e₂ e₂
    have e : (ρ₁ * ρ₂ * (ρ₃ * ρ₄)) *ᵥ u - u =
        ((ζ - 1) / gramForm h G e₁ e₁ * gramForm h G e₁ u) • (S *ᵥ e₁ + e₁) +
          ((ζ⁻¹ - 1) / gramForm h G e₂ e₂ * gramForm h G e₂ u) • (S *ᵥ e₂ + e₂) := by
      simp only [← mulVec_mulVec, hρ₁, hρ₂, hρ₃, hρ₄, quasiRefl_mulVec, map_add, map_smul,
        smul_eq_mul, o1, o2, o3, o4, o5, o6, hu1, hu2, hS1, hS2', mul_zero, add_zero]
      module
    have hm : ∀ x : Fin n → K, S *ᵥ x + x ∈ LinearMap.range (S - 1).mulVecLin := fun x => by
      refine ⟨x, ?_⟩
      rw [Matrix.mulVecLin_apply, sub_mulVec, one_mulVec]
      have h2 : (2 : K) • x = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
      linear_combination (norm := module) -h2
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hm e₁)) (Submodule.smul_mem _ _ (hm e₂))

end Elements

section Supply

variable (h : UnitaryFieldData 2 f K) {G : Matrix (Fin n) (Fin n) K}
  (hH : (gramForm h G).IsSymm)

theorem mul_eichlerMatrix_comm {S : Matrix (Fin n) (Fin n) K}
    (hS : ∀ x y, gramForm h G (S *ᵥ x) (S *ᵥ y) = gramForm h G x y) {w u : Fin n → K}
    (hSw : S *ᵥ w = w) (hSu : S *ᵥ u = u) (c : K) :
    S * eichlerMatrix h G w u c = eichlerMatrix h G w u c * S := by
  refine matrix_ext_mulVec fun v => ?_
  have h1 : gramForm h G w (S *ᵥ v) = gramForm h G w v := by
    calc gramForm h G w (S *ᵥ v) = gramForm h G (S *ᵥ w) (S *ᵥ v) := by rw [hSw]
      _ = gramForm h G w v := hS w v
  have h2 : gramForm h G u (S *ᵥ v) = gramForm h G u v := by
    calc gramForm h G u (S *ᵥ v) = gramForm h G (S *ᵥ u) (S *ᵥ v) := by rw [hSu]
      _ = gramForm h G u v := hS u v
  rw [← mulVec_mulVec, ← mulVec_mulVec, eichlerMatrix_mulVec, eichlerMatrix_mulVec, h1, h2,
    mulVec_add, mulVec_sub, mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, hSw, hSu]

theorem exists_add_bar_eq {d : K} (hd : h.bar d = d) : ∃ t : K, t + h.bar t = d := by
  obtain ⟨t, ht⟩ := h.traceLin_surjective ⟨d, hd⟩
  exact ⟨t, congrArg Subtype.val ht⟩

include hH in
theorem exists_eichler {s : GL (Fin n) K} (hs : s ∈ gramSU h G) {W L : Submodule K (Fin n → K)}
    (hLdef : L = LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) (hWL : W ≤ L)
    (hL : L = W.orthogonalBilin (gramForm h G)) {w u : Fin n → K} (hw : w ∈ W) (hu : u ∈ L) :
    ∃ r : gramSU h G, s * (r : GL (Fin n) K) = (r : GL (Fin n) K) * s ∧
      IsShear (gramForm h G) W L w u
        ((((r : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ ·) := by
  have hSiso := (mem_gramSU_iff_isometry.mp hs).1
  have hww : gramForm h G w w = 0 := by
    have hwL := hWL hw
    rw [hL] at hwL
    exact hwL w hw
  have hwu : gramForm h G w u = 0 := by
    have hu' := hu
    rw [hL] at hu'
    exact hu' w hw
  obtain ⟨c, hc⟩ := exists_add_bar_eq h (d := -gramForm h G u u)
    (by rw [map_neg, hH.eq u u])
  refine ⟨⟨_, eichlerGL_mem hH hww hwu hc⟩, Units.ext ?_, ?_⟩
  · have hSw : (s : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
      have := hWL hw
      rw [hLdef] at this
      exact mem_ker_sub_one.mp this
    have hSu : (s : Matrix (Fin n) (Fin n) K) *ᵥ u = u := by
      rw [hLdef] at hu
      exact mem_ker_sub_one.mp hu
    exact mul_eichlerMatrix_comm h hSiso hSw hSu c
  · exact SesqShear.eichlerMatrix_shear h hL hw u c

include hH in
theorem exists_commutator_shear_right {s : GL (Fin n) K} (hs : s ∈ gramSU h G)
    {W L : Submodule K (Fin n → K)}
    (hWdef : W = LinearMap.range ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin)
    (hLdef : L = LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) (hWL : W ≤ L)
    (hL : L = W.orthogonalBilin (gramForm h G)) (hW : W = L.orthogonalBilin (gramForm h G))
    {ζ : K} (hζ : h.norm ζ = 1) (hζ1 : ζ ≠ 1) {w : Fin n → K} (hw : w ∈ W) {e : Fin n → K}
    (he : e ∈ anisotropicPairs (gramForm h G) L) (a : K) :
    ∃ r y : gramSU h G, s * (r : GL (Fin n) K) = (r : GL (Fin n) K) * s ∧
      s * (y : GL (Fin n) K) = (y : GL (Fin n) K) * s ∧ y ^ (2 ^ f + 1) = 1 ∧
      IsShear (gramForm h G) W L w (a • e)
        ((((r * y * r⁻¹ * y⁻¹ : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
  obtain ⟨heL, hee, e', he'L, he'e', hee'⟩ := he
  have hSiso := (mem_gramSU_iff_isometry.mp hs).1
  set Sm := (s : Matrix (Fin n) (Fin n) K) with hSm
  have hSe : Sm *ᵥ e = e := by
    have := heL
    rw [hLdef] at this
    exact mem_ker_sub_one.mp this
  have hSe' : Sm *ᵥ e' = e' := by
    have := he'L
    rw [hLdef] at this
    exact mem_ker_sub_one.mp this
  obtain ⟨hYiso, hYdet, hYpow, hYe, hYfix⟩ := quasiRefl_pair h hH hζ hee he'e' hee'
  set Ym := quasiRefl h G e ζ * quasiRefl h G e' ζ⁻¹ with hYm
  have hYcomm : Sm * Ym = Ym * Sm := quasiRefl_pair_commute h hSiso hSe hSe' ζ ζ⁻¹
  set Y : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero Ym (by rw [hYdet]; exact one_ne_zero)
    with hY
  have hYcoe : (Y : Matrix (Fin n) (Fin n) K) = Ym := rfl
  have hYmem : Y ∈ gramSU h G := mem_gramSU_iff_isometry.mpr ⟨hYiso, hYdet⟩
  have h1ζ : (1 : K) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
  set u := (a / (1 - ζ)) • e with hu
  have huL : u ∈ L := L.smul_mem _ heL
  obtain ⟨r, hrs, hr⟩ := exists_eichler h hH hs hLdef hWL hL hw huL
  refine ⟨r, ⟨Y, hYmem⟩, hrs, Units.ext hYcomm, Subtype.ext (Units.ext ?_), ?_⟩
  · change Ym ^ (2 ^ f + 1) = 1
    exact hYpow
  ·
    have hYW : ∀ x ∈ W, (Y : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W := fun x hx => by
      rw [hWdef] at hx ⊢
      exact mulVec_mem_range_of_commute hYcomm hx
    have hY'L : ∀ x ∈ L, ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ L :=
      fun x hx => by
        rw [hLdef] at hx ⊢
        exact mulVec_mem_ker_of_commute (inv_commute_of_commute (S := s) hYcomm) hx
    have hYw : (Y : Matrix (Fin n) (Fin n) K) *ᵥ w = w := by
      have hw' := hw
      rw [hW] at hw'
      exact hYfix w (hw' e heL) (hw' e' he'L)
    have hYu : (Y : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ L := by
      rw [hLdef] at huL ⊢
      exact mulVec_mem_ker_of_commute hYcomm huL
    have hc := isShear_commutator_of_fix hWL hL hW hw huL (r : GL (Fin n) K) Y hr hYiso hYW hY'L
      hYw hYu
    have hsc : a / (1 - ζ) - a / (1 - ζ) * ζ = a := by
      linear_combination div_mul_cancel₀ a h1ζ
    have hue : u - (Y : Matrix (Fin n) (Fin n) K) *ᵥ u = a • e := by
      rw [hYcoe, hu, mulVec_smul, hYe, smul_smul, ← sub_smul, hsc]
    rw [hue] at hc
    exact hc

include hH in
theorem exists_commutator_shear_left {s : GL (Fin n) K} (hs : s ∈ gramSU h G) (hs2 : s * s = 1)
    {W L : Submodule K (Fin n → K)}
    (hWdef : W = LinearMap.range ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin)
    (hLdef : L = LinearMap.ker ((s : Matrix (Fin n) (Fin n) K) - 1).mulVecLin) (hWL : W ≤ L)
    (hL : L = W.orthogonalBilin (gramForm h G)) (hW : W = L.orthogonalBilin (gramForm h G))
    {ζ : K} (hζ : h.norm ζ = 1) (hζ1 : ζ ≠ 1) {e e' : Fin n → K}
    (he : gramForm h G e (((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ e) ≠ 0)
    (he' : gramForm h G e' (((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ e') ≠ 0)
    (hee' : gramForm h G e (((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ e') = 0) (a : K)
    {u : Fin n → K} (hu : u ∈ L) :
    ∃ r y : gramSU h G, s * (r : GL (Fin n) K) = (r : GL (Fin n) K) * s ∧
      s * (y : GL (Fin n) K) = (y : GL (Fin n) K) * s ∧ y ^ (2 ^ f + 1) = 1 ∧
      IsShear (gramForm h G) W L (a • (((s : Matrix (Fin n) (Fin n) K) - 1) *ᵥ e)) u
        ((((r * y * r⁻¹ * y⁻¹ : gramSU h G) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) := by
  have : CharP K 2 := h.charP
  have hSiso := (mem_gramSU_iff_isometry.mp hs).1
  set Sm := (s : Matrix (Fin n) (Fin n) K) with hSm
  have hSm2 : Sm * Sm = 1 := by rw [hSm, ← Units.val_mul, hs2, Units.val_one]
  have hSS : ∀ v, Sm *ᵥ (Sm *ᵥ v) = v := fun v => by rw [mulVec_mulVec, hSm2, one_mulVec]
  have hNv : ∀ v, (Sm - 1) *ᵥ v = Sm *ᵥ v - v := fun v => by rw [sub_mulVec, one_mulVec]
  have hN2 : ∀ v, (Sm - 1).mulVecLin ((Sm - 1).mulVecLin v) = 0 := fun v => by
    simp only [Matrix.mulVecLin_apply, hNv, mulVec_sub, hSS]
    have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    have h3 : (2 : K) • (Sm *ᵥ v) = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
    linear_combination (norm := module) h2 - h3
  have hNB : ∀ x y, gramForm h G ((Sm - 1).mulVecLin x) y =
      gramForm h G x ((Sm - 1).mulVecLin y) := fun x y => by
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hNv, hNv, map_sub, map_sub,
      LinearMap.sub_apply, ← hSiso (Sm *ᵥ x) y, hSS]
  obtain ⟨e₁, e₂, hNe₁, h11, h22, h12, h12', h1N, h2N⟩ :=
    exists_adjusted_pair (B := gramForm h G) (fun x y => hH.eq x y)
      (fun d hd => exists_add_bar_eq h hd) hN2 hNB he he' hee'
  simp only [Matrix.mulVecLin_apply] at hNe₁ h11 h22 h12' h1N h2N
  have hS11 : gramForm h G e₁ (Sm *ᵥ e₁) = 0 := by
    rw [show Sm *ᵥ e₁ = e₁ + (Sm - 1) *ᵥ e₁ by rw [hNv]; abel, map_add]
    exact h11
  have hS22 : gramForm h G e₂ (Sm *ᵥ e₂) = 0 := by
    rw [show Sm *ᵥ e₂ = e₂ + (Sm - 1) *ᵥ e₂ by rw [hNv]; abel, map_add]
    exact h22
  have hS12 : gramForm h G e₁ (Sm *ᵥ e₂) = 0 := by
    rw [show Sm *ᵥ e₂ = e₂ + (Sm - 1) *ᵥ e₂ by rw [hNv]; abel, map_add, h12, h12', add_zero]
  have he₁ : gramForm h G e₁ e₁ ≠ 0 := by
    intro h0
    rw [h0, zero_add, h1N] at h11
    exact he h11
  have he₂ : gramForm h G e₂ e₂ ≠ 0 := by
    intro h0
    rw [h0, zero_add, h2N] at h22
    exact he' h22
  obtain ⟨hYiso, hYdet, hYcomm, hYpow, hYN, hYL⟩ :=
    quasiRefl_quad h hH hSiso hζ hSm2 he₁ he₂ hS11 hS22 h12 hS12
  set Ym := (quasiRefl h G e₁ ζ * quasiRefl h G (Sm *ᵥ e₁) ζ) *
    (quasiRefl h G e₂ ζ⁻¹ * quasiRefl h G (Sm *ᵥ e₂) ζ⁻¹) with hYm
  set Y : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero Ym (by rw [hYdet]; exact one_ne_zero)
    with hY
  have hYcoe : (Y : Matrix (Fin n) (Fin n) K) = Ym := rfl
  have hYmem : Y ∈ gramSU h G := mem_gramSU_iff_isometry.mpr ⟨hYiso, hYdet⟩
  have h1ζ : (1 : K) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ1)
  set w := (a / (1 - ζ)) • ((Sm - 1) *ᵥ e₁) with hw
  have hwW : w ∈ W := by
    rw [hWdef]
    exact Submodule.smul_mem _ _ ⟨e₁, rfl⟩
  obtain ⟨r, hrs, hr⟩ := exists_eichler h hH hs hLdef hWL hL hwW hu
  refine ⟨r, ⟨Y, hYmem⟩, hrs, Units.ext hYcomm, Subtype.ext (Units.ext ?_), ?_⟩
  · change Ym ^ (2 ^ f + 1) = 1
    exact hYpow
  · have hYW : ∀ x ∈ W, (Y : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W := fun x hx => by
      rw [hWdef] at hx ⊢
      exact mulVec_mem_range_of_commute hYcomm hx
    have hY'L : ∀ x ∈ L, ((Y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ L :=
      fun x hx => by
        rw [hLdef] at hx ⊢
        exact mulVec_mem_ker_of_commute (inv_commute_of_commute (S := s) hYcomm) hx
    have hYu : (Y : Matrix (Fin n) (Fin n) K) *ᵥ u - u ∈ W := by
      have hu' := hu
      rw [hLdef] at hu'
      rw [hWdef]
      exact hYL u (mem_ker_sub_one.mp hu')
    have hc := isShear_commutator_of_sub_mem hWL hL hW hwW hu (r : GL (Fin n) K) Y hr hYiso hYW
      hY'L hYu
    have hsc : a / (1 - ζ) - a / (1 - ζ) * ζ = a := by
      linear_combination div_mul_cancel₀ a h1ζ
    have hwe : w - (Y : Matrix (Fin n) (Fin n) K) *ᵥ w = a • ((Sm - 1) *ᵥ e) := by
      rw [hYcoe, hw, mulVec_smul, hNv e₁, hYN, ← hNv, smul_smul, ← sub_smul, hsc, hNe₁]
    rw [hwe] at hc
    exact hc

end Supply

end UnitaryShear

end CFSG.SeitzReduction
