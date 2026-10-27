module

public import CFSG.ClassicalInvolution.ModelFacts.L6CUFrame
public import CFSG.ClassicalInvolution.ModelFacts.L6CInner
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionEigen
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped MatrixGroups

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) K

theorem det_ne_zero_of_uadj_mul {M : 𝕄₄} (hM : uadj h M * M = 1) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hM
  rw [det_mul, h0, mul_zero, det_one] at this
  exact zero_ne_one this

theorem norm_eq_one_of_sq {M : 𝕄₄} (hM : uadj h M * M = 1) {c : K} (hMM : M * M = c • 1) :
    h.bar c * c = 1 := by
  have h1 : uadj h (M * M) * (M * M) = 1 := by
    rw [uadj_mul]
    calc uadj h M * uadj h M * (M * M) = uadj h M * (uadj h M * M) * M := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, Matrix.mul_one, hM]
  rw [hMM, uadj_smul, uadj_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul] at h1
  have := congrFun (congrFun h1 0) 0
  simpa using this

theorem isSquare_of_norm_one (hp2 : p ≠ 2) {c : K} (hc : h.bar c * c = 1) : IsSquare c := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  have hK2 : ringChar K ≠ 2 := MF15.ringChar_ne_two_of_two_ne_zero h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  rw [FiniteField.isSquare_iff hK2 hc0]
  have hcard : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact h.card_eq_sq
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ : Odd (p ^ f) := hpodd.pow
  have hdiv : Fintype.card K / 2 = (p ^ f + 1) * m := by
    rw [hcard, hm]
    have : (2 * m + 1) ^ 2 = 2 * ((2 * m + 1 + 1) * m) + 1 := by ring
    omega
  rw [hdiv, pow_mul, pow_succ, ← UnitaryFieldData.bar_apply h c, hc, one_pow]

theorem exists_sqrt_neg_one (hq4 : p ^ f % 4 = 1) : ∃ i : K, i * i = -1 ∧ h.bar i = i := by
  have := h.finite
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact h.card_eq_sq
  have hmod : Fintype.card K % 4 ≠ 3 := by
    rw [hcard, pow_two, Nat.mul_mod, hq4]
    norm_num
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.mpr hmod
  refine ⟨i, hi.symm, ?_⟩
  have h4 : i ^ 4 = 1 := by
    have : i ^ 4 = (i * i) * (i * i) := by ring
    rw [this, ← hi]
    norm_num
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 4 * m + 1 := ⟨p ^ f / 4, by omega⟩
  rw [UnitaryFieldData.bar_apply, hm, pow_succ, pow_mul, h4, one_pow, one_mul]

theorem exists_frame_isotropic (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1) {M : 𝕄₄}
    (hM : uadj h M * M = 1) {μ : K} (hμ0 : μ ≠ 0) (hν : h.bar μ * μ = -1) {B : 𝕄₄}
    (hMB : M = μ • B) (hBB : B * B = 1) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * (Q * (rot4 K : 𝕄₄) * uadj h Q) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  obtain ⟨i, hi, hbi⟩ := exists_sqrt_neg_one h hq4
  have hMx : ∀ x, M *ᵥ x = μ • (B *ᵥ x) := fun x => by rw [hMB, Matrix.smul_mulVec]
  have hBBx : ∀ x, B *ᵥ (B *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hBB, Matrix.one_mulVec]
  have hMM := stdHermForm_mulVec_mulVec h hM
  have hxB : ∀ x z : Fin 4 → K, B *ᵥ x = x → stdHermForm h 4 x (B *ᵥ z) =
      -stdHermForm h 4 x z := by
    intro x z hx
    have := hMM x z
    rw [hMx, hMx, hx, sh_smul_left, sh_smul_right] at this
    linear_combination (-1 : K) * this + stdHermForm h 4 x (B *ᵥ z) * hν
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → K, w + B *ᵥ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hBw : ∀ w : Fin 4 → K, B *ᵥ w = -w := fun w => eq_neg_of_add_eq_zero_right (hcon w)
    have h1 : stdHermForm h 4 (Pi.single 0 1) (Pi.single 0 1) = 1 := by
      rw [stdHermForm_single]
      simp
    have hMe : M *ᵥ (Pi.single 0 1 : Fin 4 → K) = (-μ) • (Pi.single 0 1 : Fin 4 → K) := by
      rw [hMx, hBw, smul_neg, neg_smul]
    have h0 := hMM (Pi.single 0 1) (Pi.single 0 1)
    rw [hMe, sh_smul_left, sh_smul_right, h1, map_neg] at h0
    apply h2
    linear_combination (-1 : K) * h0 + (1 : K) * hν
  set x₁ : Fin 4 → K := w + B *ᵥ w with hx₁def
  have hBx₁ : B *ᵥ x₁ = x₁ := by
    rw [hx₁def, Matrix.mulVec_add, hBBx, add_comm]
  have hMx₁ : M *ᵥ x₁ = μ • x₁ := by rw [hMx, hBx₁]
  have hxx : stdHermForm h 4 x₁ x₁ = 0 := by
    have := hxB x₁ x₁ hBx₁
    rw [hBx₁] at this
    have h3 : (2 : K) * stdHermForm h 4 x₁ x₁ = 0 := by linear_combination this
    exact (mul_eq_zero.mp h3).resolve_left h2
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, stdHermForm h 4 x₁ y₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (stdHermForm_separatingLeft h 4 x₁ hcon)
  set ym : Fin 4 → K := y₀ - B *ᵥ y₀ with hymdef
  have hBym : B *ᵥ ym = -ym := by
    rw [hymdef, Matrix.mulVec_sub, hBBx, neg_sub]
  have hxym : stdHermForm h 4 x₁ ym = 2 * stdHermForm h 4 x₁ y₀ := by
    rw [hymdef, map_sub, hxB x₁ y₀ hBx₁]
    ring
  have hd2 : 2 * stdHermForm h 4 x₁ y₀ ≠ 0 := mul_ne_zero h2 hy₀
  set y₁ : Fin 4 → K := (2 * stdHermForm h 4 x₁ y₀)⁻¹ • ym with hy₁def
  have hBy₁ : B *ᵥ y₁ = -y₁ := by rw [hy₁def, Matrix.mulVec_smul, hBym, smul_neg]
  have hMy₁ : M *ᵥ y₁ = (-μ) • y₁ := by rw [hMx, hBy₁, smul_neg, neg_smul]
  have hxy : stdHermForm h 4 x₁ y₁ = 1 := by
    rw [hy₁def, sh_smul_right, hxym]
    field_simp
  have hyx : stdHermForm h 4 y₁ x₁ = 1 := sh_symm_one h hxy
  have hyy : stdHermForm h 4 y₁ y₁ = 0 := by
    have := hMM y₁ y₁
    rw [hMy₁, sh_smul_left, sh_smul_right, map_neg] at this
    have h3 : (2 : K) * stdHermForm h 4 y₁ y₁ = 0 := by
      linear_combination (-1 : K) * this + stdHermForm h 4 y₁ y₁ * hν
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hb2 : h.bar (2 : K) = 2 := map_ofNat h.bar 2
  have hhalf : (2 : K)⁻¹ + (2 : K)⁻¹ = 1 := by rw [← two_mul, mul_inv_cancel₀ h2]
  obtain ⟨u₁, hu₁⟩ : ∃ u : Fin 4 → K, u = x₁ + (2 : K)⁻¹ • y₁ := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ u : Fin 4 → K, u = i • (x₁ - (2 : K)⁻¹ • y₁) := ⟨_, rfl⟩
  have h11 : stdHermForm h 4 u₁ u₁ = 1 := by
    rw [hu₁]
    simp only [sh_smul_left, map_add, LinearMap.add_apply, sh_smul_right, hxx, hyy,
      hxy, hyx, map_inv₀, hb2]
    linear_combination hhalf
  have h22 : stdHermForm h 4 u₂ u₂ = 1 := by
    rw [hu₂]
    simp only [sh_smul_left, sh_smul_right, map_sub, LinearMap.sub_apply, hxx, hyy,
      hxy, hyx, map_inv₀, hb2, hbi]
    linear_combination (-(i * i)) * hhalf + (-1 : K) * hi
  have h12 : stdHermForm h 4 u₁ u₂ = 0 := by
    rw [hu₁, hu₂]
    simp only [sh_smul_left, sh_smul_right, map_add, map_sub,
      LinearMap.add_apply, hxx, hyy, hxy, hyx, map_inv₀, hb2]
    linear_combination (i * 0) * hhalf
  have hM1 : M *ᵥ u₁ = (0 : K) • u₁ - (i * μ) • u₂ := by
    rw [hu₁, hu₂, Matrix.mulVec_add, Matrix.mulVec_smul, hMx₁, hMy₁]
    ext r
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, zero_mul, zero_sub]
    linear_combination (μ * (x₁ r - (2 : K)⁻¹ * y₁ r)) * hi
  have hM2 : M *ᵥ u₂ = (i * μ) • u₁ + (0 : K) • u₂ := by
    rw [hu₁, hu₂, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hMx₁, hMy₁]
    ext r
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, zero_mul, add_zero]
    ring
  have hdet : (0 : K) * 0 + (i * μ) * (i * μ) ≠ 0 := by
    have e : (0 : K) * 0 + (i * μ) * (i * μ) = -(μ * μ) := by
      linear_combination (μ * μ) * hi
    rw [e]
    exact neg_ne_zero.mpr (mul_self_ne_zero.mpr hμ0)
  exact exists_frame_of_plane h hM h11 h22 h12 hdet hM1 hM2

theorem exists_frame_eigen (hp2 : p ≠ 2) {M : 𝕄₄} (hM : uadj h M * M = 1) {μ : K} (hμ0 : μ ≠ 0)
    (hν : h.bar μ * μ = 1) {B : 𝕄₄} (hMB : M = μ • B) (hBB : B * B = 1)
    (hk : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' B - 1))) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * (Q * (rot4 K : 𝕄₄) * uadj h Q) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  have hK2 : ringChar K ≠ 2 := MF15.ringChar_ne_two_of_two_ne_zero h2
  have hMx : ∀ x, M *ᵥ x = μ • (B *ᵥ x) := fun x => by rw [hMB, Matrix.smul_mulVec]
  have hMM := stdHermForm_mulVec_mulVec h hM
  have hBM : ∀ x y : Fin 4 → K, stdHermForm h 4 (B *ᵥ x) (B *ᵥ y) = stdHermForm h 4 x y := by
    intro x y
    have := hMM x y
    rw [hMx, hMx, sh_smul_left, sh_smul_right, ← mul_assoc, hν, one_mul] at this
    exact this
  set V := LinearMap.ker (Matrix.toLin' B - 1) with hV
  set V' := LinearMap.ker (Matrix.toLin' B + 1) with hV'
  have hc : IsCompl V V' :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.isCompl_eigenspaces hK2 hBB
  have hBV : ∀ v ∈ V, B *ᵥ v = v := fun v hv => by
    rw [hV, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply, Module.End.one_apply,
      sub_eq_zero] at hv
    exact hv
  have hBV' : ∀ v ∈ V', B *ᵥ v = -v := fun v hv => by
    rw [hV', LinearMap.mem_ker, LinearMap.add_apply, Matrix.toLin'_apply,
      Module.End.one_apply] at hv
    exact eq_neg_of_add_eq_zero_left hv
  have horth : ∀ x ∈ V, ∀ y ∈ V', stdHermForm h 4 x y = 0 := by
    intro x hx y hy
    have := hBM x y
    rw [hBV x hx, hBV' y hy, map_neg] at this
    have h3 : (2 : K) * stdHermForm h 4 x y = 0 := by linear_combination -this
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hsep : ((stdHermForm h 4).domRestrict₁₂ V V).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply stdHermForm_separatingLeft h 4
    intro y
    have hy : y ∈ V ⊔ V' := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    have e1 := hx ⟨y₁, hy₁⟩
    rw [LinearMap.domRestrict₁₂_apply] at e1
    rw [map_add, e1, horth x x.2 y₂ hy₂, add_zero]
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis ((stdHermForm_isSymm h 4).domRestrict V) hsep
  have i0 : 0 < Module.finrank K V := by omega
  have i1 : 1 < Module.finrank K V := by omega
  set u₁ : Fin 4 → K := (e ⟨0, i0⟩ : Fin 4 → K) with hu₁
  set u₂ : Fin 4 → K := (e ⟨1, i1⟩ : Fin 4 → K) with hu₂
  have hne : (⟨0, i0⟩ : Fin (Module.finrank K V)) ≠ ⟨1, i1⟩ := by simp
  have g : ∀ (a b : Fin (Module.finrank K V)), stdHermForm h 4 (e a) (e b) =
      if a = b then 1 else 0 := fun a b => by
    rw [← he a b, LinearMap.domRestrict₁₂_apply]
  have h11 : stdHermForm h 4 u₁ u₁ = 1 := by rw [hu₁, g]; simp
  have h22 : stdHermForm h 4 u₂ u₂ = 1 := by rw [hu₂, g]; simp
  have h12 : stdHermForm h 4 u₁ u₂ = 0 := by
    rw [hu₁, hu₂, g, ite_eq_right_iff]
    intro h'
    exact absurd h' hne
  have hMu₁ : M *ᵥ u₁ = μ • u₁ := by rw [hMx, hBV _ (e ⟨0, i0⟩).2]
  have hMu₂ : M *ᵥ u₂ = μ • u₂ := by rw [hMx, hBV _ (e ⟨1, i1⟩).2]
  refine exists_frame_of_plane h hM h11 h22 h12 (a := μ) (b := 0) ?_ ?_ ?_
  · simpa using hμ0
  · rw [hMu₁]
    simp
  · rw [hMu₂]
    simp

theorem exists_frame_inner (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1) {M : 𝕄₄} (hM : uadj h M * M = 1)
    {c : K} (hMM : M * M = c • 1) :
    ∃ Q : 𝕄₄, uadj h Q * Q = 1 ∧
      M * (Q * (rot4 K : 𝕄₄) * uadj h Q) = Q * (rot4 K : 𝕄₄) * uadj h Q * M := by
  have h2 : (2 : K) ≠ 0 := UnitaryHigher.two_ne_zero_of_odd h hp2
  have hK2 : ringChar K ≠ 2 := MF15.ringChar_ne_two_of_two_ne_zero h2
  have hc0 : c ≠ 0 := by
    intro hc
    have hd := det_ne_zero_of_uadj_mul h hM
    have := congrArg Matrix.det hMM
    rw [det_mul, hc, zero_smul, det_zero] at this
    exact hd (mul_self_eq_zero.mp this)
  have hcc := norm_eq_one_of_sq h hM hMM
  obtain ⟨μ, hμ⟩ := isSquare_of_norm_one h hp2 hcc
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hc0 (by rw [hμ, mul_zero])
  have hBB : (μ⁻¹ • M) * (μ⁻¹ • M) = 1 := inv_smul_mul_self4 hμ0 hμ.symm hMM
  have hMB : M = μ • (μ⁻¹ • M) := by rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
  have hν2 : (h.bar μ * μ) * (h.bar μ * μ) = 1 := by
    rw [← hcc, hμ, map_mul]
    ring
  rcases mul_self_eq_one_iff.mp hν2 with hν | hν
  · by_cases hk : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' (μ⁻¹ • M) - 1))
    · exact exists_frame_eigen h hp2 hM hμ0 hν hMB hBB hk
    · have hsum := Submodule.finrank_add_eq_of_isCompl
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.isCompl_eigenspaces hK2 hBB)
      rw [Module.finrank_fin_fun] at hsum
      have hker : LinearMap.ker (Matrix.toLin' (-(μ⁻¹ • M)) - 1) =
          LinearMap.ker (Matrix.toLin' (μ⁻¹ • M) + 1) := by
        ext v
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
          Matrix.toLin'_apply, Module.End.one_apply, neg_mulVec]
        rw [← neg_add', neg_eq_zero]
      refine exists_frame_eigen h hp2 hM (neg_ne_zero.mpr hμ0)
        (by rw [map_neg, neg_mul_neg]; exact hν) (B := -(μ⁻¹ • M))
        (by rw [neg_smul_neg]; exact hMB) (by rw [neg_mul_neg]; exact hBB) ?_
      rw [hker]
      omega
  · exact exists_frame_isotropic h hp2 hq4 hM hμ0 hν hMB hBB

end CFSG.ClassicalInvolution.ModelFacts.L6C
