module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalFrame
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaOddOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix CFSG.Open QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K]

theorem eichler_pow_ringChar {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)
    (u w : V) : eichler Q u w ^ ringChar K = 1 := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have key : ∀ n : ℕ, eichler Q u w ^ n = eichler Q u (n • w) := by
      intro n
      induction n with
      | zero => simp [eichler_zero_right]
      | succ n ih =>
        have hn : polar Q u (n • w) = 0 := by
          rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right_eq, h.2, mul_zero]
        rw [pow_succ, ih, eichler_mul hn h.2, succ_nsmul]
    rw [key, ← Nat.cast_smul_eq_nsmul K, ringChar.Nat.cast_ringChar, zero_smul,
      eichler_zero_right]
  · rw [eichler_of_not h, one_pow]

theorem eichler_eq_eichler_neg_of_singular {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) :
    eichler Q u w = eichler Q w (-u) := by
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  have hwnu : polar Q w (-u) = 0 := by rw [polar_neg_right, hwu, neg_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply hu huw, eichler_apply hw hwnu, QuadraticMap.map_neg, hu, polar_neg_right,
    hw, zero_mul, add_zero, zero_mul, add_zero, neg_smul, sub_eq_add_neg, sub_eq_add_neg]
  module

theorem eichler_cyclic_of_add_eq_zero {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {t₁ t₂ t₃ : V} (hsum : t₁ + t₂ + t₃ = 0) (h₁ : Q t₁ = 0)
    (h₂ : Q t₂ = 0) (h₁₂ : polar Q t₁ t₂ = 0) : eichler Q t₂ t₃ = eichler Q t₁ t₂ := by
  have h3 : t₃ = -t₁ + (-1 : K) • t₂ := by
    linear_combination (norm := module) hsum
  have hnu : Q (-t₁) = 0 := by rw [QuadraticMap.map_neg, h₁]
  have h21 : polar Q t₂ (-t₁) = 0 := by rw [polar_neg_right, polar_comm, h₁₂, neg_zero]
  rw [h3, eichler_add_smul_self h₂, eichler_eq_eichler_neg_of_singular h₂ hnu h21,
    show (-t₁ : V) = (-1 : K) • t₁ by rw [neg_smul, one_smul], eichler_smul_left]
  congr 1
  rw [neg_smul, one_smul, neg_neg]

@[expose] noncomputable def omegaRootGL (F : Frame K) (u w : Idx → K) : GL Idx K :=
  (toLinEquiv Idx K).symm (eichler (quadOdd 3 K) (F.lin u) (F.lin w))

theorem toLinEquiv_omegaRootGL (F : Frame K) (u w : Idx → K) :
    toLinEquiv Idx K (omegaRootGL F u w) = eichler (quadOdd 3 K) (F.lin u) (F.lin w) :=
  (toLinEquiv Idx K).apply_symm_apply _

theorem omegaRootGL_isometry (F : Frame K) (u w x : Idx → K) :
    StatedQuadOdd 3 K (((omegaRootGL F u w : GL Idx K) : Matrix Idx Idx K) *ᵥ x) =
      StatedQuadOdd 3 K x := by
  have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (eichler_mem_orthogonalGroup (quadOdd 3 K) (F.lin u) (F.lin w)) x
  rw [← toLinEquiv_omegaRootGL F u w, toLinEquiv_apply] at h
  rw [← coe_quadOdd 3 K]
  exact h

theorem omegaRootGL_pow_ringChar (F : Frame K) (u w : Idx → K) :
    omegaRootGL F u w ^ ringChar K = 1 := by
  apply (toLinEquiv Idx K).injective
  rw [map_pow, toLinEquiv_omegaRootGL, map_one]
  exact eichler_pow_ringChar _ _ _

theorem omegaRootGL_mem [Finite K] (F : Frame K) (u w : Idx → K) :
    omegaRootGL F u w ∈ Omega7 K := by
  refine mem_statedOmega_quadOdd_of_odd F.hK _ (omegaRootGL_isometry F u w) ?_
  exact Odd.of_dvd_nat ((CharP.prime_ringChar K).odd_of_ne_two F.hK)
    (orderOf_dvd_of_pow_eq_one (omegaRootGL_pow_ringChar F u w))

@[expose] noncomputable def omegaRoot [Finite K] (F : Frame K) (u w : Idx → K) : ↥(Omega7 K) :=
  ⟨omegaRootGL F u w, omegaRootGL_mem F u w⟩

theorem coe_omegaRoot [Finite K] (F : Frame K) (u w : Idx → K) :
    ((omegaRoot F u w : ↥(Omega7 K)) : GL Idx K) = omegaRootGL F u w :=
  rfl

theorem omegaRootGL_model_apply (F : Frame K) {u w : Idx → K} (hu : modelQuad K F.a u = 0)
    (hw : modelPolar K F.a u w = 0) (x : Idx → K) :
    ((F.P⁻¹ * omegaRootGL F u w * F.P : GL Idx K) : Matrix Idx Idx K) *ᵥ x =
      x + modelPolar K F.a x u • w -
        (modelPolar K F.a x w + modelQuad K F.a w * modelPolar K F.a x u) • u := by
  apply F.lin.injective
  have hPP : (F.P : Matrix Idx Idx K) * ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ∀ y : Idx → K,
      (F.P : Matrix Idx Idx K) *ᵥ (((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
  have h1 : F.lin (((F.P⁻¹ * omegaRootGL F u w * F.P : GL Idx K) : Matrix Idx Idx K) *ᵥ x) =
      eichler (quadOdd 3 K) (F.lin u) (F.lin w) (F.lin x) := by
    rw [F.lin_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      h2, ← toLinEquiv_omegaRootGL, toLinEquiv_apply, F.lin_apply]
  have hu' : quadOdd 3 K (F.lin u) = 0 := by rw [F.quadOdd_lin, hu]
  have hw' : polar (quadOdd 3 K) (F.lin u) (F.lin w) = 0 := by rw [F.polar_lin, hw]
  rw [h1, eichler_apply hu' hw', map_sub, map_add, map_smul, map_smul, F.polar_lin, F.polar_lin,
    F.quadOdd_lin]

theorem omegaRoot_mul [Finite K] (F : Frame K) {u w₁ w₂ : Idx → K}
    (h₁ : modelPolar K F.a u w₁ = 0) (h₂ : modelPolar K F.a u w₂ = 0) :
    omegaRoot F u w₁ * omegaRoot F u w₂ = omegaRoot F u (w₁ + w₂) := by
  apply Subtype.ext
  apply (toLinEquiv Idx K).injective
  show toLinEquiv Idx K (omegaRootGL F u w₁ * omegaRootGL F u w₂) =
    toLinEquiv Idx K (omegaRootGL F u (w₁ + w₂))
  rw [map_mul, toLinEquiv_omegaRootGL, toLinEquiv_omegaRootGL, toLinEquiv_omegaRootGL, map_add]
  exact eichler_mul (by rw [F.polar_lin]; exact h₁) (by rw [F.polar_lin]; exact h₂)

theorem omegaRoot_cyclic [Finite K] (F : Frame K) {t₁ t₂ t₃ : Idx → K}
    (hsum : t₁ + t₂ + t₃ = 0) (h₁ : modelQuad K F.a t₁ = 0) (h₂ : modelQuad K F.a t₂ = 0)
    (h₁₂ : modelPolar K F.a t₁ t₂ = 0) : omegaRoot F t₂ t₃ = omegaRoot F t₁ t₂ := by
  apply Subtype.ext
  apply (toLinEquiv Idx K).injective
  show toLinEquiv Idx K (omegaRootGL F t₂ t₃) = toLinEquiv Idx K (omegaRootGL F t₁ t₂)
  rw [toLinEquiv_omegaRootGL, toLinEquiv_omegaRootGL]
  exact eichler_cyclic_of_add_eq_zero (by rw [← map_add, ← map_add, hsum, map_zero])
    (by rw [F.quadOdd_lin, h₁]) (by rw [F.quadOdd_lin, h₂]) (by rw [F.polar_lin, h₁₂])

theorem Frame.conj_isometry (F : Frame K) {m : GL Idx K}
    (hm : ∀ w, modelQuad K F.a ((m : Matrix Idx Idx K) *ᵥ w) = modelQuad K F.a w) (w : Idx → K) :
    StatedQuadOdd 3 K (((F.P * m * F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ w) =
      StatedQuadOdd 3 K w := by
  have hPP : (F.P : Matrix Idx Idx K) * ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.isometry,
    hm, ← F.isometry, Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]

theorem conj_omegaRootGL (F : Frame K) {m : GL Idx K}
    (hm : ∀ w, modelQuad K F.a ((m : Matrix Idx Idx K) *ᵥ w) = modelQuad K F.a w)
    (u w : Idx → K) :
    F.P * m * F.P⁻¹ * omegaRootGL F u w * (F.P * m * F.P⁻¹)⁻¹ =
      omegaRootGL F ((m : Matrix Idx Idx K) *ᵥ u) ((m : Matrix Idx Idx K) *ᵥ w) := by
  apply (toLinEquiv Idx K).injective
  have hPP : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) * (F.P : Matrix Idx Idx K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg : toLinEquiv Idx K (F.P * m * F.P⁻¹) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadOdd 3 K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [toLinEquiv_apply, coe_quadOdd]
    exact F.conj_isometry hm x
  have key : ∀ y : Idx → K, toLinEquiv Idx K (F.P * m * F.P⁻¹) (F.lin y) =
      F.lin ((m : Matrix Idx Idx K) *ᵥ y) := by
    intro y
    have h1 : ((F.P⁻¹ : GL Idx K) : Matrix Idx Idx K) *ᵥ ((F.P : Matrix Idx Idx K) *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [toLinEquiv_apply, F.lin_apply, F.lin_apply, Units.val_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1]
  rw [map_mul, map_mul, map_inv, toLinEquiv_omegaRootGL, eichler_conj hg, key, key,
    toLinEquiv_omegaRootGL]

theorem omegaRoot_conj_c₀ [Finite K] (F : Frame K) (v : F3Cube) (u w : Idx → K) :
    c₀ F v * omegaRoot F u w * (c₀ F v)⁻¹ =
      omegaRoot F (rotMat K (Multiplicative.toAdd v) *ᵥ u)
        (rotMat K (Multiplicative.toAdd v) *ᵥ w) := by
  apply Subtype.ext
  have h := conj_omegaRootGL F (m := rotGL K v) (fun w => modelQuad_rotMat_mulVec F.a _ w) u w
  exact h

theorem commute_c₀_omegaRoot [Finite K] (F : Frame K) (v : F3Cube) {u w : Idx → K}
    (hu : rotMat K (Multiplicative.toAdd v) *ᵥ u = u)
    (hw : rotMat K (Multiplicative.toAdd v) *ᵥ w = w) :
    Commute (c₀ F v) (omegaRoot F u w) := by
  have h := omegaRoot_conj_c₀ F v u w
  rw [hu, hw] at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem mem_centralizer_c₀_of_model [Finite K] (F : Frame K) (v : F3Cube) {m : GL Idx K}
    (hmem : F.P * m * F.P⁻¹ ∈ Omega7 K)
    (hc : (m : Matrix Idx Idx K) * rotMat K (Multiplicative.toAdd v) =
      rotMat K (Multiplicative.toAdd v) * (m : Matrix Idx Idx K)) :
    (⟨F.P * m * F.P⁻¹, hmem⟩ : ↥(Omega7 K)) ∈
      Subgroup.centralizer ({c₀ F v} : Set ↥(Omega7 K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hrot : m * rotGL K v = rotGL K v * m := by
    apply Units.ext
    simpa [rotGL, rotHom, Units.val_mul] using hc
  show F.P * m * F.P⁻¹ * c₀GL F v = c₀GL F v * (F.P * m * F.P⁻¹)
  simp only [c₀GL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc F.P * m * F.P⁻¹ * (F.P * rotGL K v * F.P⁻¹)
      = F.P * (m * rotGL K v) * F.P⁻¹ := by group
    _ = F.P * (rotGL K v * m) * F.P⁻¹ := by rw [hrot]
    _ = _ := by group

theorem orderOf_modelElt [Finite K] (F : Frame K) {m : GL Idx K}
    (hmem : F.P * m * F.P⁻¹ ∈ Omega7 K) :
    orderOf (⟨F.P * m * F.P⁻¹, hmem⟩ : ↥(Omega7 K)) = orderOf m := by
  rw [Subgroup.orderOf_mk]
  exact orderOf_injective (MulAut.conj F.P).toMonoidHom (MulAut.conj F.P).injective m

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
