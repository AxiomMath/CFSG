module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterFix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryDecomp

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ProperTwoGeneratedCore.RootCenter
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K]

theorem fix_rootCenter_of_sq_mem_conj [Finite K] (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγR : (unitaryCoverRoot J hJ).map γ.toMonoidHom = unitaryCoverRoot J hJ)
    (hγ2 : γ ^ 2 ∈ (unitaryCoverRoot J hJ).map MulAut.conj) :
    ∀ u ∈ unitaryRootCenter J hJ, γ u = u := by
  have : CharP K 2 := charP_two_of_card f hcard
  have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  obtain ⟨σ, A, -, hrep⟩ := exists_isometry_psu_of_card Nat.prime_two hq hcard hfixed hJ γ
  have hσc : ∀ x, σ (J.conj x) = J.conj (σ x) := conj_comm_of_frobenius J hcard hfixed σ
  have hact : ∀ z w : hermitianUnipotentCoord J,
      γ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ w →
        A * hermitianUnipotentGL J (sigmaCoord J σ hσc z) * A⁻¹ = hermitianUnipotentGL J w := by
    intro z w hzw
    obtain ⟨hm, h⟩ := hrep ⟨hermitianUnipotentGL J z, hermitianUnipotentGL_mem J hJ z⟩
    rw [← hermitianUnipotentPSU_eq_psuMk J hJ, hzw] at h
    have hX : ((glAut σ (hermitianUnipotentGL J z) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).trace = 1 := by
      rw [glAut_hermitianUnipotentGL J σ hσc, hermitianUnipotentGL_val,
        trace_hermitianUnipotentMatrix]
    have := conj_eq_of_psuMk_eq J hJ hX hm w h.symm
    rwa [glAut_hermitianUnipotentGL J σ hσc] at this
  have hroot : ∀ z : hermitianUnipotentCoord J, ∃ w,
      γ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ w := by
    intro z
    have hmem : γ (hermitianUnipotentPSU J hJ z) ∈ unitaryCoverRoot J hJ := by
      rw [← hγR]
      exact Subgroup.mem_map_of_mem _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hmem
    exact ⟨w, hw.symm⟩
  have hcenter : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ∃ w : hermitianUnipotentCoord J,
      w.1.1 = 0 ∧ γ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ w := by
    intro z hz
    have hzU : hermitianUnipotentPSU J hJ z ∈ unitaryRootCenter J hJ :=
      ⟨z, (mem_ker_firstCoord J).mpr hz, rfl⟩
    rw [mem_unitaryRootCenter_iff J hJ f hcard hfixed] at hzU
    have hγU : γ (hermitianUnipotentPSU J hJ z) ∈ unitaryRootCenter J hJ := by
      rw [mem_unitaryRootCenter_iff J hJ f hcard hfixed]
      refine ⟨by rw [← hγR]; exact Subgroup.mem_map_of_mem _ hzU.1, fun y hy => ?_⟩
      rw [← hγR] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      change γ _ * γ y' = γ y' * γ _
      rw [← map_mul, ← map_mul, hzU.2 y' hy']
    obtain ⟨w, hw, hw'⟩ := hγU
    exact ⟨w, (mem_ker_firstCoord J).mp hw, hw'.symm⟩
  obtain ⟨w₁, hw₁0, hw₁⟩ := hcenter (coordZeroOne J) rfl
  have hσz₁ : sigmaCoord J σ hσc (coordZeroOne J) = coordZeroOne J :=
    coord_ext (by simp [sigmaCoord, coordZeroOne]) (by simp [sigmaCoord, coordZeroOne])
  have hAN : (A : Matrix (Fin 3) (Fin 3) K) * rootE *
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = w₁.1.2 • rootE := by
    have h := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) (hact _ _ hw₁)
    simp only [hσz₁, Units.val_mul, hermitianUnipotentGL_val] at h
    rw [hermitianUnipotentMatrix_of_fst_eq_zero J (show (coordZeroOne J).1.1 = 0 from rfl),
      hermitianUnipotentMatrix_of_fst_eq_zero J hw₁0, conj_one_add_smul] at h
    simpa [coordZeroOne] using add_left_cancel h
  have hU : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ∃ w : hermitianUnipotentCoord J,
      w.1.1 = 0 ∧ w.1.2 = w₁.1.2 * σ z.1.2 ∧
        γ (hermitianUnipotentPSU J hJ z) = hermitianUnipotentPSU J hJ w := by
    intro z hz
    obtain ⟨w, hw0, hw⟩ := hcenter z hz
    refine ⟨w, hw0, ?_, hw⟩
    have h := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) (hact z w hw)
    have hσz0 : (sigmaCoord J σ hσc z).1.1 = 0 := by simp [sigmaCoord, hz]
    simp only [Units.val_mul, hermitianUnipotentGL_val] at h
    rw [hermitianUnipotentMatrix_of_fst_eq_zero J hσz0,
      hermitianUnipotentMatrix_of_fst_eq_zero J hw0, conj_one_add_smul, hAN] at h
    have h' := congrFun (congrFun (add_left_cancel (G := Matrix (Fin 3) (Fin 3) K) h) 0) 2
    simp [sigmaCoord] at h'
    linear_combination -h'
  obtain ⟨r, ⟨y, rfl⟩, hγr⟩ := hγ2
  have hγγ : ∀ x, γ (γ x) =
      hermitianUnipotentPSU J hJ y * x * (hermitianUnipotentPSU J hJ y)⁻¹ := by
    intro x
    have h := DFunLike.congr_fun hγr x
    rw [MulAut.conj_apply, pow_two, MulAut.mul_apply] at h
    exact h.symm
  set B : GL (Fin 3) K := (hermitianUnipotentGL J y)⁻¹ * A * glAut σ A with hBdef
  have hBQ : ∀ z : hermitianUnipotentCoord J,
      B * hermitianUnipotentGL J (sigmaCoord J σ hσc (sigmaCoord J σ hσc z)) =
        hermitianUnipotentGL J z * B := by
    intro z
    obtain ⟨w, hw⟩ := hroot z
    obtain ⟨w', hw'⟩ := hroot w
    have h1 := hact z w hw
    have h2 := hact w w' hw'
    have hw'' : w' = y * z * y⁻¹ := by
      apply CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
      rw [← hw', ← hw, hγγ, map_mul, map_mul, map_inv]
    have hQ : ∀ a b : hermitianUnipotentCoord J,
        hermitianUnipotentGL J (a * b) = hermitianUnipotentGL J a * hermitianUnipotentGL J b :=
      fun a b => congrArg Subtype.val (map_mul (hermitianUnipotentSU J hJ) a b)
    have hQinv : ∀ a : hermitianUnipotentCoord J,
        hermitianUnipotentGL J a⁻¹ = (hermitianUnipotentGL J a)⁻¹ :=
      fun a => congrArg Subtype.val (map_inv (hermitianUnipotentSU J hJ) a)
    have hσw : hermitianUnipotentGL J (sigmaCoord J σ hσc w) =
        glAut σ A * hermitianUnipotentGL J (sigmaCoord J σ hσc (sigmaCoord J σ hσc z)) *
          (glAut σ A)⁻¹ := by
      rw [← glAut_hermitianUnipotentGL J σ hσc w, ← h1, map_mul, map_mul, map_inv,
        glAut_hermitianUnipotentGL J σ hσc (sigmaCoord J σ hσc z)]
    rw [hσw, hw'', hQ, hQ, hQinv] at h2
    have h3 : hermitianUnipotentGL J z = (hermitianUnipotentGL J y)⁻¹ *
        (A * (glAut σ A * hermitianUnipotentGL J (sigmaCoord J σ hσc (sigmaCoord J σ hσc z)) *
          (glAut σ A)⁻¹) * A⁻¹) * hermitianUnipotentGL J y := by
      rw [h2]; group
    rw [h3, hBdef]
    group
  have hBM : ∀ z : hermitianUnipotentCoord J,
      (B : Matrix (Fin 3) (Fin 3) K) *
          hermitianUnipotentMatrix J (sigmaCoord J σ hσc (sigmaCoord J σ hσc z)) =
        hermitianUnipotentMatrix J z * (B : Matrix (Fin 3) (Fin 3) K) := fun z => by
    have h := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) (hBQ z)
    simpa only [Units.val_mul, hermitianUnipotentGL_val] using h
  have hσσz₁ : sigmaCoord J σ hσc (sigmaCoord J σ hσc (coordZeroOne J)) = coordZeroOne J := by
    rw [hσz₁, hσz₁]
  have hB₁ := hBM (coordZeroOne J)
  rw [hσσz₁, hermitianUnipotentMatrix_of_fst_eq_zero J (show (coordZeroOne J).1.1 = 0 from rfl)]
    at hB₁
  simp only [coordZeroOne, one_smul] at hB₁
  obtain ⟨hb20, hb21, hb10, hb00⟩ := entries_of_comm_one_add_rootE hB₁
  have hconjσσ : ∀ a : K, (B : Matrix (Fin 3) (Fin 3) K) 1 1 * J.conj (σ (σ a)) =
      J.conj a * (B : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    intro a
    obtain ⟨z, hz⟩ := exists_fst_eq J (2 ^ f) hcard hfixed a
    have h := entry_one_two_of_comm J hb10 (hBM z)
    simpa [sigmaCoord, hz] using h
  have hb11 : (B : Matrix (Fin 3) (Fin 3) K) 1 1 = (B : Matrix (Fin 3) (Fin 3) K) 2 2 := by
    simpa using hconjσσ 1
  have hb22 : (B : Matrix (Fin 3) (Fin 3) K) 2 2 ≠ 0 := by
    intro h0
    have hdet := (Matrix.GeneralLinearGroup.det B).ne_zero
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_three, hb20, hb21, h0] at hdet
    exact hdet (by ring)
  have hσσ : σ * σ = 1 := by
    refine RingEquiv.ext fun a => ?_
    have h := hconjσσ a
    rw [hb11] at h
    have h' : J.conj (σ (σ a)) = J.conj a := by
      have := mul_left_cancel₀ hb22 (h.trans (mul_comm _ _))
      exact this
    exact J.conj.injective h'
  have hfix : ∀ b : K, J.conj b = b → σ b = b := fun b hb =>
    ringEquiv_apply_eq_self_of_mul_self J (by omega) hcard hfixed hσσ hb
  have hν : w₁.1.2 = 1 := by
    obtain ⟨w₂, -, hw₂, hγw₂⟩ := hU w₁ hw₁0
    have hcent : γ (γ (hermitianUnipotentPSU J hJ (coordZeroOne J))) =
        hermitianUnipotentPSU J hJ (coordZeroOne J) := by
      rw [hγγ, ← map_inv, ← map_mul, ← map_mul,
        ← mul_comm_of_fst_eq_zero J (show (coordZeroOne J).1.1 = 0 from rfl) y,
        mul_inv_cancel_right]
    rw [hw₁, hγw₂] at hcent
    have h2 := congrArg (fun w : hermitianUnipotentCoord J => w.1.2)
      (CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ hcent)
    simp only [hw₂, hfix _ (conj_snd_of_fst_eq_zero J hw₁0), coordZeroOne] at h2
    have h3 : (w₁.1.2 - 1) ^ 2 = 0 := by
      have : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination h2 + (1 - w₁.1.2) * this
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3)
  rintro _ ⟨z, hz, rfl⟩
  have hz0 : z.1.1 = 0 := (mem_ker_firstCoord J).mp hz
  obtain ⟨w, hw0, hw2, hγw⟩ := hU z hz0
  rw [hγw]
  congr 1
  refine coord_ext (by rw [hw0, hz0]) ?_
  rw [hw2, hν, one_mul, hfix _ (conj_snd_of_fst_eq_zero J hz0)]

end CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter
