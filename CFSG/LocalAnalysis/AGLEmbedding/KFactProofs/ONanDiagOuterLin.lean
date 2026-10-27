module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanDiagOuterBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.AGLEmbedding.KFactProofs.ThreeWeak

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem hasDiagOuterThree_projectiveSL {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    (h3n : 3 ∣ n) (h3q : 3 ∣ Nat.card K - 1) : HasDiagOuterThree (projectiveSL n K) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨μ, hμ⟩ := exists_not_cube h3q
  obtain ⟨A, hA⟩ := GeneralLinearGroup.det_surjective (n := Fin n) μ
  refine ⟨conjAut n K A, fun k hk => ?_⟩
  obtain ⟨x, hx⟩ := hk
  obtain ⟨s, rfl⟩ := proj_surjective n K x
  have h1 : conjAut n K (A ^ 2 ^ k * (SpecialLinearGroup.toGL s)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_pow, conjAut_toGL, hx, mul_inv_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn
    (A ^ 2 ^ k * (SpecialLinearGroup.toGL s)⁻¹) 1 (by rw [map_one, mul_one, h1])
  have hdet := congrArg Matrix.GeneralLinearGroup.det hc
  rw [Matrix.GeneralLinearGroup.det_scalar, map_mul, map_pow, hA, map_inv,
    Matrix.SpecialLinearGroup.coeToGL_det, inv_one, mul_one, Fintype.card_fin] at hdet
  obtain ⟨m, hm⟩ := h3n
  have hcube : μ ^ 2 ^ k = (c ^ m) ^ 3 := by
    rw [← hdet, hm, ← pow_mul, mul_comm]
  obtain ⟨z, hz⟩ := isCube_of_pow_eq_cube (Nat.Coprime.pow_left k (by norm_num)) hcube
  exact hμ z hz

end CFSG.AGLEmbedding.KFactProofs.ThreeWeak
