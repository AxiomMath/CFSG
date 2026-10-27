module

public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBQSylowActionInnerTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergBIQuaternionBlockObstruction

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  SteinbergBQ.SylowActionInner

namespace SteinbergBQ.PrimeLinearThree

variable {K : Type*} [Field K]

@[expose] def blockGammaHom : GL (Fin 2) K →* SpecialLinearGroup (Fin 3) K where
  toFun := blockGamma
  map_one' := blockGamma_one
  map_mul' := blockGamma_mul

theorem pow_three_eq_one_of_mem_scalars {s : SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ scalars 3 K) : s ^ 3 = 1 := by
  obtain ⟨u, hu, hsu⟩ := hs
  have hm : ((s ^ 3 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hsu, ← map_pow, ← Units.val_pow_eq_pow_val, hu,
      Units.val_one, map_one]
  exact Subtype.ext hm

theorem conjAut_pow_three_mem (A : GL (Fin 3) K) :
    conjAut 3 K A ^ 3 ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
  set u : Kˣ := Matrix.GeneralLinearGroup.det A
  set B : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A ^ 3
  have hB : (B : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det B = 1 := by
      rw [map_mul, map_pow]
      have h2 : Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) u⁻¹) =
          u⁻¹ ^ 3 := by
        rw [GeneralLinearGroup.det_scalar, Fintype.card_fin]
      rw [h2, ← mul_pow, inv_mul_cancel, one_pow]
    have h3 := congrArg Units.val h1
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h3
  set B₁ : SpecialLinearGroup (Fin 3) K := ⟨B, hB⟩
  have hB₁ : Matrix.SpecialLinearGroup.toGL B₁ = B := Units.ext rfl
  have hA3 : A ^ 3 = GeneralLinearGroup.scalar (Fin 3) u * B := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨proj 3 K B₁, ?_⟩
  rw [← map_pow, hA3, map_mul, conjAut_scalar, one_mul, ← hB₁, conjAut_toGL]

end SteinbergBQ.PrimeLinearThree

open SteinbergBQ.PrimeLinearThree

variable {K : Type*} [Field K]

end CFSG.QuasithinUnique
