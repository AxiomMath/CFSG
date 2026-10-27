module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.OrthCentGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open CFSG.LocalAnalysis.GLTheoremB CFSG.Assembly.LowTwoRank QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem statedOmegaPlusEquiv_coe {m : ℕ} (hm : 3 ≤ m)
    (y : ↥(StatedOmega (StatedQuadPlus m (ZMod 2)))) :
    ((statedOmegaPlusEquiv hm y : ↥(elementaryGroup (quadPlus m (ZMod 2)))) :
        (Fin m ⊕ Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) =
      toLinEquiv (Fin m ⊕ Fin m) (ZMod 2) (y : GL (Fin m ⊕ Fin m) (ZMod 2)) := rfl

theorem statedOmegaMinusEquiv_coe {m : ℕ} (hm : 2 ≤ m)
    (y : ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :
    ((statedOmegaMinusEquiv hm y : ↥(elementaryGroup (quadMinus m (ZMod 2) 1 1))) :
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)) =
      toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)
        (y : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) := rfl

theorem statedOmegaPlusEquiv_conj {m : ℕ} (hm : 3 ≤ m) (t : GL (Fin m ⊕ Fin m) (ZMod 2))
    (ht : t ∈ Subgroup.normalizer (StatedOmega (StatedQuadPlus m (ZMod 2)) :
      Set (GL (Fin m ⊕ Fin m) (ZMod 2))))
    (y : ↥(StatedOmega (StatedQuadPlus m (ZMod 2)))) :
    ((statedOmegaPlusEquiv hm
        ((StatedOmega (StatedQuadPlus m (ZMod 2))).normalizerMonoidHom ⟨t, ht⟩ y) :
          ↥(elementaryGroup (quadPlus m (ZMod 2)))) :
        (Fin m ⊕ Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) =
      toLinEquiv (Fin m ⊕ Fin m) (ZMod 2) t *
        ((statedOmegaPlusEquiv hm y : ↥(elementaryGroup (quadPlus m (ZMod 2)))) :
          (Fin m ⊕ Fin m → ZMod 2) ≃ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)) *
        (toLinEquiv (Fin m ⊕ Fin m) (ZMod 2) t)⁻¹ := by
  rw [statedOmegaPlusEquiv_coe, statedOmegaPlusEquiv_coe]
  have : (((StatedOmega (StatedQuadPlus m (ZMod 2))).normalizerMonoidHom ⟨t, ht⟩ y :
      ↥(StatedOmega (StatedQuadPlus m (ZMod 2)))) : GL (Fin m ⊕ Fin m) (ZMod 2)) =
      t * (y : GL (Fin m ⊕ Fin m) (ZMod 2)) * t⁻¹ := by
    simp
  rw [this, map_mul, map_mul, map_inv]

theorem statedOmegaMinusEquiv_conj {m : ℕ} (hm : 2 ≤ m)
    (t : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2))
    (ht : t ∈ Subgroup.normalizer (StatedOmega (StatedQuadMinus m (ZMod 2) 1 1) :
      Set (GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2))))
    (y : ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :
    ((statedOmegaMinusEquiv hm
        ((StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)).normalizerMonoidHom ⟨t, ht⟩ y) :
          ↥(elementaryGroup (quadMinus m (ZMod 2) 1 1))) :
        (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)) =
      toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2) t *
        ((statedOmegaMinusEquiv hm y : ↥(elementaryGroup (quadMinus m (ZMod 2) 1 1))) :
          (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
            (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)) *
        (toLinEquiv (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2) t)⁻¹ := by
  rw [statedOmegaMinusEquiv_coe, statedOmegaMinusEquiv_coe]
  have : (((StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)).normalizerMonoidHom ⟨t, ht⟩ y :
      ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1))) :
        GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) =
      t * (y : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) * t⁻¹ := by
    simp
  rw [this, map_mul, map_mul, map_inv]

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
