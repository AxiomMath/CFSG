module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldUnipotent

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F] [Finite F] [CharP F 2]

theorem pgroup_fixedSL2_card_le (sigma : RingAut F) (B : Subgroup SL(2, F))
    (hB : IsPGroup 2 B) (hle : B ≤ fixedSL2 sigma) :
    Nat.card B ≤ Nat.card (fixedField sigma) := by
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) (fixedField sigma).subtype
  have hf : Function.Injective f := sl2_map_injective _
  have hmap : (B.comap f).map f = B := Subgroup.map_comap_eq_self hle
  have hp : IsPGroup 2 (B.comap f) := hB.comap_of_injective f hf
  calc
    Nat.card B = Nat.card (B.comap f) := by
      nth_rw 1 [← hmap]
      exact (Nat.card_congr ((B.comap f).equivMapOfInjective f hf).toEquiv).symm
    _ ≤ Nat.card (fixedField sigma) := pgroup_sl2_card_le (B.comap f) hp

theorem pgroup_conjugate_fixedSL2_card_le (sigma : RingAut F) (x : SL(2, F))
    (B : Subgroup SL(2, F)) (hB : IsPGroup 2 B)
    (hle : B ≤ (fixedSL2 sigma).map (MulAut.conj x).toMonoidHom) :
    Nat.card B ≤ Nat.card (fixedField sigma) := by
  let C := B.map (MulAut.conj x⁻¹).toMonoidHom
  have hC : C ≤ fixedSL2 sigma := by
    rintro y ⟨b, hb, rfl⟩
    have hm := hle hb
    rw [Subgroup.mem_map_equiv] at hm
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_symm_apply,
      MulAut.conj_apply, inv_inv] using hm
  calc
    Nat.card B = Nat.card C :=
      Nat.card_congr (B.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv
    _ ≤ Nat.card (fixedField sigma) :=
      pgroup_fixedSL2_card_le sigma C (hB.map _) hC

theorem pgroup_outer_centralizer_card_le (a : Gamma F) (ha : orderOf a = 2)
    (houter : a ∉ linearKernel F) (B : Subgroup SL(2, F))
    (hB : IsPGroup 2 B) (hle : B ≤ centralizerS a) :
    Nat.card B ≤ Nat.card (fixedField a.right) := by
  obtain ⟨x, _hx, hc⟩ := outer_involution_conjugator_and_centralizer a ha houter
  exact pgroup_conjugate_fixedSL2_card_le a.right x B hB (hc ▸ hle)

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
