module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldArithmetic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldConjugacy

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F]

def fixedSL2 (sigma : RingAut F) : Subgroup SL(2, F) :=
  (Matrix.SpecialLinearGroup.map (fixedField sigma).subtype).range

theorem sl2_map_injective {K : Type u} [Field K] (f : K →+* F) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) f) := by
  intro a b hab
  ext i j
  apply f.injective
  exact congrFun (congrFun (congrArg
    (fun h : SL(2, F) => (h : Matrix (Fin 2) (Fin 2) F)) hab) i) j

theorem sl2_field_fixed_iff (sigma : RingAut F) (h : SL(2, F)) :
    sl2FieldAction sigma h = h ↔ h ∈ fixedSL2 sigma := by
  constructor
  · intro hh
    have hentry (i j : Fin 2) : sigma (h i j) = h i j :=
      congrFun (congrFun (congrArg
        (fun h : SL(2, F) => (h : Matrix (Fin 2) (Fin 2) F)) hh) i) j
    let B : Matrix (Fin 2) (Fin 2) (fixedField sigma) :=
      fun i j => ⟨h i j, (mem_fixedField_iff sigma _).mpr (hentry i j)⟩
    have hBdet : B.det = 1 := by
      apply (fixedField sigma).subtype.injective
      rw [map_one, RingHom.map_det]
      exact h.2
    exact ⟨⟨B, hBdet⟩, by ext i j; rfl⟩
  · rintro ⟨B, rfl⟩
    ext i j
    exact (mem_fixedField_iff sigma _).mp (B i j).2

theorem pure_field_centralizer (sigma : RingAut F) :
    centralizerS (SemidirectProduct.inr sigma : Gamma F) = fixedSL2 sigma := by
  ext h
  rw [mem_centralizerS_iff]
  constructor
  · intro hh
    apply (sl2_field_fixed_iff sigma h).mp
    simpa using (congrArg SemidirectProduct.left hh).symm
  · intro hh
    apply SemidirectProduct.ext
    · simpa using (sl2_field_fixed_iff sigma h).mpr hh |>.symm
    · simp

theorem centralizerS_conjugate (a : Gamma F) (x : SL(2, F)) :
    centralizerS ((SemidirectProduct.inl x : Gamma F) * a * (SemidirectProduct.inl x)⁻¹) =
      (centralizerS a).map (MulAut.conj x).toMonoidHom := by
  ext h
  rw [Subgroup.mem_map_equiv]
  simp only [mem_centralizerS_iff, MulAut.conj_symm_apply, map_mul, map_inv]
  let c : Gamma F := SemidirectProduct.inl x
  let b : Gamma F := SemidirectProduct.inl h
  change b * (c * a * c⁻¹) = (c * a * c⁻¹) * b ↔
    (c⁻¹ * b * c) * a = a * (c⁻¹ * b * c)
  constructor
  · intro heq
    have := congrArg (fun y : Gamma F => c⁻¹ * y * c) heq
    simpa [mul_assoc] using this
  · intro heq
    have := congrArg (fun y : Gamma F => c * y * c⁻¹) heq
    simpa [mul_assoc] using this

theorem outer_involution_conjugator_and_centralizer [CharP F 2]
    (a : Gamma F) (ha : orderOf a = 2) (houter : a ∉ linearKernel F) :
    ∃ x : SL(2, F),
      a = (SemidirectProduct.inl x : Gamma F) * SemidirectProduct.inr a.right *
        (SemidirectProduct.inl x)⁻¹ ∧
      centralizerS a = (fixedSL2 a.right).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨x, hx⟩ := outer_involution_sl2_conjugate a ha houter
  refine ⟨x, hx, ?_⟩
  nth_rw 1 [hx]
  rw [centralizerS_conjugate, pure_field_centralizer]

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
