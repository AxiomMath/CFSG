
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable Subgroup

theorem cv_substWord (hs : List (List (Fin 2 × Bool))) (w : List (Fin 2 × Bool)) :
    FreeGroup.lift (fun i : Fin 2 => cv (hs.getD i [])) (FreeGroup.mk w) = cv (substWord hs w) :=
  lift_substWord hs w

theorem r₄_mul_self : r₄ * r₄ = 1 := by
  have h := pow_orderOf_eq_one r₄R
  rw [orderOf_r₄R, pow_two] at h
  exact congrArg Subtype.val h

theorem r₂_mul_self : r₂ * r₂ = 1 := by
  have h := pow_orderOf_eq_one r₂R
  rw [orderOf_r₂R, pow_two] at h
  exact congrArg Subtype.val h

theorem r₃_mul_self : r₃ * r₃ = 1 := by
  have h := pow_orderOf_eq_one r₃R
  rw [orderOf_r₃R, pow_two] at h
  exact congrArg Subtype.val h

section Extension

variable {E : Type*} [Group E]

end Extension

end CFSG.ComponentClassification.GrSLit.L34Facts
