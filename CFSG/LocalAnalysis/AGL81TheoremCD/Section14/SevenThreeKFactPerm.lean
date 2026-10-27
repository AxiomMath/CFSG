module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

@[expose] def vA9Perm : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 4 5 *
    Equiv.swap 6 7 * Equiv.swap 7 8

@[expose] def tA9Perm : Equiv.Perm (Fin 9) :=
  Equiv.swap 0 3 * Equiv.swap 3 6 * Equiv.swap 1 4 * Equiv.swap 4 7 *
    Equiv.swap 2 5 * Equiv.swap 5 8

@[expose] def vA9 : alternatingGroup (Fin 9) :=
  ⟨vA9Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

@[expose] def tA9 : alternatingGroup (Fin 9) :=
  ⟨tA9Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem vA9_pow_three : vA9 ^ 3 = 1 :=
  Subtype.ext (by
    show vA9Perm ^ 3 = 1
    decide +kernel)

theorem tA9_pow_three : tA9 ^ 3 = 1 :=
  Subtype.ext (by
    show tA9Perm ^ 3 = 1
    decide +kernel)

theorem commute_vA9_tA9 : Commute vA9 tA9 := by
  show vA9 * tA9 = tA9 * vA9
  exact Subtype.ext (by
    show vA9Perm * tA9Perm = tA9Perm * vA9Perm
    decide +kernel)

theorem vA9_ne_one : vA9 ≠ 1 := by
  decide +kernel

private def cTVPerm : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 8 * Equiv.swap 8 3 * Equiv.swap 2 4 * Equiv.swap 4 6

theorem isConj_tA9_vA9 : IsConj tA9 vA9 := by
  refine isConj_iff.mpr
    ⟨⟨cTVPerm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cTVPerm * tA9Perm * cTVPerm⁻¹ = vA9Perm
  decide +kernel

private def cVTPerm : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 7 * Equiv.swap 7 4 * Equiv.swap 2 5 * Equiv.swap 5 8

theorem isConj_vA9_mul_tA9 : IsConj (vA9 * tA9) vA9 := by
  refine isConj_iff.mpr
    ⟨⟨cVTPerm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cVTPerm * (vA9Perm * tA9Perm) * cVTPerm⁻¹ = vA9Perm
  decide +kernel

private def cVT2Perm : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 4 * Equiv.swap 4 7 * Equiv.swap 2 8 * Equiv.swap 8 5

theorem isConj_vA9_mul_tA9_sq : IsConj (vA9 * tA9 ^ 2) vA9 := by
  refine isConj_iff.mpr
    ⟨⟨cVT2Perm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cVT2Perm * (vA9Perm * tA9Perm ^ 2) * cVT2Perm⁻¹ = vA9Perm
  decide +kernel

private def cInvPerm : Equiv.Perm (Fin 9) :=
  Equiv.swap 1 2 * Equiv.swap 3 6 * Equiv.swap 4 8 * Equiv.swap 5 7

theorem isConj_vA9_inv : IsConj vA9 vA9⁻¹ := by
  refine isConj_iff.mpr
    ⟨⟨cInvPerm, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩, ?_⟩
  apply Subtype.ext
  show cInvPerm * vA9Perm * cInvPerm⁻¹ = vA9Perm⁻¹
  decide +kernel

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
