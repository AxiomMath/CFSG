module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetMax

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega.E7RootSet

open Certificates.OmegaSevenMax

private theorem polar_sep : ∀ x : V, (∀ k : Fin 7, polarV x (Pi.single k 1) = 0) → x = 0 := by
  decide +kernel

theorem e7QForm_nondegenerate : qForm.Nondegenerate := by
  have hsep : ∀ x : V, (∀ y : V, QuadraticMap.polar qForm x y = 0) → x = 0 := by
    intro x hx
    refine polar_sep x fun k => ?_
    rw [← polar_qForm]
    exact hx _
  refine QuadraticMap.nondegenerate_polar_iff.mp ⟨fun x hx => hsep x fun y => ?_,
    fun y hy => hsep y fun x => ?_⟩
  · have h := hx y
    rwa [QuadraticMap.polarBilin_apply_apply] at h
  · have h := hy x
    rw [QuadraticMap.polarBilin_apply_apply] at h
    rw [QuadraticMap.polar_comm]
    exact h

theorem isCoatom_stabilizer_rootSet'
    (hStab : Nat.card (MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet) = 1451520) :
    IsCoatom (MulAction.stabilizer (omegaGroup e7QForm_nondegenerate) rootSet) :=
  isCoatom_stabilizer_rootSet e7QForm_nondegenerate hStab

end CFSG.OddStandard.SmallF3.Omega.E7RootSet

end
