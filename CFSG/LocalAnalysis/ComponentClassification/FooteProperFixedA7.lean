module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFourgroupA7

public noncomputable section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup Equiv
open CFSG.ComponentClassification.AutL2Facts

abbrev fixedSubgroup {X : Type*} [Group X] (a : MulAut X) : Subgroup X :=
  CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup a

abbrev innAut (X : Type*) [Group X] : Subgroup (MulAut X) :=
  (MulAut.conj : X →* MulAut X).range

theorem congr_mem_innAut_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (f : MulAut X) : MulAut.congr e f ∈ innAut Y ↔ f ∈ innAut X := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply (MulAut.congr e).injective
    rw [congr_conj_eq, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (congr_conj_eq e x).symm⟩

end CFSG.ComponentClassification.FooteLit
