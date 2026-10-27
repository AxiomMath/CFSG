module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.Q3T6D

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem isSolvable_of_twoGroup_oddCore {M : Subgroup G}
    (h : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) : Group.IsSolvable ↥M := by
  have hq : Group.IsSolvable (↥M ⧸ classicalInvolutionOddCore ↥M) := by
    have : Group.IsNilpotent (↥M ⧸ classicalInvolutionOddCore ↥M) := h.isNilpotent
    infer_instance
  have ho : Group.IsSolvable ↥(classicalInvolutionOddCore ↥M) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card ↥M)
  exact Group.isSolvable_of_ker_le_range (classicalInvolutionOddCore ↥M).subtype
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥M))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem Std20Frame.isSolvable_member (d : Std20Frame K K' J S R R' W V z t) {M : Subgroup G}
    (hM : M ∈ CoreAssembly.conjClass K) : Group.IsSolvable ↥M := by
  have hK : Group.IsSolvable ↥K := isSolvable_of_twoGroup_oddCore d.twoGroup
  obtain ⟨g, rfl⟩ := hM
  let e : ↥K ≃* ↥(conjSub g K) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
