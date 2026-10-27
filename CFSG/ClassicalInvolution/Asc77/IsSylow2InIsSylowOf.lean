module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] {V P : Subgroup G}

theorem IsSylow2In.of_isSylowOf [Finite G] (h : CFSG.ABGLocalTools.IsSylowOf 2 V P) :
    IsSylow2In V P :=
  ⟨h.le, h.isPGroup, fun _ hV'P hV'2 hle => h.eq_of_le hle hV'P hV'2⟩

end CFSG.ClassicalInvolution.Asc77
