module

public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Sect

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rLayer_le_exactLayer (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : c * c = 1) :
    rLayer Ω c ≤ ExactLayer.exactLayer Ω c := by
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  unfold rLayer
  refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
  obtain ⟨J, hJΩ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJtq : J ∈ ExactLayer.tqMembers Ω c :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hc2').mpr ⟨hJΩ, R, hRJ, hRc⟩
  have hRcore : R ≤ ExactLayer.exactCore c J := fun x hx => ⟨hRJ.1 hx, hRc hx⟩
  exact hRcore.trans (ExactLayer.exactCore_le_exactLayer hJtq)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
