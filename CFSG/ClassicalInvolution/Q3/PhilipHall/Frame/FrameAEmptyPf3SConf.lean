module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3Close
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Frame

variable (d : Std20Frame K K' J S R R' W V z t)
include d

theorem s_comm_z {a : G} (haS : a ∈ (S : Subgroup G)) : a * z = z * a :=
  Subgroup.mem_centralizer_singleton_iff.mp (d.hSz haS)

theorem s_a_not_mem_closure (c4 : Concl20_4 S K K' J z) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) (ha1 : a ≠ 1) :
    a ∉ Subgroup.closure ({z, t} : Set G) := by
  obtain ⟨r, hr, r', hr', -, hrt⟩ := d.late_tor d.late_JW d.late_hW
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_a_not_mem_closure_of d.viol.hzK
    d.viol.hzJ.sq d.late_zt_comm ⟨r, d.hR.1 hr, d.hRS hr, hrt⟩ c4 ha ha1

theorem s_comm_t {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) :
    a * t = t * a := d.cent_comm_t ha.1

theorem s_B_isElemAbelian {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J)
    (ha2 : a * a = 1) : IsElemAbelian 2 (Subgroup.closure ({z, t, a} : Set G)) :=
  isElemAbelian_closure_three d.viol.hzK.sq d.viol.hzJ.sq ha2 d.late_zt_comm
    (d.s_comm_z ha.1.1).symm (d.s_comm_t ha).symm

theorem s_B_natCard (c4 : Concl20_4 S K K' J z) {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) (ha1 : a ≠ 1)
    (ha2 : a * a = 1) : Nat.card ↥(Subgroup.closure ({z, t, a} : Set G)) = 8 :=
  natCard_closure_three d.viol.hzK.sq d.viol.hzJ.sq ha2 d.viol.hzK.ne_one d.viol.hzJ.ne_one ha1
    d.late_ne_inv.symm d.late_zt_comm (d.s_comm_z ha.1.1).symm (d.s_comm_t ha).symm
    (d.s_a_not_mem_closure c4 ha ha1)

theorem s_comm_K {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) {k : G}
    (hk : k ∈ K) : ⁅a, k⁆ ∈ oddCoreOf K := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.comm_mem_oddCoreOf_of le_sup_left ha.1
    (d.cent_le_normalizer ha.1) hk

theorem s_comm_K' {a : G}
    (ha : a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J) {k : G}
    (hk : k ∈ K') : ⁅a, k⁆ ∈ oddCoreOf K' := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.comm_mem_oddCoreOf_of le_sup_right ha.1
    (d.cent_le_normalizer' ha.1) hk

end Std20Frame

end Std


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
