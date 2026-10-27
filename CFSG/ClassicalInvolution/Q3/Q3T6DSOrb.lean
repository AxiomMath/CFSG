module

public import CFSG.ClassicalInvolution.Q3.Q3T6DSHyp
public import CFSG.ClassicalInvolution.Q3.Q3T6DSFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

@[expose] def Res20_7Hyp51AtThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [FrameSimple G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20Three K K' J S R R' W V z t →
      Concl20_4 S K K' J z → ∀ a : G,
        a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J → a ≠ 1 →
          a * a = 1 →
            Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a ∧
              Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)

namespace Std20Three

variable (d : Std20Three K K' J S R R' W V z t) {a : G} (h : AConf3 S K K' J z a)
include d h

theorem s_hyp51_of_at (ha : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a)
    (haz : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)) :
    Hyp51 (Subgroup.closure ({z, t, a} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_hyp51_of_at_of (d.s_exists_rho_a h)
    d.viol.hzK.sq d.viol.hzJ.sq h.ha2 d.late_zt_comm (d.s_comm_z h.hA.1.1).symm
    (d.s_comm_t h.hA).symm
    (d.s_B_isElemAbelian h.hA h.ha2) (d.s_B_natCard h.c4 h.hA h.ha1 h.ha2) (d.s_hyp51At_z h)
    ha haz

end Std20Three

theorem res20_7Hyp51_of_atThree (hH : Res20_7Hyp51AtThree) : Res20_7Hyp51Three := by
  intro G _ _ _ K K' J S R R' W V z t d c4 a ha ha1 ha2
  obtain ⟨hA, hAz⟩ := hH G K K' J S R R' W V z t d c4 a ha ha1 ha2
  exact d.s_hyp51_of_at ⟨ha, ha1, ha2, c4⟩ hA hAz

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
