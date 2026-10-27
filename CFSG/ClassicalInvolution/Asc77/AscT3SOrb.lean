module

public import CFSG.ClassicalInvolution.Asc77.AscT3SHyp
public import CFSG.ClassicalInvolution.Asc77.AscT3SOrbEng
public import CFSG.ClassicalInvolution.Asc77.AscT3SFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Orb

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


@[expose] def Res20_7Hyp51At (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_4 S K K' J z → ∀ a : G,
        a ∈ centralizerModOdd (centralizerModOdd (S : Subgroup G) (K ⊔ K')) J → a ≠ 1 →
          a * a = 1 →
            Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a ∧
              Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t) {a : G} (h : AConf S K K' J z a)
include d h

theorem s_hyp51_of_at (ha : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) a)
    (haz : Hyp51At (Subgroup.closure ({z, t, a} : Set G)) (a * z)) :
    Hyp51 (Subgroup.closure ({z, t, a} : Set G)) := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.s_hyp51_of_at_of (d.s_exists_rho_a h)
    d.viol.hzK.sq d.viol.hzJ.sq h.ha2 d.late_zt_comm (d.s_comm_z h.hA.1.1).symm
    (d.s_comm_t h.hA).symm
    (d.s_B_isElemAbelian h.hA h.ha2) (d.s_B_natCard h.c4 h.hA h.ha1 h.ha2) (d.s_hyp51At_z h)
    ha haz

end Std20

theorem res20_7Hyp51_of_at (hH : Res20_7Hyp51At p f) : Res20_7Hyp51 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c4 a ha ha1 ha2
  obtain ⟨hA, hAz⟩ := hH G K K' J S R R' W V z t d c4 a ha ha1 ha2
  exact d.s_hyp51_of_at ⟨ha, ha1, ha2, c4⟩ hA hAz

end Orb

end CFSG.ClassicalInvolution.Asc77.T3CII
