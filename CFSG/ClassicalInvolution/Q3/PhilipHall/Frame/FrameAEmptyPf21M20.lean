module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

section Vocab

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def frameKa (K : Subgroup G) (a : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (tightCore (K ⊓ Subgroup.centralizer ({a} : Set G))).subgroupOf
    (Subgroup.centralizer ({a} : Set G))

end Vocab

section Rows

variable {G : Type} [Group G] [Finite G] [FrameCore G] {K K' J : Subgroup G} {S : Sylow 2 G}
  {R R' W V : Subgroup G} {z t : G}

theorem card_centralizer_lt (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hd : Frame205Data d a) : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G := by
  have hCtop : Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
    intro htop
    have hac : a ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    rw [FrameCore.center d.nonabelian, Subgroup.mem_bot] at hac
    exact hd.conf.ha1 hac
  exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
    (fun h => hCtop ((Subgroup.card_eq_iff_eq_top _).mp h))

end Rows

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
