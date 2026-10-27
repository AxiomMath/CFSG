module

public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.ClassicalInvolution.Asc77.AscC25W4
public import CFSG.ClassicalInvolution.Asc77.AscC25W9
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.ClassicalInvolution.Asc77.C25Y (GoodFusion)
open CFSG.ClassicalInvolution.Asc77.C25H (zpow_eq_one_or_self)
open CFSG.ClassicalInvolution.Asc77.C25W (InFour mem_zStarOf_centralizer_conj_iff good_of_mem_zpowers exists_sq_mem_mod exists_conj_ge_sylow)
open CFSG.ClassicalInvolution.Asc77.C25Y (mem_closure_pair)
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def P25_A4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → Nat.card ↥(cA S R R') ≤ 4

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S
