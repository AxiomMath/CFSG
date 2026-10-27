module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC4
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC5Eng

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Data

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K K' J : Subgroup G}
  {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20

variable (d : Std20 p f K K' J S R R' W V z t)
include d

theorem concl20_5_of_7 (c7 : Concl20_7 S K K' z) : Concl20_5 S K K' z := by
  exact CFSG.ClassicalInvolution.Asc77.T3CII.concl20_5_of_7_of d.sup_le_centralizer_z
    ((d.hSz).trans (le_normalizer_sup_pair d.hyp.conjInvariant d.viol.hzK d.twins d.ne))
    d.viol.hzK d.z_mem_S c7

end Std20

end Data

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Res20_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K K' J : Subgroup G) (S : Sylow 2 G)
    (R R' W V : Subgroup G) (z t : G), Std20 p f K K' J S R R' W V z t →
      Concl20_3 K K' V z → Concl20_4 S K K' J z → Concl20_7 S K K' z

variable {p f}

theorem c20_5_of_res20_7 (h : Res20_7 p f) : C20_5 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4
  exact d.concl20_5_of_7 (h G K K' J S R R' W V z t d c3 c4)

theorem res20_7_of_c20_5 (h5 : C20_5 p f) : Res20_7 p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4
  exact c20_7 p f G K K' J S R R' W V z t d c3 c4 (h5 G K K' J S R R' W V z t d c3 c4)

end CFSG.ClassicalInvolution.Asc77.T3CII
