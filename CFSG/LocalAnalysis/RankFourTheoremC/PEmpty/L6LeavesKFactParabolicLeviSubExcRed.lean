module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOPMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOMMain

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

structure LeviSubExcInputs : Prop where
  g2 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .G2 2 f → LeviSubAt S
  f4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .F4 2 f → LeviSubAt S
  e6 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E6 2 f → LeviSubAt S
  e7 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E7 2 f → LeviSubAt S
  e8 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .E8 2 f → LeviSubAt S
  twistedE6 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .twistedE6 2 f → LeviSubAt S
  trialityD4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ChevalleyExceptionalModel S .trialityD4 2 f → LeviSubAt S
  twistedF4 : ∀ {S : Type} [Group S] [Finite S] {f : ℕ},
    ReeTitsModel S .twistedF4 2 f → LeviSubAt S

theorem leviSubInputs_of_exc (h : LeviSubExcInputs) : LeviSubInputs where
  psu := fun h4 hm => leviSubAt_of_psuFour h4 hm
  pomegaPlus := fun hm => leviSubAt_of_pomegaPlus hm
  pomegaMinus := fun hm => leviSubAt_of_pomegaMinus hm
  g2 := h.g2
  f4 := h.f4
  e6 := h.e6
  e7 := h.e7
  e8 := h.e8
  twistedE6 := h.twistedE6
  trialityD4 := h.trialityD4
  twistedF4 := h.twistedF4

theorem kFactParabolicLeviSub_of_exc
    (h : LeviSubExcInputs) : KFactParabolicLeviSub :=
  kFactParabolicLeviSub_of_inputs (leviSubInputs_of_exc h)

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
