module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFFrontier

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator

@[expose] def GF2NoFFSporadicFor (n : TauCeti.SporadicName) : Prop :=
  NoFFModule (TauCeti.CFSGIndex.sporadic n).Group

theorem gf2NoFFSporadicFor_of_noIrrFFOffender {n : TauCeti.SporadicName}
    (h : NoIrrFFOffender (TauCeti.CFSGIndex.sporadic n).Group) : GF2NoFFSporadicFor n :=
  noFFModule_of_noIrrFFOffender h

theorem gf2NoFFSporadic_of_each (hJ3 : GF2NoFFSporadicFor .J3) (hCo1 : GF2NoFFSporadicFor .Co1)
    (hCo2 : GF2NoFFSporadicFor .Co2) (hCo3 : GF2NoFFSporadicFor .Co3)
    (hFi22 : GF2NoFFSporadicFor .Fi22) (hFi23 : GF2NoFFSporadicFor .Fi23)
    (hFi24 : GF2NoFFSporadicFor .Fi24Prime) (hMcL : GF2NoFFSporadicFor .McL)
    (hSuz : GF2NoFFSporadicFor .Suz) (hON : GF2NoFFSporadicFor .ONan)
    (hHN : GF2NoFFSporadicFor .HN) (hLy : GF2NoFFSporadicFor .Ly) (hTh : GF2NoFFSporadicFor .Th)
    (hB : GF2NoFFSporadicFor .B) (hM : GF2NoFFSporadicFor .M) : GF2NoFFSporadic := by
  intro n hn
  cases n
  case J3 => exact hJ3
  case Co1 => exact hCo1
  case Co2 => exact hCo2
  case Co3 => exact hCo3
  case Fi22 => exact hFi22
  case Fi23 => exact hFi23
  case Fi24Prime => exact hFi24
  case McL => exact hMcL
  case Suz => exact hSuz
  case ONan => exact hON
  case HN => exact hHN
  case Ly => exact hLy
  case Th => exact hTh
  case B => exact hB
  case M => exact hM
  all_goals exact absurd (by simp [IsSQTKSporadic]) hn

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
