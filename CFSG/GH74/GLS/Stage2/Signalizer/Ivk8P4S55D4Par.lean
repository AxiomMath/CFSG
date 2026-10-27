module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55G2Even
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4SParity
public import CFSG.LieType.BorelTits.AllModels

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (td4_parity)


theorem borelTitsConcl_d4 {Y : Type} [Group Y] {p f : ℕ} (hm : LieModel Y .trialityD4 0 p f) :
    BorelTitsConcl p Y := by
  intro U hU hUp
  obtain ⟨S, P, hP, hN, -, -, hNS, -⟩ :=
    CFSG.LieType.BorelTits.lieModel_conclusion Y .trialityD4 0 p f hm U hU hUp
  exact ⟨S, P, hP, hN, hNS (by decide)⟩


theorem evenParabolics_d4 {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hm : LieModel Y .trialityD4 0 p f) : EvenParabolics p Y :=
  evenParabolics_of_parity fun S M hM hSM => td4_parity hp hp2 hf hm S M hM hSM

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
