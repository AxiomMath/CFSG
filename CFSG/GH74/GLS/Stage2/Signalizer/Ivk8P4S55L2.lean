module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Par
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55L2Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem defData_l2 {Y : Type} [Group Y] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : FL2d p Y) :
    DefData p Y := by
  obtain ⟨_, _, h⟩ := h
  exact ⟨l2_borelTitsConcl hp h, l2_evenParabolics hp hp2 h, l2_outerFalse hp hp2 h⟩

theorem def55_l2 : Def55 FL2d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ h => defData_l2 hp hp2 h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
