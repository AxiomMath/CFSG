module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UOut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UPar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenBT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial

theorem defData_u3 {p : ℕ} {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) (hp2 : p ≠ 2)
    (h : FU3d p Y) : DefData p Y := by
  obtain ⟨f, hf, hlie⟩ := h
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := lieModel_psu3_unpack hlie
  have hU : UnitaryFieldData p f F := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨borelTitsConcl_of_lieModel hlie (by decide), EvenParabolics.of_mulEquiv e
    (evenParabolics_u3 hU hp2), OuterFalse.of_mulEquiv e
    (outerFalse_unitary hU hp2 (by norm_num : 3 ≤ 3) (i₀ := 0) (i₁ := 1) (i₂ := 2)
      (by decide) (by decide) (by decide))⟩

theorem def55_u3 : Def55 FU3d :=
  def55_of_defData fun _ _ _ _ hp hp2 _ h => defData_u3 hp hp2 h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
