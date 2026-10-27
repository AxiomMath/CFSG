module

public import Certificates.Data.GH74EvSporCheck

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

@[expose] def j2Row0 : ClassRow := j2Rows[0]'(by decide)

theorem j2Row0_mem : j2Row0 ∈ j2Rows := List.getElem_mem _
theorem j2Row0_outer : j2Row0.outer = true := rfl
theorem j2Row0_centOrder : j2Row0.centOrder = 336 := rfl

theorem j2Rows_cases' (r : ClassRow) (hr : r ∈ j2Rows) :
    r = j2Row0 ∨ r = j2Row2B ∨ r = j2Row2A := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hlen : j2Rows.length = 3 := rfl
  rw [hlen] at hi
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end CFSG.GH74.Generic.S45.EvSpor
