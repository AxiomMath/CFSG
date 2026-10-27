
module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2b
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2c
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2d
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2e
public import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gInputs
public import CFSG.GH74.GLS.C3.Layer2.L5C2gListInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C2gListInputs
public import CFSG.GH74.GLS.C3.Layer2.L5Fin
public import CFSG.GH74.GLS.C3.Layer2.L5A1Inputs
public import CFSG.GH74.GLS.C3.Layer2.L5B2
public import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public import CFSG.GH74.GLS.C3.Layer2.L5C0Inputs

@[expose] public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

namespace Fus

theorem sh1M_codes :
    sh1M.map sh1Code = sh1WW.map fun pw => codeP16 pw.1 := by
  simp [sh1M, sh1Code, List.map_pmap, List.pmap_eq_map]

theorem sh1M_length :
    sh1M.length = 128 := by
  simp [sh1M, sh1WW_chk.2.1]

theorem sh1M_complete
    (m : ↥Sh1) : m ∈ sh1M := by
  classical
  have : Fintype ↥Sh1 := Fintype.ofFinite _
  have hnd : sh1M.Nodup := by
    apply List.Nodup.of_map sh1Code
    rw [sh1M_codes]
    exact sh1WW_chk.2.2
  have hcard : sh1M.length = Fintype.card ↥Sh1 := by
    rw [sh1M_length, ← Nat.card_eq_fintype_card, card_Sh1]
  have hu : sh1M.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, hcard])
  have hm : m ∈ sh1M.toFinset := by rw [hu]; exact Finset.mem_univ m
  exact List.mem_toFinset.1 hm

end Fus

end CFSG.GH74.GLS.C3.Layer2.L5
