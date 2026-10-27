module

import all CFSG.Fischer.F4
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckA2

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix CFSG.ClassicalGroups.UnitaryFlag Certificates.U52Yamada
open scoped commutatorElement

theorem normalizer_A₂sub_conj_mem_Fsub {n f : SU52} (hn : n ∈ normalizer (A₂sub : Set SU52))
    (hf : f ∈ Fsub) : n * f * n⁻¹ ∈ Fsub := by
  refine mem_Fsub_of_central ((mem_normalizer_iff.1 hn f).1 (Fsub_le_A₂sub hf)) fun a ha => ?_
  have ha' : n⁻¹ * a * n ∈ A₂sub := by
    have := (mem_normalizer_iff.1 (inv_mem hn) a).1 ha
    rwa [inv_inv] at this
  have hc := Fsub_comm_A₂ ha' hf
  calc a * (n * f * n⁻¹) = n * (n⁻¹ * a * n * f) * n⁻¹ := by group
    _ = n * (f * (n⁻¹ * a * n)) * n⁻¹ := by rw [hc]
    _ = n * f * n⁻¹ * a := by group

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
