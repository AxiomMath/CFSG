module

public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts
public import CFSG.GH74.KGroups.Sz8Tables

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.Blueprint CFSG.OddStandard.ThmC.T

theorem false_of_lieModel_sz8
    {K : Type} [Group K] [Finite K] (h : LieModel K .twistedB2 0 2 3) (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) : False := by
  obtain ⟨hinv, -⟩ :=
    CFSG.GH74.KGroups.Sz8.bender h (T : Subgroup K) T.isPGroup' T.not_dvd_index
  obtain ⟨x, hx2, -, hxE⟩ := hT.exists_involution_not_mem (E := Subgroup.center ↥(T : Subgroup K))
    (fun z hz => hT.sq_eq_one_of_mem_center hz)
  apply hxE
  rw [Subgroup.mem_center_iff]
  intro y
  have hx2' : (x : K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val hx2
  exact Subtype.ext (hinv (x : K) x.2 hx2' (y : K) y.2)

end CFSG.OddStandard.ThmC.Sylow
