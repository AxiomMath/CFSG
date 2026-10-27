module

public import Certificates.Data.FzFusK3

public section

namespace CFSG.KC.FzFus

open Certificates.FzJ36 Certificates.FzFus

theorem classCheck_of (h : ClassFact) : classCheck () = true := by
  unfold classCheck
  refine List.all_eq_true.mpr fun m _ => ?_
  cases hm : isInvB m
  · rfl
  obtain ⟨g, hg⟩ := h m (isInvB_iff.mp hm)
  simp only [Bool.not_true, Bool.false_or]
  exact List.any_eq_true.mpr ⟨g, allM_mem g, kb_iff.mpr hg⟩

theorem rowsCheck_of (h : RowsFact) : rowsCheck () = true := by
  unfold rowsCheck
  refine List.all_eq_true.mpr fun r hr => ?_
  obtain ⟨w, hw⟩ := h r hr
  exact List.any_eq_true.mpr ⟨w, allM_mem w, rowOKb_iff.mpr hw⟩

theorem subsCheck_of (h : SubsFact) : subsCheck () = true := by
  unfold subsCheck
  refine List.all_eq_true.mpr fun s hs => List.all_eq_true.mpr fun m _ => ?_
  cases hm : isInvB m
  · rfl
  by_cases hp : phi s.1 s.2.1 m = 1
  · simp [h s hs m (isInvB_iff.mp hm) hp]
  · simp [hp]

theorem pair7Check_of (h : Pair7Fact) : pair7Check () = true := by
  unfold pair7Check
  refine List.all_eq_true.mpr fun a _ => List.all_eq_true.mpr fun b _ => ?_
  cases hd : d5b z3M a b
  · rfl
  · exact absurd (d5b_iff.mp hd) (h a b)

theorem fusCheck_of (hC : ClassFact) (hR : RowsFact) (hS : SubsFact) (hN : Pair7Fact) :
    fusCheck () = true := by
  simp only [fusCheck, classCheck_of hC, rowsCheck_of hR, subsCheck_of hS, pair7Check_of hN,
    Bool.and_self]

end CFSG.KC.FzFus
