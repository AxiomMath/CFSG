
module

public import CFSG.Certificates.Kernel.Th.Max3S.DefsExtra
public import CFSG.Certificates.Kernel.Th.Max3S.Leaves
public import CFSG.Certificates.Kernel.Th.Spec.Big

@[expose] public section

namespace CFSG.KC.Th.Max3S

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.KC.Th.Spec
open CFSG.ComponentClassification.PresentationLocal (CarmichaelIndex)

section Wf

variable {A B : Array V4}

end Wf

variable {D : CFSG.KC.Th.Gen.Max3Data}

theorem segMid_length : (segMid D).length = 41 := rfl

theorem segEnd_length : (segEnd D).length = 38 := rfl

theorem mem_leaves_segMid {b : Bool} (hb : b ∈ segMid D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb))

theorem mem_leaves_segEnd {b : Bool} (hb : b ∈ segEnd D) : b ∈ leaves D := by
  rw [leaves]
  exact List.mem_append_right _ hb

theorem segMid_true (h : CFSG.KC.Th.Gen.max3Chk D = true) (i : ℕ) (hi : i < (segMid D).length) :
    (segMid D)[i] = true :=
  leaves_true D h _ (mem_leaves_segMid (List.getElem_mem hi))

theorem segEnd_true (h : CFSG.KC.Th.Gen.max3Chk D = true) (i : ℕ) (hi : i < (segEnd D).length) :
    (segEnd D)[i] = true :=
  leaves_true D h _ (mem_leaves_segEnd (List.getElem_mem hi))

private def abGen (i : ℕ) : Gen := if i = 1 then .x else .y

private theorem ab_eq_wordRows (A B : Array V4) (w : List ℕ) :
    ab A B w = wordRows A B (w.map abGen) := by
  unfold ab wordRows
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  unfold abLetter abGen
  by_cases h : i = 1 <;> simp [h, Gen.eval]

end CFSG.KC.Th.Max3S

end
