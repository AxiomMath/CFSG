module

public import Certificates.Certificate15101
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuSimCode

public section

namespace CFSG.ComponentClassification.GMS78

open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

theorem ruQ0_check : q0Check = true :=
  Certificates.certificate15101

namespace RuQCode

@[expose] def allPlanes : List (List Nat) := pointPlanes ++ linePlanes ++ singerPlanes

theorem sqN_xiApply {d : RuSimCode.SData} (hd : d ∈ steinData)
    {m : Nat} (hm : m < 256) : sqN d.1.1 d.1.2.1 (xiApply d.2.2 m) = qC m := by
  have h := ruQ0_check
  simp only [q0Check, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h d hd m hm

theorem singMasks_eq : ((List.range 256).filter fun m => m != 0 && qC m == 0) = singMasks := by
  decide +kernel

theorem mem_singMasks_iff {m : Nat} (hm : m < 256) : m ∈ singMasks ↔ m ≠ 0 ∧ qC m = 0 := by
  rw [← singMasks_eq]
  simp [hm]

theorem exists_plane_check : (singMasks.all fun a => singMasks.all fun b =>
    a == b || bC a b != 0 || allPlanes.any fun P => P.contains a && P.contains b) = true := by
  decide +kernel

theorem exists_plane {a b : Nat} (ha : a ∈ singMasks) (hb : b ∈ singMasks) (hab : a ≠ b)
    (h0 : bC a b = 0) : ∃ P ∈ allPlanes, a ∈ P ∧ b ∈ P := by
  have h := exists_plane_check
  simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.any_eq_true,
    Bool.and_eq_true, List.contains_iff_mem] at h
  rcases h a ha b hb with (h | h) | h
  · exact absurd h hab
  · exact absurd h0 h
  · exact h

theorem mem_of_perp_check : (allPlanes.all fun P => singMasks.all fun c =>
    P.contains c || P.any fun t => bC t c != 0) = true := by
  decide +kernel

theorem mem_of_forall_bC_eq_zero {P : List Nat} (hP : P ∈ allPlanes) {c : Nat}
    (hc : c ∈ singMasks) (h0 : ∀ t ∈ P, bC t c = 0) : c ∈ P := by
  have h := mem_of_perp_check
  simp only [List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    bne_iff_ne, ne_eq] at h
  rcases h P hP c hc with h | ⟨t, ht, h⟩
  · exact h
  · exact absurd (h0 t ht) h

theorem length_eq_of_mem_allPlanes : ∀ P ∈ allPlanes, P.length = 3 := by
  decide +kernel

end RuQCode

end CFSG.ComponentClassification.GMS78
