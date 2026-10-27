module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Data
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem mem_centTabs_of_commute {ER : Array Tab} {t : Tab} {a : Equiv.Perm (Fin 42)}
    (ht : t ∈ ER) (hta : TabRep t a) (hc : a * r₃ = r₃ * a) : t ∈ centTabs 42 ER r₃T := by
  unfold centTabs
  rw [Array.mem_filter]
  exact ⟨ht, (hta.comp tabRep_r₃).beq_iff (tabRep_r₃.comp hta) |>.2 hc⟩

theorem hl34Check_spec
    (h : hl34Check enumR.tabs (orbitR r₂T).tabs (orbitR r₄T).tabs = true)
    {x w : R} (hxr : x * r₃R = r₃R * x) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx3 : x ≠ r₃R)
    (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1) (hwr : w * r₃R = r₃R * w) (hwx : w * x = x * w) :
    (IsConj x r₂R ∧ IsConj (r₃R * x) r₄R) ∨ (IsConj x r₄R ∧ IsConj (r₃R * x) r₂R) := by
  have hxr' : (x : Equiv.Perm (Fin 42)) * r₃ = r₃ * x := congrArg Subtype.val hxr
  have hwr' : (w : Equiv.Perm (Fin 42)) * r₃ = r₃ * w := congrArg Subtype.val hwr
  have hwx' : (w : Equiv.Perm (Fin 42)) * x = x * w := congrArg Subtype.val hwx
  have hx2' : (x : Equiv.Perm (Fin 42)) * x = 1 := congrArg Subtype.val hx2
  have hw3' : (w : Equiv.Perm (Fin 42)) ^ 3 = 1 := congrArg Subtype.val hw3
  obtain ⟨kx, hkx, hxrep⟩ := enumerates_R.exists_pos x.2
  obtain ⟨kw, hkw, hwrep⟩ := enumerates_R.exists_pos w.2
  have hxE : enumR.tabs[kx]! ∈ enumR.tabs := Array.mem_def.2 (getElem!_mem hkx)
  have hwE : enumR.tabs[kw]! ∈ enumR.tabs := Array.mem_def.2 (getElem!_mem hkw)
  have hxC := mem_centTabs_of_commute hxE hxrep hxr'
  have hwC := mem_centTabs_of_commute hwE hwrep hwr'
  obtain ⟨k, hk, hkx'⟩ := exists_getElem!_of_mem (Array.mem_def.1 hxC)
  have hw1' : (enumR.tabs[kw]! == idTab 42) = false := by
    rw [← Bool.not_eq_true]
    intro hc
    exact hw1 (Subtype.ext ((hwrep.beq_iff TabRep.idTab).1 hc))
  have hwW : enumR.tabs[kw]! ∈ (centTabs 42 enumR.tabs r₃T).filter
      fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42 := by
    rw [Array.mem_filter]
    refine ⟨hwC, ?_⟩
    rw [hw1', Bool.not_false, Bool.true_and]
    exact ((hwrep.pow 3).beq_iff TabRep.idTab).2 hw3'
  obtain ⟨j, hj, hjw⟩ := exists_getElem!_of_mem (Array.mem_def.1 hwW)
  simp only [hl34Check, allBelow_eq_true] at h
  have hk' := h k hk
  rw [hkx'] at hk'
  have e1 : (comp 42 enumR.tabs[kx]! enumR.tabs[kx]! == idTab 42) = true :=
    ((hxrep.comp hxrep).beq_iff TabRep.idTab).2 hx2'
  have e2 : (enumR.tabs[kx]! == idTab 42) = false := by
    rw [← Bool.not_eq_true]
    intro hc
    exact hx1 (Subtype.ext ((hxrep.beq_iff TabRep.idTab).1 hc))
  have e3 : (enumR.tabs[kx]! == r₃T) = false := by
    rw [← Bool.not_eq_true]
    intro hc
    exact hx3 (Subtype.ext ((hxrep.beq_iff tabRep_r₃).1 hc))
  have e4 : (anyBelow ((centTabs 42 enumR.tabs r₃T).filter
      fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42).size fun j =>
        comp 42 ((centTabs 42 enumR.tabs r₃T).filter
          fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42)[j]! enumR.tabs[kx]! ==
        comp 42 enumR.tabs[kx]! ((centTabs 42 enumR.tabs r₃T).filter
          fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42)[j]!) = true := by
    rw [anyBelow_eq_true]
    refine ⟨j, hj, ?_⟩
    rw [hjw]
    exact ((hwrep.comp hxrep).beq_iff (hxrep.comp hwrep)).2 hwx'
  simp only [e1, e2, e3, e4, Bool.not_false, Bool.and_self, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, Bool.and_eq_true] at hk'
  have hr₃x : TabRep (comp 42 r₃T enumR.tabs[kx]!) (((r₃R * x : R)) : Equiv.Perm (Fin 42)) :=
    tabRep_r₃.comp hxrep
  rcases hk' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    refine ⟨(conjClass₂.1 x).2 ?_, (conjClass₄.1 (r₃R * x)).2 ?_⟩
    · obtain ⟨i, hi, hie⟩ := memTab_iff.1 ha
      exact ⟨_, getElem!_mem hi, by rw [hie]; exact hxrep⟩
    · obtain ⟨i, hi, hie⟩ := memTab_iff.1 hb
      exact ⟨_, getElem!_mem hi, by rw [hie]; exact hr₃x⟩
  · right
    refine ⟨(conjClass₄.1 x).2 ?_, (conjClass₂.1 (r₃R * x)).2 ?_⟩
    · obtain ⟨i, hi, hie⟩ := memTab_iff.1 ha
      exact ⟨_, getElem!_mem hi, by rw [hie]; exact hxrep⟩
    · obtain ⟨i, hi, hie⟩ := memTab_iff.1 hb
      exact ⟨_, getElem!_mem hi, by rw [hie]; exact hr₃x⟩

end CFSG.EvenSporadicStandard.HSStd.HL34
