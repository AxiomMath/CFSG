module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Spec

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
  CFSG.EvenSporadicStandard.HSStd.HL34

theorem hfi34Check_spec
    (h : hfi34Check enumR.tabs (orbitR r₃T).tabs = true)
    {x : R} (hxr : x * r₃R = r₃R * x) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx3 : x ≠ r₃R) :
    ¬ (IsConj x r₃R ∧ IsConj (r₃R * x) r₃R) := by
  rintro ⟨hc1, hc2⟩
  have hxr' : (x : Equiv.Perm (Fin 42)) * r₃ = r₃ * x := congrArg Subtype.val hxr
  have hx2' : (x : Equiv.Perm (Fin 42)) * x = 1 := congrArg Subtype.val hx2
  obtain ⟨kx, hkx, hxrep⟩ := enumerates_R.exists_pos x.2
  have hxE : enumR.tabs[kx]! ∈ enumR.tabs := Array.mem_def.2 (getElem!_mem hkx)
  have hxC := mem_centTabs_of_commute hxE hxrep hxr'
  obtain ⟨k, hk, hkx'⟩ := exists_getElem!_of_mem (Array.mem_def.1 hxC)
  simp only [hfi34Check, allBelow_eq_true] at h
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
  have hr₃x : TabRep (comp 42 r₃T enumR.tabs[kx]!) (((r₃R * x : R)) : Equiv.Perm (Fin 42)) :=
    tabRep_r₃.comp hxrep
  have m1 : memTab (orbitR r₃T).tabs enumR.tabs[kx]! = true := by
    obtain ⟨t, ht, hr⟩ := (conjClass₃.1 x).1 hc1
    rw [memTab_iff]
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    exact ⟨i, hi, hr.tab_eq hxrep⟩
  have m2 : memTab (orbitR r₃T).tabs (comp 42 r₃T enumR.tabs[kx]!) = true := by
    obtain ⟨t, ht, hr⟩ := (conjClass₃.1 (r₃R * x)).1 hc2
    rw [memTab_iff]
    obtain ⟨i, hi, rfl⟩ := exists_getElem!_of_mem ht
    exact ⟨i, hi, hr.tab_eq hr₃x⟩
  simp only [e1, e2, e3, m1, m2, Bool.not_false, Bool.and_self, Bool.not_true,
    Bool.or_false] at hk'
  exact Bool.noConfusion hk'

end CFSG.EvenSporadicStandard.HSStd.HFI
