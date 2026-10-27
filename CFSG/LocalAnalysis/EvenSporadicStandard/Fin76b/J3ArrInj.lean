module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.J3Check

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J3

theorem arr_getElem!_inj {α β : Type*} [Inhabited α] (A : Array α) (f : α → β)
    (hnd : (A.toList.map f).Nodup) {a b : ℕ} (ha : a < A.size) (hb : b < A.size)
    (h : f A[a]! = f A[b]!) : a = b := by
  have ha' : a < (A.toList.map f).length := by simpa using ha
  have hb' : b < (A.toList.map f).length := by simpa using hb
  have h1 : (A.toList.map f)[a] = (A.toList.map f)[b] := by
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos A a ha, ← getElem!_pos A b hb]
    exact h
  exact hnd.getElem_inj_iff.1 h1

end CFSG.EvenSporadicStandard.Fin76b.J3
