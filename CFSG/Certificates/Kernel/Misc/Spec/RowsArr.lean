module

public import CFSG.Certificates.Kernel.Misc.Spec.ArrMat

public section

namespace CFSG.KC.Misc.Spec

open CFSG.LieType.Multipliers.G24

@[expose] def rowsArr {R : Type*} (f : Char → R) (rows : List (List ℕ)) : Array (Array R) :=
  ((rows.map fun r => String.ofList (r.map Char.ofNat)).map
    fun s => (s.toList.map f).toArray).toArray

theorem rowsArr_size {R : Type*} (f : Char → R) (rows : List (List ℕ)) :
    (rowsArr f rows).size = rows.length := by
  simp [rowsArr]

theorem rowsArr_getD {R : Type*} (f : Char → R) (rows : List (List ℕ)) (i : ℕ) :
    (rowsArr f rows).getD i #[] = (((rows.getD i []).map Char.ofNat).map f).toArray := by
  unfold rowsArr
  simp only [Array.getD, List.size_toArray, List.length_map]
  by_cases hi : i < rows.length
  · simp [hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · simp [hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : rows.length ≤ i)]

theorem rowsArr_row_size {R : Type*} (f : Char → R) (rows : List (List ℕ)) {r : Array R}
    (hr : r ∈ (rowsArr f rows).toList) : ∃ c ∈ rows, r.size = c.length := by
  unfold rowsArr at hr
  simp only [List.toList_toArray, List.mem_map] at hr
  obtain ⟨s, ⟨c, hc, rfl⟩, rfl⟩ := hr
  exact ⟨c, hc, by simp⟩

theorem getD_rowsArr {R : Type*} [Zero R] (f : Char → R) (rows : List (List ℕ)) {i j : ℕ}
    (hj : j < (rows.getD i []).length) :
    ((rowsArr f rows).getD i #[]).getD j 0 = f (Char.ofNat ((rows.getD i []).getD j 0)) := by
  rw [rowsArr_getD]
  generalize rows.getD i [] = r at hj ⊢
  simp [Array.getD, hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

end CFSG.KC.Misc.Spec

end
