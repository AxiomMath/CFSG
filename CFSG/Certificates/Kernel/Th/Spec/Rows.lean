
module

public import CFSG.Certificates.Kernel.Th.Spec.RowsBase

public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.KC.Th.Spec

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.ThSchreier

theorem rowsMatrix_prodRows (l : List (Array V4)) :
    rowsMatrix (prodRows l) = (l.map rowsMatrix).prod := by
  induction l with
  | nil => rw [prodRows_nil, List.map_nil, List.prod_nil]; exact rowsMatrix_idRows
  | cons X l ih => rw [prodRows_cons, rowsMatrix_mulRows, ih, List.map_cons, List.prod_cons]

theorem wfRows_prodRows {l : List (Array V4)} (h : ∀ X ∈ l, WfRows X) : WfRows (prodRows l) := by
  induction l with
  | nil => rw [prodRows_nil]; exact wfRows_idRows
  | cons X l ih =>
    rw [prodRows_cons]
    exact (h X List.mem_cons_self).mulRows (ih fun Y hY => h Y (List.mem_cons_of_mem _ hY))

theorem rowsMatrix_signedRows (letter : ℤ → Array V4) (w : List ℤ) :
    rowsMatrix (signedRows letter w) = (w.map fun l => rowsMatrix (letter l)).prod := by
  rw [signedRows, rowsMatrix_prodRows, List.map_map]
  rfl

theorem wfRows_signedRows {letter : ℤ → Array V4} {w : List ℤ}
    (h : ∀ l ∈ w, WfRows (letter l)) : WfRows (signedRows letter w) :=
  wfRows_prodRows fun X hX => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hX
    exact h l hl

theorem rowsMatrix_wordRows (rx ry : Array V4) (w : List Gen) :
    rowsMatrix (wordRows rx ry w) =
      (w.map fun g => Gen.eval (rowsMatrix rx) (rowsMatrix ry) g).prod := by
  rw [wordRows, rowsMatrix_prodRows, List.map_map]
  congr 1
  refine List.map_congr_left fun g _ => ?_
  cases g <;> rfl

theorem wfRows_wordRows {rx ry : Array V4} (hx : WfRows rx) (hy : WfRows ry) (w : List Gen) :
    WfRows (wordRows rx ry w) :=
  wfRows_prodRows fun X hX => by
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hX
    cases g
    · exact hx
    · exact hy

end CFSG.KC.Th.Spec

end
