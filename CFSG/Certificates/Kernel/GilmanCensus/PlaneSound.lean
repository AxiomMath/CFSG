module

public import Certificates.Data.Census

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def zAB (d : Nat) (x y : Array Nat) (a b : Nat) : Array Nat :=
  line3 (Array.ofFn (n := d) fun i => (a * x[i.val]! + b * y[i.val]!) % 3)

@[expose] def dlStep (d : Nat) (x y : Array Nat) (a : Nat) (dl : Array (Array Nat)) (b : Nat) :
    Array (Array Nat) :=
  if (a != 0 || b != 0) = true then
    if (!dl.contains (zAB d x y a b)) = true then dl.push (zAB d x y a b) else dl
  else dl

@[expose] def dlM (d : Nat) (x y : Array Nat) : Array (Array Nat) :=
  (List.range' 0 3).foldl (fun dl a => (List.range' 0 3).foldl (dlStep d x y a) dl) #[]

theorem arr_contains (dl : Array (Array Nat)) (z : Array Nat) :
    dl.contains z = (dl.toList.map Array.toList).contains z.toList := by
  rw [Bool.eq_iff_iff, Array.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  constructor
  · intro hz
    exact ⟨z, Array.mem_toList_iff.mpr hz, rfl⟩
  · rintro ⟨w, hw, he⟩
    rw [← Array.toList_inj.mp he]
    exact Array.mem_toList_iff.mp hw

@[expose] def dlF (d : Nat) (x y : Array Nat) (ps : List (Nat × Nat)) (dl : Array (Array Nat)) :
    Array (Array Nat) :=
  ps.foldl (fun dl ab => dlStep d x y ab.1 dl ab.2) dl

theorem dlM_eq (d : Nat) (x y : Array Nat) :
    dlM d x y = dlF d x y [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)] #[] := by
  have e : List.range' 0 3 = [0, 1, 2] := rfl
  unfold dlM dlF
  rw [e]
  simp only [List.foldl_cons, List.foldl_nil]

end Certificates.GilmanCensusK

end
