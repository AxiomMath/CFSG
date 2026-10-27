module

public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.KS.PW

open CFSG.ONSchreier.Native

@[expose] def cgen (n : Nat) (g : Array (Array Nat)) (sp : Nat × Nat × Nat) : Array Nat :=
  let ga := g[sp.1 - 1]!
  let gb := g[sp.2.1 - 1]!
  let x := pcomp n gb (pcomp n ga (pcomp n (pinvCand n gb) (pinvCand n ga)))
  if sp.2.2 == 0 then x else pcomp n g[sp.2.2 - 1]! (pcomp n x (pinvCand n g[sp.2.2 - 1]!))

theorem commGens_eq (n : Nat) (g : Array (Array Nat)) (specs : Array (Nat × Nat × Nat)) :
    commGens n g specs = specs.map (cgen n g) := by
  unfold commGens cgen
  simp

theorem conjAll_eq (n : Nat) (c ci : Array Nat) (g : Array (Array Nat)) :
    conjAll n c ci g = g.map fun x => pcomp n c (pcomp n x ci) := by
  unfold conjAll
  simp

theorem map_get {f : Array Nat → Array Nat} {g : Array (Array Nat)} {j : Nat} (hj : j < g.size) :
    (g.map f)[j]! = f g[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos g j hj]

theorem map_get' {α : Type} [Inhabited α] {f : α → Array Nat} {g : Array α} {j : Nat}
    (hj : j < g.size) : (g.map f)[j]! = f g[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos g j hj]

end CFSG.KS.PW

end
