module

public import Certificates.Data.RuF45Geom

public section

namespace CFSG.RuF45

open CFSG.Monster.B.Co2.Native

@[expose] def signedLetter (l : Nat × Bool) : Int :=
  if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

theorem evalArr_eq_wordA (n : Nat) (G Gi : Array (Array Nat)) (w : Word) :
    evalArr n G Gi w = wordA n G Gi (w.map signedLetter) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [evalArr, List.map_cons, wordA, ih]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [lettArr, letterA, signedLetter] <;> omega

end CFSG.RuF45
