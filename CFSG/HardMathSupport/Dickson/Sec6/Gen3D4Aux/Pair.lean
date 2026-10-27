module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Letters

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.AGLEmbedding.ChevOuter

abbrev Pr : Type := Array GF64 × ℕ

@[expose] def mulP (p q : Pr) : Pr := (mulArr p.1 (frobPow p.2 q.1), (p.2 + q.2) % 3)

@[expose] def oneP : Pr := (oneArr, 0)

@[expose] def powP (p : Pr) : ℕ → Pr
  | 0 => oneP
  | n + 1 => mulP p (powP p n)

@[expose] def symP (s : ℕ) : Pr := if s < 16 then (letterArr s, 0) else (oneArr, 1)

@[expose] def wordP (w : List ℕ) : Pr := w.foldr (fun s p => mulP (symP s) p) oneP

@[expose] def invWord (w : List ℕ) : List ℕ :=
  w.reverse.flatMap fun s => if s < 16 then [s] else [16, 16]

theorem size_mulP (p q : Pr) : (mulP p q).1.size = 64 := size_mulArr _ _

theorem size_oneP : oneP.1.size = 64 := size_oneArr

theorem size_powP (p : Pr) (n : ℕ) : (powP p n).1.size = 64 := by
  cases n with
  | zero => exact size_oneP
  | succ n => exact size_mulP _ _

theorem size_symP (s : ℕ) : (symP s).1.size = 64 := by
  unfold symP
  split_ifs
  · exact size_letterArr s
  · exact size_oneArr

theorem size_wordP (w : List ℕ) : (wordP w).1.size = 64 := by
  induction w with
  | nil => exact size_oneP
  | cons s w ih => exact size_mulP _ _

theorem snd_mulP_lt (p q : Pr) : (mulP p q).2 < 3 := Nat.mod_lt _ (by norm_num)

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
