module

public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8

open CFSG.Sporadic.Schreier CFSG.Certificates

variable {n : ℕ}

@[expose] def fixNum (g : Equiv.Perm (Fin n)) : ℕ :=
  (List.finRange n).countP fun i => decide (g i = i)

@[expose] def maskProd : List (Equiv.Perm (Fin n)) → ℕ → Equiv.Perm (Fin n)
  | [], _ => 1
  | g :: gs, m => (if m % 2 = 1 then g else 1) * maskProd gs (m / 2)

@[expose] def badState (zs : List (Equiv.Perm (Fin n))) (forbid : List ℕ)
    (cur : List (Equiv.Perm (Fin n))) : Bool :=
  cur.any (fun g => !schreierPermEq (g * g) 1) ||
    cur.any (fun g => cur.any fun h => !schreierPermEq (g * h) (h * g)) ||
    (List.range (2 ^ cur.length)).any fun m =>
      let p := tab (maskProd cur m)
      !schreierPermEq p 1 && (zs.any (schreierPermEq p) || forbid.contains (fixNum p))

@[expose] def derivCheck (al : List (Equiv.Perm (Fin n))) (okW : List ℤ → Bool)
    (zs : List (Equiv.Perm (Fin n))) (forbid : List ℕ) :
    List (Equiv.Perm (Fin n)) → List (ℕ × List ℤ × ℕ) → Bool
  | cur, [] => badState zs forbid cur
  | cur, (m, w, i) :: rest =>
    badState zs forbid cur ||
      (let p := tab (maskProd cur m)
       let c := tab (evalCodes al w)
       !schreierPermEq p 1 && okW w && schreierPermEq (c * p) (p * c) && decide (i < cur.length) &&
         derivCheck al okW zs forbid (cur ++ [tab (c * cur.getD i 1 * c⁻¹)]) rest)

@[expose] def parseStep (s : String) : ℕ × List ℤ × ℕ :=
  match s.splitOn ":" with
  | [m, w, i] => ((m.toNat?).getD 0, (w.splitOn ",").filterMap String.toInt?, (i.toNat?).getD 0)
  | _ => (0, [], 0)

@[expose] def parseDeriv (s : String) : List (ℕ × List ℤ × ℕ) :=
  if s.isEmpty then [] else (s.splitOn ";").map parseStep

@[expose] def parseDerivs (s : String) : List (List (ℕ × List ℤ × ℕ)) :=
  (s.splitOn "|").map parseDeriv

end CFSG.ComponentClassification.RankTwoClassical.ExcO8
