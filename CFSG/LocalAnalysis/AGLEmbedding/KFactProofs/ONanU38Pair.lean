module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Arr

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open scoped Matrix

abbrev Pr3 : Type := Array GF64 × ℕ

@[expose] def sigPow : ℕ → Array GF64 → Array GF64
  | 0, A => A
  | n + 1, A => sigArr (sigPow n A)

@[expose] def mulP3 (p q : Pr3) : Pr3 := (mulArr3 p.1 (sigPow p.2 q.1), (p.2 + q.2) % 3)

@[expose] def oneP3 : Pr3 := (oneArr3, 0)

@[expose] def powP3 (p : Pr3) : ℕ → Pr3
  | 0 => oneP3
  | n + 1 => mulP3 p (powP3 p n)

@[expose] def invP3 (p : Pr3) : Pr3 :=
  (sigPow ((3 - p.2) % 3) (conjTrArr3 p.1), (3 - p.2) % 3)

@[expose] def eqMod (sc : List GF64) (p q : Pr3) : Bool :=
  p.2 == q.2 && sc.any fun s => p.1 == smulArr3 s q.1

@[expose] def monoP3 (e : Array Pr3) (v : Array ℕ) : Pr3 :=
  mulP3 (mulP3 (powP3 (e.getD 0 oneP3) (v.getD 0 0)) (powP3 (e.getD 1 oneP3) (v.getD 1 0)))
    (powP3 (e.getD 2 oneP3) (v.getD 2 0))

theorem size_sigPow (n : ℕ) (A : Array GF64) : (sigPow n A).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sigPow, size_sigArr, ih]

theorem toMat3_sigPow (n : ℕ) (A : Array GF64) :
    toMat3 (sigPow n A) =
      ((fun M : Matrix (Fin 3) (Fin 3) GF64 => M.map sigma2)^[n]) (toMat3 A) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sigPow, toMat3_sigArr, ih, Function.iterate_succ_apply']

end CFSG.AGLEmbedding.ChevOuter.U38
