module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Sym6Check

public section

namespace CFSG.EvenSporadicStandard.M24Std.Sym6

open CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint

@[expose] def symGens : List (S24 × Equiv.Perm (Fin 6)) :=
  [(sxS, Equiv.swap 0 1), (sxT, finRotate 6)]

@[expose] def addNew (acc : List (S24 × Equiv.Perm (Fin 6))) (c : S24 × Equiv.Perm (Fin 6)) :
    List (S24 × Equiv.Perm (Fin 6)) :=
  if acc.any fun q => decide (q.2 = c.2) then acc else acc ++ [c]

@[expose] def symStep (st : List (S24 × Equiv.Perm (Fin 6)) × List (S24 × Equiv.Perm (Fin 6))) :
    List (S24 × Equiv.Perm (Fin 6)) × List (S24 × Equiv.Perm (Fin 6)) :=
  let acc := (st.2.flatMap fun p => symGens.map fun g =>
    (normH NativeSporadic.M24 (g.1 * p.1), tab (g.2 * p.2))).foldl addNew st.1
  (acc, acc.drop st.1.length)

@[expose] def sym6T : List (S24 × Equiv.Perm (Fin 6)) := (symStep^[20] ([(1, 1)], [(1, 1)])).1

@[expose] def Sym6InvData : Prop :=
  (∀ σ : Equiv.Perm (Fin 6), ∃ p ∈ sym6T, p.2 = σ) ∧
    (∀ p ∈ sym6T, p.2 * p.2 = 1 → ∀ k ∈ sxK0, k * p.1 * (k * p.1) = 1 → k * p.1 ∉ m24E1l →
      (m24E1l.filter fun x => decide (k * p.1 * x * (k * p.1)⁻¹ = x)).length =
        if Equiv.Perm.sign p.2 = 1 then 16 else 8) ∧
    ∃ k ∈ sxK0, k * sxS * (k * sxS) = 1

instance : Decidable Sym6InvData := by
  unfold Sym6InvData
  infer_instance

@[expose] def wordSxC1 : List ℤ :=
  [2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 1, -2, 1,
    -2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2,
    -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1,
    -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, 2, 1, 2, 2, -1, 2, -1, -2, -1, 2,
    -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, -2,
    1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, -1]

@[expose] def wordSxC2 : List ℤ :=
  [1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, 2, -1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1,
    -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
    1, 2, 1, -2, -2, -1, -2, -1, 2, -1, -2, -2, 1, 2, 1, 2, 1, -2, 1, -2, -2, -1, -2, -1, -2, -1,
    2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -1, -2, -1,
    2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -1, -2, -1, 2,
    -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, -2,
    -1, 2, 1, 2]

@[expose] def Sym6ConjData : Prop :=
  (∃ x ∈ m24E1l, (m24Cj wordSxC1 : Equiv.Perm (Fin 24)) * m24InvReps.getD 0 1 *
      (m24Cj wordSxC1 : Equiv.Perm (Fin 24))⁻¹ = (x : Equiv.Perm (Fin 24))) ∧
    ∃ x ∈ m24E1l, (m24Cj wordSxC2 : Equiv.Perm (Fin 24)) * m24InvReps.getD 1 1 *
      (m24Cj wordSxC2 : Equiv.Perm (Fin 24))⁻¹ = (x : Equiv.Perm (Fin 24))

instance : Decidable Sym6ConjData := by
  unfold Sym6ConjData
  infer_instance

end CFSG.EvenSporadicStandard.M24Std.Sym6
