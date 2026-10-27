module

public import CFSG.Sporadic.SuzOddCore.InvPerms
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzN0Data

public noncomputable section

namespace CFSG.EvenSporadicStandard.SuzN0

open CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

@[expose] def xElt (j : ℕ) : Equiv.Perm (Fin 1782) :=
  ⁅invInnerGen 0 1, invInnerGen 0 (j + 2)⁆

@[expose] def letterElt (l : ℤ) : Equiv.Perm (Fin 1782) :=
  if 0 < l then xElt (l.toNat - 1) else (xElt ((-l).toNat - 1))⁻¹

@[expose] def wordElt (w : List ℤ) : Equiv.Perm (Fin 1782) := (w.map letterElt).prod

@[expose] def oddElt (k : ℕ) : Equiv.Perm (Fin 1782) := wordElt (oddWords.getD k ([], 1)).1

@[expose] def rElt (i : ℕ) : Equiv.Perm (Fin 1782) := oddElt (2 * i) * oddElt (2 * i + 1)

@[expose] def wElt : Equiv.Perm (Fin 1782) := oddElt 8

@[expose] def zElt : Equiv.Perm (Fin 1782) := wordElt zWord

@[expose] def RR : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (Set.range fun i : Fin 4 => rElt i)

@[expose] def gensElt (h : Equiv.Perm (Fin 1782)) (j : ℕ) : Equiv.Perm (Fin 1782) :=
  if j < 4 then h⁻¹ * rElt j * h else h⁻¹ * wElt * h

structure SurvFacts (S : Set (Equiv.Perm (Fin 1782))) : Prop where
  mem : ∀ s ∈ S, s ∈ suzM
  pow : ∀ s ∈ S, s * s = 1 ∨ s * s * s = 1
  comm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ * ⁅s, t⁆ = 1
  invol : ∀ s ∈ S, ∀ t ∈ S, s * s = 1 → t * t = 1 → s * t = t * s
  card : {s | s ∈ S ∧ s * s = 1}.ncard ≤ 4

@[expose] def SuzN0Facts : Prop :=
  (∀ k < 9, oddElt k ^ (oddWords.getD k ([], 1)).2 = 1) ∧ Nat.card RR = 64 ∧ zElt ∈ RR ∧
    (∀ i < 4, wElt * rElt i * wElt⁻¹ ∈ RR) ∧
    ∃ h ∈ suzM, h * suzInv 1 * h⁻¹ = zElt ∧ ∃ S : Set (Equiv.Perm (Fin 1782)), SurvFacts S ∧
      ∀ τ ∈ invD 1, (∀ j < 5, τ * gensElt h j = gensElt h j * τ) → τ ∈ S

end CFSG.EvenSporadicStandard.SuzN0

end
