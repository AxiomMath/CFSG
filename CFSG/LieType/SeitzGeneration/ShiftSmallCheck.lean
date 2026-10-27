module

public import CFSG.LieType.SeitzGeneration.OuterSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

variable {L : Type} [Field L]

@[expose] def GenExactL (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Prop :=
  G.det = 1 ∧ (G.map (· ^ q)).transpose * G = 1 ∧ ∃ M ∈ lines, G * M = M * G

variable [DecidableEq L] [Fintype L]

instance (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Decidable (GenExactL q lines G) := by
  unfold GenExactL
  infer_instance

@[expose] def shiftEntryOk (q : ℕ) (ω : L) (e : OuterEntry L) : Bool :=
  e.gens.all (fun G => decide (GenExactL q [cM3 e.alpha, dM3 ω] G)) &&
    decide (e.words.map (evalW e.gens) = [sM3])

@[expose] def shiftCheck (q : ℕ) (ω : L) (table : List (OuterEntry L)) : Bool :=
  table.all (shiftEntryOk q ω) && decide (AlphaCovered q table)

end CFSG.LieType.SeitzGeneration.HeisSmall
