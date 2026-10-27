module

public import CFSG.LieType.SeitzGeneration.HeisSmallCheck

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

variable {L : Type} [Field L]

@[expose] def cM3 (α : L) : M3 L := ⟨0, 0, α, 1, 0, 0, 0, 1, 0⟩

@[expose] def outerLineList (ω α : L) : List (M3 L) :=
  [cM3 α, dM3 ω, cM3 α * dM3 ω, cM3 α * (dM3 ω * dM3 ω)]

@[expose] def GenOkL (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Prop :=
  G.det = 1 ∧ (G.map (· ^ q)).transpose * G = 1 ∧
    ∃ M ∈ lines, ∃ c : L, G * M = M3.smul c (M * G)

structure OuterEntry (L : Type) where
  alpha : L
  gens : List (M3 L)
  words : List (List ℕ)

variable [DecidableEq L] [Fintype L]

instance (q : ℕ) (lines : List (M3 L)) (G : M3 L) : Decidable (GenOkL q lines G) := by
  unfold GenOkL
  infer_instance

@[expose] def entryOk (q : ℕ) (ω : L) (letters : List (M3 L)) (e : OuterEntry L) : Bool :=
  e.gens.all (fun G => decide (GenOkL q (outerLineList ω e.alpha) G)) &&
    decide (e.words.map (evalW e.gens) = letters)

@[expose] def AlphaCovered (q : ℕ) (table : List (OuterEntry L)) : Prop :=
  ∀ α : L, α ^ (q + 1) = 1 → (¬ ∃ μ : L, μ ^ 3 = α) → ∃ e ∈ table, e.alpha = α

instance (q : ℕ) (table : List (OuterEntry L)) : Decidable (AlphaCovered q table) := by
  unfold AlphaCovered
  infer_instance

@[expose] def outerCheck (q : ℕ) (ω : L) (letters : List (M3 L)) (ws₂ : List (List ℕ))
    (table : List (OuterEntry L)) : Bool :=
  coverBool q (ws₂.map (evalW letters)) && table.all (entryOk q ω letters) &&
    decide (AlphaCovered q table)

end CFSG.LieType.SeitzGeneration.HeisSmall
