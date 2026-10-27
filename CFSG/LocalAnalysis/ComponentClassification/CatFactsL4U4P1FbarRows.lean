module

public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore

variable {n : ℕ}

@[expose] def FbarRowFacts (A₀ : Subgroup (Equiv.Perm (Fin n))) (first : Bool) (r : Row) : Prop :=
  match r.kind with
  | .inner => r.row.outer = false ∧ first = false
  | .noFive =>
      ¬ 5 ∣ Nat.card ↥(A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))))
  | .small gs _ =>
      ¬ 5 ∣ Nat.card ↥(A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n)))) ∧
        (∀ g ∈ gs, Rep n g (tp n g)) ∧
        genOf n gs ≤ A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ∧
        A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ≤
          normalizer (genOf n gs : Set (Equiv.Perm (Fin n)))
  | .five gs ord =>
      (∀ g ∈ gs, tp n g ∈ A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ∧
        orderOf (tp n g) = 5) ∧ Nat.card ↥(genOf n gs) = ord
  | .a6 l₁ l₂ _ =>
      Rep n l₁ (tp n l₁) ∧ Rep n l₂ (tp n l₂) ∧
        genOf n [l₁, l₂] ≤ A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ∧
        A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n))) ≤
          normalizer (genOf n [l₁, l₂] : Set (Equiv.Perm (Fin n))) ∧
        (∃ a : ℕ, (genOf n [l₁, l₂]).relIndex
          (A₀ ⊓ centralizer ({tp n r.row.rep} : Set (Equiv.Perm (Fin n)))) = 2 ^ a) ∧
        Nonempty (↥(genOf n [l₁, l₂]) ≃* alternatingGroup (Fin 6))

end CFSG.ComponentClassification.HarrisLit.P1
