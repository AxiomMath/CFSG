module

public import CFSG.CGT.Stroth77.AmbientSplit

public section

namespace CFSG.CGT.Stroth77

@[expose] def StrothExtStep : Prop :=
  ∀ {S : Type} [Group S] [Finite S] {B C S' : Subgroup S} {τ : StrothTypeIndex}
    (D : StrothTypeData B τ), (∀ i, 1 ≤ τ.k i) → τ ≠ StrothTypeIndex.t101 0 → B ≤ C →
    C ≤ Subgroup.centralizer (B : Set S) →
    (Nat.card C = 2 * Nat.card B ∨ Nat.card C = 4 * Nat.card B) →
    (∀ x ∈ C, x * x ∈ B) → D.L ≤ Subgroup.normalizer C →
    NoInvolutionsCentralizing S' B → C ≤ S' →
    ∃ (τ' : StrothTypeIndex) (D' : StrothTypeData C τ'),
      D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ

end CFSG.CGT.Stroth77
