module

public import CFSG.ClassicalInvolution.Q3.Q3NMAut
public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Asc77

@[expose] def Model165Aut : Prop :=
  ∀ (L : Type) [Group L] [Finite L],
    ((IsSimpleGroup L ∧ ((∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (CFSG.Blueprint.LieModel L .PSL 3 p f ∨ CFSG.Blueprint.LieModel L .PSU 3 p f)) ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic L .M11)) ∨
      (Group.IsPerfect L ∧
        CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12)) →
    ∀ 𝒳 : Subgroup (MulAut L), Q3NM.innSubgroup L ≤ 𝒳 →
      ∀ A : Subgroup ↥𝒳, (∀ a ∈ A, ((a : ↥𝒳) : MulAut L) ∈ Q3NM.innSubgroup L) →
        (∀ a ∈ A, a * a = 1) → Nat.card ↥A = 4 → alphaOf A = ⊥

end CFSG.ClassicalInvolution.Q3.TL4
