module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Assembly

namespace Dichotomy

@[expose] def dichotomyStronglyEmbedded {G : Type*} [Group G] (M : Subgroup G) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card M) ∧
    ∀ g : G, g ∉ M → Odd (Nat.card ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom))

@[expose] def dichotomyCharP (p : ℕ) (H : Type*) [Group H] : Prop :=
  Subgroup.centralizer (pCore p H : Set H) ≤ pCore p H

end Dichotomy
end CFSG.Assembly
