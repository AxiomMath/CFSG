module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open scoped Pointwise commutatorElement

@[expose] def KFactA9NotInvolvedK34Classical : Prop :=
  ∀ (S : Type) [Group S] [Finite S],
    ((∃ p f : ℕ, p ≠ 3 ∧ CFSG.Blueprint.LieModel S .PSp 3 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ CFSG.Blueprint.LieModel S .POmegaMinus 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel S .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧ CFSG.Blueprint.LieModel S .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel S .PSL 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel S .PSU 6 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ CFSG.Blueprint.LieModel S .PSL 7 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ CFSG.Blueprint.LieModel S .PSU 7 p f) ∨
      (∃ p f : ℕ, p ≠ 3 ∧ CFSG.Blueprint.LieModel S .POmegaOdd 3 p f)) →
    ∀ I : Subgroup S, ⁅I, I⁆ = I → ∀ φ : ↥I →* alternatingGroup (Fin 9),
      Function.Surjective φ → IsPGroup 2 φ.ker → False

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
