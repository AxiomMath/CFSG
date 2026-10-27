module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Asc77.FrameVertex

section Statement

variable (p : ℕ) [Fact p.Prime]

@[expose] def Z2NoD8 : Prop :=
  ∀ (t : StatedLieTag) (k e : ℕ), p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t k p e →
    ((t = .PSL ∧ k = 3 ∧ p ^ e % 4 = 3) ∨ (t = .PSU ∧ k = 3 ∧ p ^ e % 4 = 1)) →
    ∀ {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
      ∀ (R : Subgroup (modelUniv t k p e Fact.out).K) (x : (modelUniv t k p e Fact.out).K),
        R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D →
        x ∈ R → x * x = 1 → x ≠ 1 →
        ∀ (a v : ↥(inducedAutOn ψ.range)),
          (∀ r ∈ R, a * innerHom ψ r = innerHom ψ r * a) →
          (∀ r ∈ R, v * innerHom ψ r = innerHom ψ r * v) →
          a * a = innerHom ψ x → v * v = 1 → v * a * v⁻¹ = a⁻¹ → False

end Statement

end S16

end CFSG.ClassicalInvolution.Asc77
