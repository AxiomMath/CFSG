module

public import CFSG.ClassicalInvolution.SmallCases.NDBE1S
public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank

variable (p : ℕ) [Fact p.Prime]

@[expose] def SpinOuterKleinAlpha : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), ExoticModel.SpinTag t n → p ≠ 2 → 5 ≤ p ^ e →
    StatedLieAdmissible t n p e → ∀ (H : Type) [Group H] [Finite H]
      (ψ : (modelUniv t n p e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
      ∀ x : (modelUniv t n p e Fact.out).K, IsUniqueInvolution R x →
      ∀ (v : H) (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)), v * v = 1 →
        (∀ r ∈ R, v * ψ r = ψ r * v) →
        (∀ y : (modelUniv t n p e Fact.out).K, toInducedAutOn ψ.range ⟨v, hv⟩ ≠
          toInducedAutOn ψ.range ⟨ψ y, Subgroup.le_normalizer ⟨y, rfl⟩⟩) →
        alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, Subgroup.le_normalizer ⟨x, rfl⟩⟩,
          toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) = ⊥

end CFSG.ClassicalInvolution.NDB
