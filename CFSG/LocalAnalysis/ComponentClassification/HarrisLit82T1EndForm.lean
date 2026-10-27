module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris82TheoremOneKProper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G → ¬ Blueprint.Catalog G →
    ∀ (zz : G), orderOf zz = 2 → ∀ (J : Subgroup ↥(centralizer ({zz} : Set G))),
      IsPComponent 2 J → (⟨zz, mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(centralizer ({zz} : Set G))) ∈ J →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsMType p ↥J

end CFSG.ComponentClassification.HarrisLit
