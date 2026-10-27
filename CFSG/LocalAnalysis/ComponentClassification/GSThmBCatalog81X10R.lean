module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Exit

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF81Exit10Recognition : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f → 3 < p ^ f →
      (Blueprint.OddLieType ↥(generalizedFitting H) ∨
        Blueprint.NativeSporadic.IsSporadic ↥(generalizedFitting H) .M11) →
      h.Concl81

end CFSG.ComponentClassification.GSThmB
