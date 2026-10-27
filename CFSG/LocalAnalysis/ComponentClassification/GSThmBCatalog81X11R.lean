module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Exit

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def CF81Exit11Recognition : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → (∀ M : Subgroup H, IsComponent M → GSRestricted (↥M ⧸ center ↥M)) →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2 →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1 → h.Concl81

end CFSG.ComponentClassification.GSThmB
