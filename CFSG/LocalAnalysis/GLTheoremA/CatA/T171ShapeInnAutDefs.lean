module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def InnAutDerivedInnDiag (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {Γ : Type} [Group Γ] [Finite Γ] (p : ℕ) (J : Subgroup Γ) (a : Γ)
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ)), p.Prime →
    IsQuasisimple (PQuot p J) → catalogIs (PSimple p J) (onLie F) →
    MI.indAut p J a haJ ∈ innAutDerived (PSimple p J) →
    InnDiagOn p (Subgroup.zpowers a) J

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
