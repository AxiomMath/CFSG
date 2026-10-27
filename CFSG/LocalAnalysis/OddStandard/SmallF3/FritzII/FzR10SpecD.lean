module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Rules
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319IdxEv

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Certificates.FzL26 Certificates.FzR10 CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def FzFusionSpec : Prop :=
  ∀ t s l : MulAut FzUT, FzValidTriple t s l →
    (∀ x₁, FzValidX t l x₁ → FzShape t s l x₁) ∨
      ¬ ∃ θ : ℕ → Prop,
        FzRules (parOf (pctx ()) (fzAutI t) (actTab (fzAutI t) (fzAutI s) (fzAutI l))) θ

end CFSG.OddStandard.SmallF3.FritzII
