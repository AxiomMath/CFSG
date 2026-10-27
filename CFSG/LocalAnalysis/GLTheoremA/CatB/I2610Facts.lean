module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S9

abbrev FactShape (Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K W : Subgroup Γ), CFSG.Open.IsQuasisimple ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q → W ≤ Subgroup.normalizer (K : Set Γ) →
    IsElemAbelian 3 W → Nat.card ↥W = 3 ^ 3 →
    Nat.card ↥(W ⊓ Subgroup.centralizer (K : Set Γ)) = 3 →
      ∀ J : Subgroup Γ, GLAPComponent 3 (K ⊓ Subgroup.centralizer (W : Set Γ)) J →
        ¬ catalogIs (PSimple 3 J) isL2prime

@[expose] def I2610FactU6 : Prop :=
  FactShape isU6two

@[expose] def I2610FactF4 : Prop :=
  FactShape isF4two

@[expose] def I2610FactTE6 : Prop :=
  FactShape isTE6two

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
