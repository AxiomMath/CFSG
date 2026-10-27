module

public import CFSG.ClassicalInvolution.Asc77.AscC22P7
public import CFSG.ClassicalInvolution.Asc77.AscR31Recog

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace C22P

section Named

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C22_alpha : Prop :=
  p ^ f % 4 = 1 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
        alphaOf (Subgroup.closure ({u₁ * u₂, z} : Set G)) = ⊥

end Named

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem c22_chainPos_of_alpha (hodd : T7Z.OddCenterClassical) (hα : C22_alpha p f) :
    R31.C22_chainPos p f := by
  intro hq1 G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG
  exact chain_of_alpha hodd hq1 hs hW hLG.1 hLG.2 (hα hq1 G Ω K K' K₃ z u₁ u₂ u₃ hs hW hLG)

end Final

end C22P

end CFSG.ClassicalInvolution.Asc77
