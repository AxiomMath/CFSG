module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Glue

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

@[expose] def Lem65_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ →
    Qz S z = zpowers z → Cond6a S K₁ → Cond6a S K₂ → ¬ IsDoubleCoverOfAlt (HatT K₁) 7

theorem lemma_6_5 (h41 : Prop4_1) (hc : Lem65_core) : Lemma6_5 := by
  intro G _ _ z S K₁ K₂ h ha₁ ha₂
  have hQ : Qz S z = zpowers z := (h41 G z S K₁ K₂ h).1
  exact ⟨hc G z S K₁ K₂ h hQ ha₁ ha₂, hc G z S K₂ K₁ h.swap hQ ha₂ ha₁⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6
