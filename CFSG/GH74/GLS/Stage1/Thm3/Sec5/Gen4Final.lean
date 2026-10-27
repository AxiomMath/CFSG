module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Gen4B
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Extremal
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem52

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.Blueprint
open scoped commutatorElement

@[expose] def Std4Gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G), Std4 G z S K₁ K₂ → Gen4 G

theorem prop_5_1_gen4 (hII : II4_4_4_center) (hq : CFSG.GH74.GLS.Stage1.Thm3.Sec6.II4_4_quat)
    (h41 : Prop4_1) (h15 : IG_15_16_ext) (hE : P_normal_four) (h52a : IVK_1_2j_52)
    (h52b : IVK_1_9_52) (h32 : IVK_3_2_lifted) (hgen : Std4Gen4) : Prop5_1 := by
  intro G _ _ z S K₁ K₂ h hm₁ hm₂ a haS ha2 haz hf₁ hf₂ hcomm
  have hQ : Qz S z = zpowers z := (h41 G z S K₁ K₂ h).1
  obtain ⟨a', x, hctr⟩ :=
    exists_extremal hII h15 hE ⟨h, hQ, hm₁, hm₂⟩ ⟨haS, ha2, haz, hf₁, hf₂⟩ hcomm
  have h53 : L53 z S K₁ K₂ a' := lemma_5_3 h32 (lemma_5_2 hII h52a h52b) G z S K₁ K₂ a' x hctr
  exact (Rank5.false_of_ctr5_L53_gen4 (hgen G z S K₁ K₂ h) hII hq hctr h53).elim

end CFSG.GH74.GLS.Stage1.Thm3.Sec5
