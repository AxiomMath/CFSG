module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7

variable {G : Type} [Group G] [Finite G]

theorem prop71_of_sec6 (hS : GLStanding G 4 3) {B : Subgroup G} (hB : IsBOneMax 3 B)
    (h63 : ∃ M₀ : Subgroup G, Prop63Out B M₀) (h67 : Prop67Out B) (h68 : Prop68Out B)
    (hU : UniqComp B) (h75 : Lemma75Stmt B) (h76 : Lemma76Stmt B) (h710 : Lemma710Stmt B) :
    ∃ M : Subgroup G, IsPreUniquenessSubgroup 3 B M := by
  obtain ⟨M₀, h63⟩ := h63
  by_contra hno
  by_cases hC : Case1Hyp B
  · exact not_case1_of_no_preUniqueness hS hB h63 h67 h68 hU h75 h76 hno hC
  · unfold Case1Hyp at hC
    push Not at hC
    obtain ⟨K₁, K₂, hK₁, hK₂, hne⟩ := hC
    have hfin := Sec7.lemma715 hS hB h63 h68 hU h75 h76 h710 hK₁ hK₂ hne
    have hall : ∀ K' : Subgroup G, IsHSet B K' →
        K' ≤ K₁ ⊔ gammaOneThree B ∨ K' ≤ K₂ ⊔ gammaOneThree B := fun K' hK' =>
      Sec7.lemma714 hS hB h68 hU h75 h710 hK₁ hK₂ hne hK'
    have hM2M1 := gammaOneThree_le_glbCore B
    have hK₁N : K₁ ≤ K₂ ⊔ K₁ ⊔ GLBCore 3 3 B := le_sup_right.trans le_sup_left
    have hK₂N : K₂ ≤ K₂ ⊔ K₁ ⊔ GLBCore 3 3 B := le_sup_left.trans le_sup_left
    have hM₁N : GLBCore 3 3 B ≤ K₂ ⊔ K₁ ⊔ GLBCore 3 3 B := le_sup_right
    have hBN : B ≤ K₂ ⊔ K₁ ⊔ GLBCore 3 3 B :=
      ((le_gammaOneThree_self hS hB).trans hM2M1).trans hM₁N
    refine hno ⟨K₂ ⊔ K₁ ⊔ GLBCore 3 3 B, ?_, hM₁N, ?_⟩
    · refine iSup₂_le fun x hx => iSup_le fun hx1 => ?_
      refine lambdaStar_le_of_lambdaOf_le hS hB hM₁N hx ?_
      refine sSup_le fun L hL => ?_
      by_cases hLM : L ≤ GLBCore 3 3 B
      · exact hLM.trans hM₁N
      · rcases hall L (h67 x hx hx1 L hL.1 hL.2 hLM) with h | h
        · exact h.trans (sup_le hK₁N (hM2M1.trans hM₁N))
        · exact h.trans (sup_le hK₂N (hM2M1.trans hM₁N))
    · exact even_card_glaPPrimeCoreOf_of_le h75 h76 hK₁ hfin hBN
        (sup_le hK₁N (hM2M1.trans hM₁N))

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
