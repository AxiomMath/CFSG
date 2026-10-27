module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Final
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6CUniq
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def Sec6Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G], GLStanding G 4 3 → GLCaseFour G 3 →
    ∀ B : Subgroup G, IsExtremal B →
      (∃ M₀ : Subgroup G, Prop63Out B M₀) ∧ Prop67Out B ∧ Prop68Out B

theorem caseFourPreUniqueness_of_inputs (i183 : Input18_3_4) (i25 : Input2_5)
    (i145 : Input14_5) (i252 : Input25_2) (i116 : Input11_6) (i18 : Input18_10)
    (i28 : Input28_8) (h51 : Prop51) (h6 : Sec6Out) : CaseFourPreUniqueness := by
  intro G _ _ m p hS hC
  have hC' := hC
  obtain ⟨hp3, hrk, -⟩ := hC'
  subst hp3
  have hm : m = 4 := by rw [← hS.rank_eq]; exact hrk
  subst hm
  obtain ⟨B, hB⟩ := h51 G 4 hS hC
  obtain ⟨h63, h67, h68⟩ := h6 G hS hC B hB
  exact ⟨B, hB.1, prop71_of_inputs i183 i25 i145 i252 i116 i18 i28 hS hB.1 h63 h67 h68
    (uniqComp_of_B1max hS hB.1)⟩

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
