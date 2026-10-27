module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15SExact
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RVertexExclFin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Open (classicalInvolutionOddCore)

section Sec

variable {p f : ℕ} [Fact p.Prime]

theorem secAEmpty_proved : SecAEmpty p f := by
  intro hp hq G _ _ Ω hΩ hA c hc2 _ K hK
  have hΛ : HypOmegaMod p f
      (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c)) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥(exLayer Ω c))) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥(exLayer Ω c)
  have hΛ' : HypOmegaMod p f
      (quotFamily (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c))
        (classicalInvolutionOddCore ↥(exLayer Ω c))) :=
    oddQuotHyp p f hp hq ↥(exLayer Ω c) _ hΛ _ hN
  have hfam : secFam Ω c =
      quotFamily (restrictFamily (centralizingMembers (exactFamily Ω c) {c}) (exLayer Ω c))
        (classicalInvolutionOddCore ↥(exLayer Ω c)) := rfl
  rw [hfam] at hK ⊢
  exact aEmpty_quotFamily hp hq hΛ hΛ' hN (aEmpty_exactPair hp hq hΩ hA hc2) K hK

theorem g2VertexExcl_proved : G2VertexExcl p f :=
  g2VertexExcl_of_secAEmpty secAEmpty_proved

theorem g2d4VertexExcl_proved : G2D4VertexExcl p f :=
  g2d4VertexExcl_of_g2 g2VertexExcl_proved

theorem g2VertexExclFuzzy_proved : G2VertexExclFuzzy p f :=
  fun hp hq G _ _ Ω hΩ hA c hc2 _ D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j =>
    g2VertexExcl_proved hp hq G Ω hΩ hA c hc2 D j hG2 M M' b hM hM' hMb hM'b hne hMj hM'j

end Sec

end CFSG.ClassicalInvolution.Asc77
