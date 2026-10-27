module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KcMain
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S152He12E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223P4.Kc

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem isThreePrimeGroup_cv_F4 (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (hq : IsLnTwoQuot X 3) (he : ∃ e ∈ oTwoUpper H ⊓ X, orderOf e = 3)
    (hred : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)))
    (h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I)
    (h12 : He12.StageLemma15212W_F4) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  obtain ⟨H₁, H₂, hpair⟩ := c.inputs.hN.pair
  have h21' := h21 H₁ H₂ hpair
  have hKcle : conjClosure (oTwoUpper H) Mc ≤ Mc ⊓ I :=
    ((h21'.one hred).2.2.1).trans (centralizer_zS_le_inf152 c.inputs)
  obtain ⟨e, heKX, he3⟩ := he
  have hKc : conjClosure (oTwoUpper H) Mc = oTwoUpper H := by
    obtain ⟨B, hB⟩ := c.inputs.hN.sigmaPrime_nonempty
    rcases (h12 G T Mc M c.setting H c.hstar B hB).cases with h | h | h | h
    · exact h
    all_goals
      exact (false_of_perfect c hN hq hKcle (perfect_of_cases (by tauto))
        (le_conjClosure _ _ heKX.1) heKX.2 he3).elim
  exact h21'.two hKc

end S15223P4.Kc

end CFSG.Quasithin
