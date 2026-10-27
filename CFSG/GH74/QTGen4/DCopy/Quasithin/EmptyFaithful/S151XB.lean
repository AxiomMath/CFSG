module

public import CFSG.Quasithin.EmptyFaithful.S151XB
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.T1515cE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem q1OffenderV15128_of_F4 (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) :
    Q1OffenderV15128 Mc Z₁ L := by
  have hLN : g1_1516 Z₁ ≤ Subgroup.normalizer (L : Set G) := by
    have h := normalizer_le_normalizer_oPrimeResidualOf1516 3 (g1_1516 Z₁)
    rw [← hc.h25.one] at h
    exact Subgroup.le_normalizer.trans h
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    ((q1_1516_le Mc Z₁).trans (mZ1516_le_g1 Mc Z₁)).trans hLN
  have h := hC27 G (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) L (vC27Of15128 Mc Z₁ L)
    hc.h18.five.2.2 hc.hL.comp hc.hL.quasi hc.h26.1 hc.hL.not_le hRN rfl
  obtain ⟨-, ⟨-, hV, -, A, hA, hAoff⟩, -⟩ := h
  exact ⟨hV, A, hA, hAoff⟩

theorem offender15128_of_F4 (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (nTr : Input15128OffenderTransfer) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
      Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L → Q1Offender15128 T Mc Z₁ Z₂ L :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc =>
    nTr G T Mc M Z₁ Z₂ V₁ V₂ L hc (q1OffenderV15128_of_F4 hC27 hc)

theorem lemma15128InputU_of_named_inputs_F4 (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (nTr : Input15128OffenderTransfer) (nML : Input15128ML)
    (nN : Input15128Natural) (nS : Input15128SumNatDual) : Lemma15128InputU_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 h25 h26 h27
  have hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L := ⟨hC, h17, h18, h19, hL, h22, h24, h25, h26, h27⟩
  have hoff := offender15128_of_F4 hC27 nTr G T Mc M Z₁ Z₂ V₁ V₂ L hc
  by_cases hsum : SumNatDual15127 Z₂ L
  · exact (nS G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hoff).elim
  · obtain ⟨hML1, hML2⟩ := nML G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum
    obtain ⟨hnat, hcard⟩ := nN G T Mc M Z₁ Z₂ V₁ V₂ L hc hsum hML2 hoff
    exact ⟨hnat, hcard, hML1, hML2⟩

end CFSG.Quasithin
