module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.RowW
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.RowL3E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem thm3RowsA_of_std (hΩ : TypeRHyp Ω) (hO : classicalInvolutionOddCore G = ⊥)
    {K J : Subgroup G} (hK : K ∈ Ω) {z j : G} (hz : IsUniqueInvolution K z)
    (hzO : TightInO2 z) (hv : AViol Ω K J z j) (hall : aStar Ω K = Ω) (hgen : omegaGen Ω = ⊤) :
    Thm3A.Thm3RowsA Ω ⊤ := by
  by_cases hsplit : ∃ s : G, (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)
  · obtain ⟨s, hs⟩ := hsplit
    exact Or.inr (Or.inr (Or.inl (PhilipHall.Frame.Thm3Quot.isL3E8_of_mulEquiv
      (secQuotTopEquiv hO) (isL3E8_of_e8 hΩ hO hK hz hzO hv hall hgen hs))))
  · push Not at hsplit
    exact Or.inr (Or.inr (Or.inr (rowW_of_e4 hΩ hO hK hz hzO hv hall hgen hsplit)))

theorem thm3RowsG_of_std {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y = ⊥) :
    ∀ Φ : Set (Subgroup Y), TypeRHyp Φ → ∀ K ∈ Φ, ¬ AEmpty Φ K → ∀ z : Y,
      IsUniqueInvolution K z → TightInO2 z → aStar Φ K = Φ → omegaGen Φ = ⊤ →
        Thm3A.Thm3RowsG Φ ⊤ := by
  intro Φ hΦ K hK hA z hz hzO hall hgen
  obtain ⟨J, zK, zJ, hv⟩ := not_aEmpty_iff.mp hA
  rw [← hz.eq hv.hzK] at hv
  exact (thm3RowsA_of_std hΦ hO hK hz hzO hv hall hgen).toRowsG

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
