module

public import CFSG.GH74.Conclusion
public import CFSG.GH74.GLS.Classes
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup Blueprint Assembly.LowTwoRank

variable {K K' : Type} [Group K] [Group K']

theorem hasL2Model_of_mulEquiv {P : ℕ → Prop} (e : K ≃* K') (h : HasL2Model K P) :
    HasL2Model K' P := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  exact ⟨p, f, hp, hf, hP, CFSG.GH74.lieModel_of_mulEquiv e hL⟩

theorem hasSL2Model_of_mulEquiv {P : ℕ → Prop} (e : K ≃* K') (h : HasSL2Model K P) :
    HasSL2Model K' P := by
  obtain ⟨F, hF, hfin, hP, ⟨e'⟩⟩ := h
  exact ⟨F, hF, hfin, hP, ⟨e.symm.trans e'⟩⟩

theorem isDoubleCoverOfAlt_of_mulEquiv {n : ℕ} (e : K ≃* K') (h : IsDoubleCoverOfAlt K n) :
    IsDoubleCoverOfAlt K' n := by
  obtain ⟨hq, hc, ⟨e'⟩⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hc
  · exact ⟨(QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)).symm.trans e'⟩

theorem isL34Quotient_of_mulEquiv (e : K ≃* K') (h : IsL34Quotient K) : IsL34Quotient K' :=
  CFSG.GH74.lieModel_of_mulEquiv
    (QuotientGroup.congr (center K) (center K') e (Subgroup.map_center_eq e)) h

theorem inT2_of_mulEquiv (e : K ≃* K') (h : InT2 K) : InT2 K' := by
  obtain ⟨hq, h⟩ := h
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_⟩
  rcases h with h | h | h | ⟨n, hn7, hn11, h⟩ | ⟨h, hexp⟩
  · exact Or.inl (hasL2Model_of_mulEquiv e h)
  · exact Or.inr (Or.inl (hasSL2Model_of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (CFSG.GH74.nonempty_alternating_of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn7, hn11, isDoubleCoverOfAlt_of_mulEquiv e h⟩)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨isL34Quotient_of_mulEquiv e h, ?_⟩)))
    rw [← Monoid.exponent_eq_of_mulEquiv (Subgroup.centerCongr e)]
    exact hexp

theorem inB2_of_mulEquiv (e : K ≃* K') (h : InB2 K) : InB2 K' := by
  refine ⟨inT2_of_mulEquiv e h.1, fun hbot => h.2 ?_⟩
  have h1 : (center K).map (e : K →* K') = ⊥ := by
    rw [Subgroup.map_center_eq e]
    exact hbot
  exact (Subgroup.map_eq_bot_iff_of_injective (center K) e.injective).mp h1

end CFSG.GH74.GLS.TwoThin
