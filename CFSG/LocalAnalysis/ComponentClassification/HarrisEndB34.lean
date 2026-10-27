module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB34Mult

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris311PSL2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    IsSimpleGroup ↥(Open.genFittingFStar G) → HarrisF p ↥(Open.genFittingFStar G) →
    ∀ J : Subgroup G, IsInvolutionTwoComponent J →
      (∃ p' f' : ℕ, Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f') →
        pPrimeCore 2 ↥J ≤ center ↥J

@[expose] def Harris81Lemma34NineInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 →
    IsSimpleGroup ↥(Open.genFittingFStar G) → HarrisF p ↥(Open.genFittingFStar G) →
    ∀ J : Subgroup G, IsInvolutionTwoComponent J → ∀ p' f' : ℕ,
      Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p' f' → p' ^ f' = 9 →
        pPrimeCore 2 ↥J ≤ center ↥J → pPrimeCore 2 ↥J = ⊥

theorem harris81Lemma34Input_of
    (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput) : Harris81Lemma34Input := by
  intro G _ _ p hp hp2 hS hF J hJ hm
  have hc := h311 G p hp hp2 hS hF J hJ hm
  obtain ⟨p', f', hm'⟩ := hm
  by_cases h9' : p' ^ f' = 9
  · exact h9 G p hp hp2 hS hF J hJ p' f' hm' h9' hc
  · obtain ⟨a, -, hJa⟩ := hJ
    exact EndB.pPrimeCore_eq_bot_of_le_center_psl_two hJa.2.2.1 hc hm' h9'

end CFSG.ComponentClassification.HarrisLit
