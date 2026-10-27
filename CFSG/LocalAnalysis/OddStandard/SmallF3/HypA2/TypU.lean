module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HLargeInputs
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

@[expose] def TypU (K : Type) [Group K] : Prop :=
  (∃ q : ℕ, Odd q ∧ 9 ≤ q ∧ HarrisLit.IsSLTwoOver q (K ⧸ pPrimeCore 2 K)) ∨
    (∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ GSThmB.TypChev r K) ∨
    LieModel (K ⧸ Open.fusionZStar K) .PSp 2 3 1 ∨
    (∃ n : ℕ, 7 ≤ n ∧ GH74.GLS.IsDoubleCoverOfAlt (K ⧸ pPrimeCore 2 K) n)

theorem isSLTwoOver_of_mulEquiv {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : HarrisLit.IsSLTwoOver q A) : HarrisLit.IsSLTwoOver q B := by
  obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i₁, i₂, hF, ⟨e.symm.trans eF⟩⟩

theorem isDoubleCoverOfAlt_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    {n : ℕ} (h : GH74.GLS.IsDoubleCoverOfAlt Q n) :
    GH74.GLS.IsDoubleCoverOfAlt Q' n := by
  obtain ⟨hQ, hcard, ⟨eQ⟩⟩ := h
  have hmap : (center Q).map e.toMonoidHom = center Q' := Subgroup.map_center_eq e
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hQ, ?_, ?_⟩
  · rw [← hmap, Subgroup.card_map_of_injective (K := center Q) (f := e.toMonoidHom) e.injective,
      hcard]
  · exact ⟨(QuotientGroup.congr (center Q) (center Q') e hmap).symm.trans eQ⟩

theorem coreInvariant_typU : GS82PumpInputs.CoreInvariant TypU := by
  intro A B _ _ ⟨e⟩ h
  unfold TypU at h
  rcases h with h | h | h | h
  · obtain ⟨q, hqodd, hq9, hSL⟩ := h
    exact Or.inl ⟨q, hqodd, hq9, isSLTwoOver_of_mulEquiv e hSL⟩
  · obtain ⟨r, hrprime, hrne2, hChev⟩ := h
    exact Or.inr (Or.inl ⟨r, hrprime, hrne2, GSThmB.coreInvariant_typChev r A B ⟨e⟩ hChev⟩)
  · exact Or.inr (Or.inr (Or.inl (LieModel.of_mulEquiv (Sol78.fusionZStarQuotOfCore e) h)))
  · obtain ⟨n, hn7, hDC⟩ := h
    exact Or.inr (Or.inr (Or.inr ⟨n, hn7, isDoubleCoverOfAlt_of_mulEquiv e hDC⟩))

end CFSG.OddStandard.SmallF3.HypA2
