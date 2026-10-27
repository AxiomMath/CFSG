module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516COmega

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def CF516CentU4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Nat.card (center Y) = 2 →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p f →
    ∀ α : MulAut Y, α ^ 2 = 1 →
      ∃ N : Subgroup Y, (∀ y ∈ N, α y = y) ∧
        (⁅N, N⁆ = N ∨ (p ^ f = 3 ∧ N ≤ closure {y : Y | α y = y ∧ Odd (orderOf y)})) ∧
        (center Y ≤ N ∨
          (∃ A : Subgroup Y, A ≤ N ∧ (∀ u ∈ A, ∀ v ∈ A, u * v = v * u) ∧ Nat.card A = 8 ∧
            ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ orderOf u = 2 ∧ orderOf v = 2) ∨
          ((∀ t : Y, α ≠ MulAut.conj t) ∧ 4 ∣ Nat.card N))

theorem cf516Cent_of_unitary (hU : CF516CentU4) : CF516Cent := by
  intro Y _ _ hY hZ p f hp hp2 hf hm α hα
  rcases hm with hL | hU' | ⟨e, rfl, hO⟩
  · exact Cent516.cent516_linear hY hZ hp hp2 hL α hα
  · exact hU Y hY hZ p f hp hp2 hf hU' α hα
  · obtain ⟨N, hfix, hperf, hconcl⟩ := Cent516.cent516_omega hY hZ hp hp2 (by omega) hO α hα
    exact ⟨N, hfix, Or.inl hperf, hconcl.imp id Or.inr⟩

end CFSG.ComponentClassification.GSThmB
