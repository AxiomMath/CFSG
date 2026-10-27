module

public import CFSG.Blueprint.ChevalleyRootArtifact

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint.Chevalley

@[expose] def gomiRootVec {r : ℕ} (l : List ℤ) : Fin r → ℤ := fun i => l.getD i 0

@[expose] def gomiPosEvenCount (τ : Tag) (m : Fin τ.rank → Bool) : ℕ :=
  ((τ.artifactRoots).filter (fun l => decide (0 < ∑ i : Fin τ.rank, gomiRootVec l i) &&
    decide (Even (∑ i : Fin τ.rank, if m i then gomiRootVec l i else 0)))).length

theorem gomi_f4_count :
    ∀ m : Fin Tag.F4.rank → Bool, (∃ i, m i = true) → 5 ≤ gomiPosEvenCount Tag.F4 m := by
  decide +kernel

theorem gomi_e6_count :
    ∀ m : Fin Tag.E6.rank → Bool, (∃ i, m i = true) → 5 ≤ gomiPosEvenCount Tag.E6 m := by
  decide +kernel

theorem gomi_e7_count :
    ∀ m : Fin Tag.E7.rank → Bool, (∃ i, m i = true) → 5 ≤ gomiPosEvenCount Tag.E7 m := by
  decide +kernel

theorem gomi_e8_count :
    ∀ m : Fin Tag.E8.rank → Bool, (∃ i, m i = true) → 5 ≤ gomiPosEvenCount Tag.E8 m := by
  decide +kernel

theorem gomi_count {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (m : Fin τ.rank → Bool) (hm : ∃ i, m i = true) : 5 ≤ gomiPosEvenCount τ m := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact gomi_f4_count m hm
  · exact gomi_e6_count m hm
  · exact gomi_e7_count m hm
  · exact gomi_e8_count m hm

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
