module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinLift

public section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn)

@[expose] def luLinTuples (n f : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | (∃ k, 2 ≤ k ∧ k < n ∧ x = (.PSL, k, f)) ∨ (Even n ∧ x = (.PSL, n / 2, 2 * f))}

@[expose] def luUniTuples (n f : ℕ) : Set (StatedLieTag × ℕ × ℕ) :=
  {x | (∃ k, 3 ≤ k ∧ k < n ∧ x = (.PSU, k, f)) ∨ x = (.PSL, 2, f) ∨
    (Even n ∧ x = (.PSL, n / 2, 2 * f))}

theorem luLinTuples_fst {n f : ℕ} {x : StatedLieTag × ℕ × ℕ} (hx : x ∈ luLinTuples n f) :
    x.1 = .PSL := by
  rcases hx with ⟨k, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem luUniTuples_fst {n f : ℕ} {x : StatedLieTag × ℕ × ℕ} (hx : x ∈ luUniTuples n f) :
    x.1 = .PSU ∨ x.1 = .PSL := by
  rcases hx with ⟨k, -, -, rfl⟩ | rfl | ⟨-, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

theorem exists_lieModel_of_modelIn {p : ℕ} {T : Set (StatedLieTag × ℕ × ℕ)}
    (hT : ∀ x ∈ T, x.1 = .PSL ∨ x.1 = .PSU) {L : Type} [Group L] (h : ModelIn p T L) :
    ∃ k s : ℕ, Blueprint.LieModel (L ⧸ center L) .PSL k p s ∨
      Blueprint.LieModel (L ⧸ center L) .PSU k p s := by
  obtain ⟨t, n, f, hmem, -, hlm⟩ := h
  rcases hT _ hmem with ht | ht
  · obtain rfl : t = .PSL := ht
    exact ⟨n, f, Or.inl hlm⟩
  · obtain rfl : t = .PSU := ht
    exact ⟨n, f, Or.inr hlm⟩

end CFSG.OddStandard.HigherRank.LinUnit
