module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Blueprint CFSG.Blueprint.Chevalley


@[expose] def node0 (τ : Tag) : Fin τ.rank := ⟨0, Tag.rank_pos τ⟩

@[expose] def rf (τ : Tag) (a b : Fin τ.rank → ℤ) : ℤ :=
  dotProduct a (Matrix.mulVec τ.symmetrizedCartan b)

@[expose] def rootB (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  decide (List.ofFn v ∈ τ.artifactRoots)

theorem isRoot_of_rootB {τ : Tag} {v : Fin τ.rank → ℤ} (h : rootB τ v = true) : IsRoot τ v := by
  rw [rootB, decide_eq_true_eq] at h
  exact isRoot_iff_mem_artifactRoots.2 h

@[expose] def PsiOK (τ : Tag) (Ψ : List (Fin τ.rank → ℤ)) : Bool :=
  Ψ.all (fun ε => rootB τ ε && decide (ε (node0 τ) = 1)) &&
    Ψ.all (fun ε => Ψ.all (fun ε' => decide (ε = ε') || decide (0 ≤ rf τ ε ε')))

@[expose] def chainOK (τ : Tag) (Ψ : List (Fin τ.rank → ℤ)) (γ β β' : Fin τ.rank → ℤ) : Bool :=
  rootB τ β && rootB τ β' && decide (β (node0 τ) = 0) && decide (β' (node0 τ) = 0) &&
    decide (rf τ γ β = -1) && rootB τ (γ + β + β') &&
    Ψ.all (fun ε => decide (0 ≤ rf τ ε β) ||
      (decide (rf τ ε β = -1) && decide (ε + β ∈ Ψ) && rootB τ (ε + β))) &&
    Ψ.all (fun ε => decide (ε = γ) || decide (rf τ ε β ≠ -1) ||
      decide (0 ≤ rf τ (ε + β) β'))

theorem PsiOK_spec {τ : Tag} {Ψ : List (Fin τ.rank → ℤ)} (h : PsiOK τ Ψ = true) :
    (∀ ε ∈ Ψ, IsRoot τ ε) ∧ (∀ ε ∈ Ψ, ε (node0 τ) = 1) ∧
      ∀ ε ∈ Ψ, ∀ ε' ∈ Ψ, ε ≠ ε' → 0 ≤ rf τ ε ε' := by
  simp only [PsiOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun ε hε => isRoot_of_rootB (h1 ε hε).1, fun ε hε => (h1 ε hε).2,
    fun ε hε ε' hε' hne => ?_⟩
  rcases h2 ε hε ε' hε' with h | h
  · exact absurd h hne
  · exact h

theorem chainOK_spec {τ : Tag} {Ψ : List (Fin τ.rank → ℤ)} {γ β β' : Fin τ.rank → ℤ}
    (h : chainOK τ Ψ γ β β' = true) :
    IsRoot τ β ∧ IsRoot τ β' ∧ β (node0 τ) = 0 ∧ β' (node0 τ) = 0 ∧ rf τ γ β = -1 ∧
      IsRoot τ (γ + β + β') ∧
      (∀ ε ∈ Ψ, 0 ≤ rf τ ε β ∨ (rf τ ε β = -1 ∧ ε + β ∈ Ψ ∧ IsRoot τ (ε + β))) ∧
      ∀ ε ∈ Ψ, ε ≠ γ → rf τ ε β = -1 → 0 ≤ rf τ (ε + β) β' := by
  simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hb'⟩, h0⟩, h0'⟩, hγ⟩, hsum⟩, h1⟩, h2⟩ := h
  refine ⟨isRoot_of_rootB hb, isRoot_of_rootB hb', h0, h0', hγ, isRoot_of_rootB hsum,
    fun ε hε => ?_, fun ε hε hne hr => ?_⟩
  · rcases h1 ε hε with h | ⟨⟨h3, h4⟩, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨h3, h4, isRoot_of_rootB h5⟩
  · rcases h2 ε hε with (h | h) | h
    · exact absurd h hne
    · exact absurd hr h
    · exact h

end CFSG.LocalAnalysis.GLTheoremA.I107X

end
