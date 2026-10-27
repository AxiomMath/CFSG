module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairF4Data
public import CFSG.LieType.Chevalley.RootCommutatorPairs

public section

namespace CFSG.HardMathSupport.Foote.Proving

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap

theorem commPairs_eq_single_of_string_one {τ : Tag} {α β : Fin τ.rank → ℤ}
    (hsum : IsRoot τ (α + β))
    (hno : ∀ p ∈ commCandidates, p ≠ (1, 1) → ¬ IsRoot τ (p.1 • α + p.2 • β)) :
    commPairs τ α β = [(1, 1)] := by
  have hmem11 : ((1, 1) : ℕ × ℕ) ∈ commPairs τ α β := by
    rw [mem_commPairs]
    refine ⟨by decide, ?_⟩
    simpa using hsum
  have hall : ∀ p ∈ commPairs τ α β, p = (1, 1) := by
    intro p hp
    rw [mem_commPairs] at hp
    by_contra hne
    exact hno p hp.1 hne hp.2
  have hnd := commPairs_nodup (τ := τ) α β
  generalize commPairs τ α β = l at hmem11 hall hnd ⊢
  rcases l with _ | ⟨a, _ | ⟨b, s⟩⟩
  · simp at hmem11
  · rw [hall a (List.mem_singleton_self a)]
  · exfalso
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    have hn := List.nodup_cons.mp hnd
    apply hn.1
    simp [ha, hb]

end CFSG.HardMathSupport.Foote.Proving
