module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDegree
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2XSurvivor {X : Type} [Group X] (R A X₀ : Subgroup X) : Prop :=
  (∀ W : Subgroup X, W ≤ X₀ → X₀ ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ A ≤ W) ∧
    X₀ ⊓ Subgroup.centralizer (A : Set X) ≤ R

@[expose] def D2XSurvivorAt (i : TauCeti.CFSGIndex) (Pp : ℕ → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Pp p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → (R : Subgroup X) = A → Nonempty (K ≃* i.Group) →
    D2XSurvivor (R : Subgroup X) A X₀

@[expose] def KFactUnitaryThreeSylow : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex),
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
    (∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    ∀ [Fact p.Prime] (T : Sylow p K), Nat.card T = p ^ 3

@[expose] def D2AltSurvivorFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), 5 ≤ p → ∀ (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* alternatingGroup (Fin (2 * p))) →
    D2XSurvivor (R : Subgroup X) A X₀

theorem d2XSurvivorAt_alt_of (hA : D2AltSurvivorFacts)
    (hA6 : D2XSurvivorAt (.alternating 6 (by norm_num)) fun p => p = 3) (n : ℕ) (hn : 5 ≤ n) :
    D2XSurvivorAt (.alternating n hn) fun _ => True := by
  intro X _ _ p _ R A X₀ K hK hRA ⟨e⟩
  have hn2 : n = 2 * p := hK.eq_two_mul_of_alternating hn e
  subst hn2
  have hp2 := hK.ne_two
  have hp3 := hK.prime.two_le
  rcases (show p = 3 ∨ 5 ≤ p by
      rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hK.prime) (by norm_num)
      · exact Or.inr h) with h3 | h5
  · subst h3
    exact hA6 X 3 rfl R A X₀ K hK hRA ⟨e⟩
  · exact hA X p h5 R A X₀ K hK ⟨e⟩

end CFSG.AGLEmbeddingD2
