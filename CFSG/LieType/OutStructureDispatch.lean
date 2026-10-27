module

public import CFSG.LieType.OutStructureFamilies
public import CFSG.LieType.OutStructureSporadic

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def I713ClauseFor (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* i.Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
        (¬ p ∣ Nat.card (Outer K)) ∨
        (∃ F : Subgroup (MulAut K), (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
          ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
          ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) ∨
        (p = 3 ∧ IsCyclic (Outer K) ∧ OuterPElementLifts K p)

theorem i713_of_clauses (h : ∀ i : TauCeti.CFSGIndex, I713ClauseFor i) : I_7_13_2_5 := by
  intro K _ _ hK hnab hcat p hp hp2 hpRank
  obtain ⟨i, ⟨e⟩⟩ := hcat
  exact h i K hK hnab ⟨e⟩ p hp hp2 hpRank

theorem i713ClauseFor_alternating (n : ℕ) (hn : 5 ≤ n) :
    I713ClauseFor (TauCeti.CFSGIndex.alternating n hn) := by
  intro K _ _ hK hnab ⟨e⟩ p hp hp2 hpRank
  exact i713_alternating hn e hp hp2

theorem i713ClauseFor_sporadic
    (s : TauCeti.SporadicName) :
    I713ClauseFor (TauCeti.CFSGIndex.sporadic s) := by
  intro K _ _ hK hnab ⟨e⟩ p hp hp2 hpRank
  exact Or.inl (i713_of_mulEquiv_sporadic hK hnab e hp hp2)

end CFSG.LieType.OutStructure
