module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeClose
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

open CFSG.Open TauCeti CFSG.AGLEmbedding CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.AnisoE6 CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Scope

theorem not_isTwoPow_of_seitzGoodIndex_E6 {q : PrimePower}
    (h : SeitzGoodIndex 3 (LieTypeIndex.E6 q)) :
    ¬ (IsTwoPow q 1 ∨ IsTwoPow q 2 ∨ IsTwoPow q 3) := by
  intro hq
  rcases h with h | h
  · exact h (Or.inr ⟨rfl, Or.inr (Or.inl hq)⟩)
  · rcases h with h | h | h <;> simp [IsF4EightIndex, IsD4FourIndex, FourIndex] at h

theorem not_isTwoPow_of_seitzGoodIndex_twE6 {q : PrimePower}
    (h : SeitzGoodIndex 3 (LieTypeIndex.twistedE6 q)) : ¬ IsTwoPow q 1 ∧ ¬ IsTwoPow q 2 := by
  rcases h with h | h
  · exact ⟨fun h1 => h (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl h1))⟩),
      fun h2 => h (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl h2)))⟩)⟩
  · rcases h with h | h | h
    · simp [IsF4EightIndex] at h
    · simp [IsD4FourIndex] at h
    · obtain ⟨-, h3⟩ : IsTwoPow q 3 := h
      refine ⟨fun h1 => ?_, fun h2 => ?_⟩
      · obtain ⟨-, h1⟩ := h1
        omega
      · obtain ⟨-, h2⟩ := h2
        omega

theorem seitzGoodIndex_three_F4 {q : PrimePower} (h1 : ¬ IsTwoPow q 1) (h2 : ¬ IsTwoPow q 2) :
    SeitzGoodIndex 3 (LieTypeIndex.F4 q) := by
  by_cases h8 : IsTwoPow q 3
  · exact Or.inr (Or.inl h8)
  · refine Or.inl ?_
    rintro (⟨-, h⟩ | ⟨-, h | h | h | h | h | h | h⟩)
    · exact h1 h
    · simp [IsL2EightIndex] at h
    · exact h2 h
    · simp [Bal209TwoIndex] at h
    · simp [IsTwistedE6FourIndex] at h
    · exact h8 h
    · simp [IsD4FourIndex] at h
    · simp [FourIndex] at h

theorem not_p1ThreeLieList_F4 {q : PrimePower} (hv : (LieTypeIndex.F4 q).Valid)
    (h1 : ¬ IsTwoPow q 1) : ¬ P1ThreeLieList 3 ⟨.F4 q, hv⟩ := by
  unfold P1ThreeLieList
  rintro (⟨n, q', hq', -⟩ | ⟨q', -, hq'⟩ | ⟨-, m, hm⟩ | ⟨q', ⟨-, -, hq'⟩ | ⟨-, -, -, hq'⟩⟩ | hch)
  · cases hq'
  · cases hq'
  · cases hm
  · cases hq'
  · cases hq'
  · unfold IsP1ChevTwoIndex at hch
    rcases hch with ⟨-, q', hp, he, h⟩ | ⟨-, q', -, -, h⟩ | ⟨h5, -⟩
    · rcases h with h | h | h | h | h | h | h | h <;> (try cases h)
      exact h1 ⟨hp, he⟩
    · rcases h with h | h | h | h <;> cases h
    · omega

theorem valid_lieTypeIndex_F4 (q : PrimePower) : (LieTypeIndex.F4 q).Valid :=
  (LieTypeIndex.valid_iff _).2 ⟨(LieTypeIndex.inStandardRange_iff _).2 trivial, by
    rw [LieTypeIndex.isDuplicateRepresentative_iff]
    exact id⟩

theorem threeScope_F4_of_E6 {K : Type} (h : SeitzExcOpenRest4.ThreeScope LieTypeIndex.E6 K) :
    SeitzExcOpenRest4.ThreeScope LieTypeIndex.F4 K := by
  obtain ⟨q, -, hKq, hgood, -⟩ := h
  have hq := not_isTwoPow_of_seitzGoodIndex_E6 hgood
  exact ⟨q, valid_lieTypeIndex_F4 q, hKq, seitzGoodIndex_three_F4 (fun h => hq (Or.inl h))
    (fun h => hq (Or.inr (Or.inl h))), not_p1ThreeLieList_F4 _ fun h => hq (Or.inl h)⟩

theorem five_le_card_of_threeScope_E6 {K : Type} [Field K] [Finite K] (hK : Nat.card K % 3 = 2)
    (h : SeitzExcOpenRest4.ThreeScope LieTypeIndex.E6 K) : 5 ≤ Nat.card K := by
  obtain ⟨q, -, hKq, hgood, -⟩ := h
  have hq := not_isTwoPow_of_seitzGoodIndex_E6 hgood
  have h2 : Nat.card K ≠ 2 := fun h2 =>
    hq (Or.inl (E6ThreeInner.isTwoPow_of_card_eq' (by rw [← hKq, h2, pow_one])))
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  omega

theorem seven_le_of_twThreeScope {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : q % 3 = 1) (h : E6ThreeInner.TwThreeScope K σ) : 7 ≤ q := by
  obtain ⟨q', -, hKq, -, hgood, -⟩ := h
  have hqq : q'.card = q := Nat.pow_left_injective two_ne_zero (hKq.symm.trans hK)
  have h4 : q ≠ 4 := fun h4 => (not_isTwoPow_of_seitzGoodIndex_twE6 hgood).2
    (E6ThreeInner.isTwoPow_of_card_eq' (by rw [hqq, h4]; norm_num))
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rw [hK] at h1
  have h2 : 2 ≤ q := by
    by_contra hlt
    interval_cases q <;> simp at h1
  omega

theorem threeScope_F4_of_twThreeScope {k K : Type} [Field K] {σ : K ≃+* K}
    (hK : Nat.card K = Nat.card k ^ 2) (h : E6ThreeInner.TwThreeScope K σ) :
    SeitzExcOpenRest4.ThreeScope LieTypeIndex.F4 k := by
  obtain ⟨q, -, hKq, -, hgood, -⟩ := h
  have hqq : q.card = Nat.card k := Nat.pow_left_injective two_ne_zero (hKq.symm.trans hK)
  have hq := not_isTwoPow_of_seitzGoodIndex_twE6 hgood
  exact ⟨q, valid_lieTypeIndex_F4 q, hqq.symm, seitzGoodIndex_three_F4 hq.1 hq.2,
    not_p1ThreeLieList_F4 _ hq.1⟩

end Scope

section D4


@[expose] def E6F4CubeD4Two : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K % 3 = 2 →
    SeitzExcOpenRest4.ThreeScope LieTypeIndex.E6 K →
    ∀ E₀ : Subgroup (adjointGroup .E6 K), E₀ ≤ fixE6 K → IsElemAbelian 3 E₀ →
      Nat.card E₀ = 3 ^ 3 → ¬ NormalizesRGroup (ringChar K) E₀ →
      IsEmpty (LangPlaneData .F4 K (E₀.comap (embE6F4 K))) →
      ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ g ∈ fixE6 K, ∀ f ∈ F, ∀ u : Kˣ,
        Commute (g * f * g⁻¹) (e6AntiA K u) ∧ Commute (g * f * g⁻¹) (e6AntiB K u)

@[expose] def TwE6F4CubeD4One : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] (σ : K ≃+* K)
    (hσ : ∀ c : K, σ c = c ^ Nat.card k)
    (hfix : ∀ c : k, σ (algebraMap k K c) = algebraMap k K c)
    (hK : Nat.card K = Nat.card k ^ 2), Nat.card k % 3 = 1 → E6ThreeInner.TwThreeScope K σ →
    ∀ E₀ : Subgroup (twistedE6RootGroup K σ), E₀ ≤ (phiG σ hfix).range → IsElemAbelian 3 E₀ →
      Nat.card E₀ = 3 ^ 3 → ¬ NormalizesRGroup (ringChar K) E₀ →
      IsEmpty (LangPlaneData .F4 k
        (E₀.comap ((phiG σ hfix).comp (e6FixedF4EquivAll k).symm.toMonoidHom))) →
      ∃ F ≤ E₀, F.relIndex E₀ = 3 ∧ ∃ g ∈ (phiG σ hfix).range, ∀ f ∈ F, ∀ t : Kˣ,
        (t : K) ^ (Nat.card k + 1) = 1 → Commute (g * f * g⁻¹) (torusWord σ hσ hK t)

end D4

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4Close

end
