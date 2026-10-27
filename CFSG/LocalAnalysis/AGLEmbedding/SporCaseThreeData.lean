module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThree.PartOne.StrongP

theorem exists_surjective_ker_eq_center {K X : Type} [Group K] [Group X]
    (e : K ⧸ Subgroup.center K ≃* X) :
    ∃ π : K →* X, Function.Surjective π ∧ π.ker = Subgroup.center K :=
  ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), e.surjective.comp (QuotientGroup.mk'_surjective _),
    by ext x; simp⟩

theorem center_eq_bot_of_kernelTrivialAt {X : Type} [Group X] {p : ℕ} (h : KernelTrivialAt X p)
    {K : Type} [Group K] [Finite K] [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* X)
    (hZp : IsPGroup p (Subgroup.center K)) : Subgroup.center K = ⊥ := by
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  rw [← hker]
  exact h K π hπ hker.le (hker ▸ hZp)

section Iso

variable {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {K : Type} [Group K] [Finite K]

theorem weakCore_or_klingenAlt_of_mulEquiv (f : K ≃* X)
    (h : ∀ T : Sylow p X, GLBWeakCore p (T : Subgroup X) = ⊤ ∨ KlingenAlt p X T)
    (T : Sylow p K) : GLBWeakCore p (T : Subgroup K) = ⊤ ∨ KlingenAlt p K T := by
  have hp : p.Prime := Fact.out
  let T' : Sylow p X := T.mapSurjective (f := f.toMonoidHom) f.surjective
  have hT : (T : Subgroup K) = (T' : Subgroup X).map f.symm.toMonoidHom := by
    ext x
    simp [T']
  rcases h T' with h1 | h1
  · exact Or.inl (glbWeakCore_eq_top_of_mulEquiv hp f.symm hT h1)
  · exact Or.inr (klingenAlt_of_mulEquiv f.symm hT h1)

omit [Fact p.Prime] in
theorem pRank_sylow_le_two_of_mulEquiv (hp : p.Prime) (f : K ≃* X)
    (h : Open.pRank p (⊤ : Subgroup X) ≤ 2) (T : Sylow p K) :
    Open.pRank p (T : Subgroup K) ≤ 2 :=
  (PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp f.toMonoidHom f.injective
    (T : Subgroup K)).symm.le.trans ((PreuniquenessRankFour.Helpers.pRank_mono p hp le_top).trans h)

end Iso

theorem primeDataToKFact :
    ∀ (X : Type) [Group X] [Finite X] (p : ℕ) [Fact p.Prime], p ≠ 2 →
      SporCaseThreePrimeData X p →
      ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
        Nonempty (K ⧸ Subgroup.center K ≃* X) → IsPGroup p (Subgroup.center K) →
        IsCyclic (Subgroup.center K) → CaseThreeKFact p K := by
  intro X _ _ p _ _ hdata K _ _ hK ⟨e⟩ hZp hZc T
  have hp : p.Prime := Fact.out
  have : Group.IsPerfect K := ⟨hK.1⟩
  obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center e
  have hiso : Subgroup.center K = ⊥ → K ≃* X := fun hZ =>
    MulEquiv.ofBijective π ⟨(MonoidHom.ker_eq_bot_iff π).mp (hker.trans hZ), hπ⟩
  rcases hdata with h3 | ⟨h4, hpair, hkt⟩ | ⟨hG, hkt | hcw⟩
  · exact Or.inr (Or.inl
      (pRank_le_two_of_not_dvd_card hZp hZc (by rwa [Nat.card_congr e.toEquiv]) T))
  · have hZ := center_eq_bot_of_kernelTrivialAt hkt e hZp
    exact Or.inr (Or.inl ⟨pRank_sylow_le_two_of_mulEquiv hp (hiso hZ)
      (pRank_le_two_of_hasNoncommPair hp h4 hpair) T, Or.inl hZ⟩)
  · rcases weakCore_or_klingenAlt_of_mulEquiv
      (hiso (center_eq_bot_of_kernelTrivialAt hkt e hZp)) hG T with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · by_cases hZ : Subgroup.center K = ⊥
    · rcases weakCore_or_klingenAlt_of_mulEquiv (hiso hZ) hG T with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inl (hcw K π hπ hker ⟨hK.1⟩ hZ hZp hZc T)

theorem kFactsFromData : KFactsFromData := by
  intro hbr hdata hJ3 hM K _ _ hK s ⟨e⟩ p _ hp2 hZp hZc hJ
  obtain ⟨b⟩ := hbr s
  by_cases hsM : s = .M
  · subst hsM
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
    exact primeDataToKFact _ p hp2
      ((hM _ (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK)
        ⟨e.trans b.symm⟩).2 p hp2) K hK ⟨MulEquiv.refl _⟩ hZp hZc
  by_cases hsJ : s = .J3
  · subst hsJ
    obtain ⟨hcard, hJdata⟩ := hJ3
    have hfin : Finite (Blueprint.NativeSporadic.Carrier .J3) := Nat.finite_of_card_ne_zero hcard
    obtain ⟨hprime, hcover⟩ := @hJdata hfin
    by_cases hp3 : p = 3
    · subst hp3
      have hZ : Subgroup.center K ≠ ⊥ := fun hZ => hJ ⟨rfl, rfl, hZ⟩
      obtain ⟨π, hπ, hker⟩ := exists_surjective_ker_eq_center (e.trans b.symm)
      intro T
      exact Or.inl (hcover K π hπ hker ⟨hK.1⟩ hZ hZp hZc T)
    · exact primeDataToKFact _ p hp2 (hprime p hp2 hp3) K hK ⟨e.trans b.symm⟩ hZp hZc
  · obtain ⟨hcard, hX⟩ := hdata s hsJ hsM
    have : Finite (Blueprint.NativeSporadic.Carrier s) := Nat.finite_of_card_ne_zero hcard
    exact primeDataToKFact _ p hp2 (hX p hp2) K hK ⟨e.trans b.symm⟩ hZp hZc

end CFSG.AGLEmbedding
