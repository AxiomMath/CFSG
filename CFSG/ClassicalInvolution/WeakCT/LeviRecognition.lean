module

public import CFSG.Timmesfeld.RankTwo.LeviEmbedding

public section

namespace CFSG.WeakCTLevi

open CFSG.LieType CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Timmesfeld

variable {K : Type} [Group K] {D : UniversalRootDatum K}

theorem exists_surjective_of_leviEmbeddings {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (E : ∀ i j, i ≤ j → LeviEmbedding D i j) {H : Type} [Group H]
    (φ : ∀ i j (h : i ≤ j), (E i j h).L →* H)
    (hcompat : ∀ i j (h : i ≤ j) k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D k k,
      ∀ g ∈ D.rootGroup γ,
        φ i j h ((E i j h).preimage g) = φ k k le_rfl ((E k k le_rfl).preimage g))
    (hgen : Subgroup.closure (⋃ k, Set.range (frameMap E φ (Pi.single k 1)) ∪
      Set.range (frameMap E φ (-Pi.single k 1))) = ⊤)
    (hnt : ∃ k, ∃ x, frameMap E φ (Pi.single k 1) x ≠ 1) :
    ∃ Ψ : K →* H, (∀ k (x : D.rootGroup (Pi.single k 1)), Ψ x = frameMap E φ _ x) ∧
      (∀ k (x : D.rootGroup (-Pi.single k 1)), Ψ x = frameMap E φ _ x) ∧
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple H ∧
      Subgroup.center H = (Subgroup.center K).map Ψ ∧
      LieModel (H ⧸ Subgroup.center H) t n p f := by
  have hpair : ∀ i j (h : i ≤ j), ExtendsToHom D.rootGroup (pairRoots D i j) (frameMap E φ) := by
    intro i j h
    refine extendsToHom_of_injective (E i j h).inj (φ i j h) fun γ hγ g => ?_
    have hg : (g : K) ∈ (E i j h).emb.range := (E i j h).le γ hγ g.2
    refine ⟨(E i j h).preimage g, (E i j h).emb_preimage hg, ?_⟩
    by_cases hs : ∃ k, γ ∈ pairRoots D k k
    · obtain ⟨k, hk⟩ := hs
      rw [frameMap_of_mem_self hk]
      have hki : k = i ∨ k = j := by
        by_contra hc
        push Not at hc
        apply RootSystem.ne_zero_of_mem_roots D.isFiniteType D.divisible hk.1
        funext l
        by_cases hl : l = k
        · subst hl; exact hγ.2 l hc.1 hc.2
        · exact hk.2 l hl hl
      exact (hcompat i j h k hki γ hk g g.2).symm
    · push Not at hs
      rcases lt_or_eq_of_le h with hlt | rfl
      · rw [frameMap_of_mem_pair hlt hγ hs]
      · exact absurd hγ (hs i)
  have hpair' : ∀ i j, ExtendsToHom D.rootGroup (pairRoots D i j) (frameMap E φ) := by
    intro i j
    rcases le_total i j with h | h
    · exact hpair i j h
    · rw [pairRoots_comm]; exact hpair j i h
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    exists_surjective_of_frame hCT hL (frameMap E φ)
      (fun i j _ _ _ _ _ => (hpair' i j).mono Set.inter_subset_right)
      (fun k => (hpair' k k).mono fun γ hγ => by
        rcases hγ with rfl | rfl
        exacts [(Levi.single_mem_pairRoots (Or.inl rfl)).1,
          (Levi.single_mem_pairRoots (Or.inl rfl)).2]) hgen hnt
  exact ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩

end CFSG.WeakCTLevi
