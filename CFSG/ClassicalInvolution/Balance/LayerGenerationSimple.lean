module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationRoots
import CFSG.ClassicalInvolution.LBalance.Main

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
  CFSG.LieType.CurtisTits

section RootDatum

variable {K : Type*} [Group K] {X : Type*} [Group X]

theorem iSup_rankOne_eq_top (D : UniversalRootDatum K) {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (CFSG.LieType.RootSystem.coxeterMatrix D.isFiniteType).toCoxeterSystem
      (CFSG.LieType.RootSystem.weylAction D.isFiniteType) D.roots D.rootGroup n H) :
    ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤ := by
  have h := iSup_leviAmalgam_eq_top
    (CFSG.LieType.RootSystem.isCTRootSystem D.isFiniteType D.divisible) hct
  rw [eq_top_iff, ← h]
  refine iSup_le fun J => ?_
  exact iSup₂_le fun j _ => le_iSup (fun i => rankOne D.rootGroup i) j

theorem single_mem_roots (D : UniversalRootDatum K) (i : Fin D.rank) :
    (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (CFSG.LieType.RootSystem.isCTRootSystem D.isFiniteType D.divisible).single_mem i

theorem iSup_rankOneRoot_simple_eq_top (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (g : (modelUniv t n p e hp).K) :
    ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOneRoot (modelUniv t n p e hp).D g (Pi.single i 1) = ⊤ := by
  obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e hp hfund hadm
  have h : ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOne (modelUniv t n p e hp).D.rootGroup i = ⊤ := iSup_rankOne_eq_top _ hct
  refine eq_top_iff.mpr ?_
  have hmap : (⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOne (modelUniv t n p e hp).D.rootGroup i).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [← hmap, Subgroup.map_iSup]
  exact le_rfl

theorem iSup_rankOneImage_simple_eq_range (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (ψ : (modelUniv t n p e hp).K →* X)
    (g : (modelUniv t n p e hp).K) :
    ⨆ i : Fin (modelUniv t n p e hp).D.rank,
      rankOneImage (modelUniv t n p e hp).D ψ g (Pi.single i 1) = ψ.range := by
  rw [MonoidHom.range_eq_map, ← iSup_rankOneRoot_simple_eq_top t n p e hp hfund hadm g,
    Subgroup.map_iSup]
  rfl

end RootDatum

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

section Criterion

variable {X : Type} [Group X] [Finite X]

theorem le_layers_of_indexTwoFamily_exists {L Ē F : Subgroup X} (hL : CFSG.IsComponent L)
    (hlie : IsOddLieComponent L) (hĒ2 : ∀ x ∈ Ē, x * x = 1) (hFĒ : F ≤ Ē) (hF4 : Nat.card F = 4)
    (hFN : F ≤ Subgroup.normalizer (L : Set X)) {𝓡 : Set (Subgroup X)}
    (hgen : L ≤ ⨆ R ∈ 𝓡, R) (hRL : ∀ R ∈ 𝓡, R ≤ L)
    (hidx : ∀ R ∈ 𝓡, IndexTwoCentralizes Ē R)
    (hlay : ∀ R ∈ 𝓡, ¬ IsInvolutionMember R → ∃ f ∈ F, f ≠ 1 ∧ R ≤ centralizerLayer f) :
    L ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), centralizerLayer f := by
  have hLopen := (CFSG.isComponent_iff_open L).mp hL
  have hB := involutionCentralizerB_of_isOddLieComponent hLopen.2.2 hlie
  refine hgen.trans (iSup₂_le fun R hR => ?_)
  by_cases hm : IsInvolutionMember R
  · obtain ⟨f, hfF, hf1, hfR⟩ := exists_ne_one_centralizes_of_indexTwo hĒ2 hFĒ hF4 (hidx R hR)
    have hRlayer : R ≤ centralizerLayer f :=
      hm.le_centralizerLayer l2PrimeBalance hLopen.2.1 (hRL R hR)
        (fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hfR r hr).symm)
        (hB f hf1 (hĒ2 f (hFĒ hfF)) (hFN hfF))
    exact le_iSup₂_of_le f hfF (le_iSup_of_le hf1 hRlayer)
  · obtain ⟨f, hfF, hf1, hRf⟩ := hlay R hR hm
    exact le_iSup₂_of_le f hfF (le_iSup_of_le hf1 hRf)

end Criterion

theorem LayerGenerationLie.of_indexTwoFamily_fourGroup (hE2 : ∀ x ∈ E, x * x = 1) {a : G}
    (ha : a ∈ E)
    (hfam : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → IsOddLieComponent L →
      L ≤ memberJoin Ω a → ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ →
        ∃ 𝓡 : Set (Subgroup (OddQuot a)), L ≤ ⨆ R ∈ 𝓡, R ∧ (∀ R ∈ 𝓡, R ≤ L) ∧
          (∀ R ∈ 𝓡, IndexTwoCentralizes (modOdd a F₀) R) ∧
          ∀ R ∈ 𝓡, ¬ IsInvolutionMember R →
            ∃ f ∈ modOdd a F₀, f ≠ 1 ∧ R ≤ centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  intro L hL hlie hjoin F₀ hF
  obtain ⟨𝓡, hgen, hRL, hidx, hlay⟩ := hfam L hL hlie hjoin F₀ hF
  obtain ⟨hF₀E, h4, hFn, -⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  exact OddCentralizerFree.of_le_layers
    (le_layers_of_indexTwoFamily_exists hL hlie (modOdd_sq_eq_one hE2 hF₀E) le_rfl
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) hFn hgen hRL hidx hlay)

noncomputable abbrev compModel {a : G} (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) :
    LieUniversal :=
  modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out

theorem LayerGenerationLie.of_toralRootFamily (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ (g : (compModel D j).K) (Γ : Set (Fin (compModel D j).D.rank → ℤ)),
          ⨆ γ ∈ Γ, rankOneImage (compModel D j).D (componentHom hΩ D j) g γ =
              (componentHom hΩ D j).range ∧
          (∀ γ ∈ Γ, IndexTwoCentralizes (modOdd a F₀)
            (rankOneImage (compModel D j).D (componentHom hΩ D j) g γ)) ∧
          ∀ γ ∈ Γ, ¬ IsInvolutionMember
              (rankOneImage (compModel D j).D (componentHom hΩ D j) g γ) →
            ∃ f ∈ modOdd a F₀, f ≠ 1 ∧
              rankOneImage (compModel D j).D (componentHom hΩ D j) g γ ≤ centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_indexTwoFamily_fourGroup hE2 ha ?_
  intro L hL hlie hjoin F₀ hF
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hcomp, -⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ D
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hcomp i
    have hQ : D'.Q i = (componentHom hΩ D j).range := hj.symm
    rw [hQ] at hF hL ⊢
    obtain ⟨g, Γ, hgen, hT, hS⟩ := htor D j F₀ hL hF
    refine ⟨{R | ∃ γ ∈ Γ, R = rankOneImage (compModel D j).D (componentHom hΩ D j) g γ},
      ?_, ?_, ?_, ?_⟩
    · rw [← hgen]
      exact iSup₂_le fun γ hγ => le_iSup₂_of_le _ ⟨γ, hγ, rfl⟩ le_rfl
    · rintro _ ⟨γ, -, rfl⟩
      exact Subgroup.map_le_range _ _
    · rintro _ ⟨γ, hγ, rfl⟩
      exact hT γ hγ
    · rintro _ ⟨γ, hγ, rfl⟩ hnm
      exact hS γ hγ hnm
  · exfalso
    have hcommL : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := fun x hx y hy => hcomm x hx y (hjoin hy)
    have hq2 := hL'.2.2
    have : Group.IsPerfect ↥L := ⟨hq2.1⟩
    have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq2.2
    have : Nontrivial ↥L :=
      (QuotientGroup.mk_surjective :
        Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ Subgroup.center ↥L)).nontrivial
    exact Group.IsPerfect.not_isMulCommutative ↥L
      ⟨⟨fun x y => Subtype.ext (hcommL x x.2 y y.2)⟩⟩

theorem LayerGenerationLie.of_toralSimpleRoots (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      CFSG.IsComponent (componentHom hΩ D j).range →
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ g : (compModel D j).K,
          (∀ i : Fin (compModel D j).D.rank, IndexTwoCentralizes (modOdd a F₀)
            (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1))) ∧
          ∀ i : Fin (compModel D j).D.rank, ¬ IsInvolutionMember
              (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1)) →
            ∃ f ∈ modOdd a F₀, f ≠ 1 ∧
              rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1) ≤
                centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralRootFamily hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hL hF
  obtain ⟨g, hT, hS⟩ := htor D j F₀ hL hF
  refine ⟨g, Set.range fun i : Fin (compModel D j).D.rank => (Pi.single i 1 : _ → ℤ), ?_, ?_, ?_⟩
  · rw [iSup_range]
    exact iSup_rankOneImage_simple_eq_range (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (D.isFundTag j) (D.admissible j) (componentHom hΩ D j) g
  · rintro _ ⟨i, rfl⟩
    exact hT i
  · rintro _ ⟨i, rfl⟩
    exact hS i

theorem LayerGenerationLie.of_toralSimpleRoots_simplyLaced (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        (D.tag j = .PSL ∨ D.tag j = .POmegaPlus ∨ D.tag j = .E6 ∨ D.tag j = .E7 ∨
          D.tag j = .E8) ∧
        ∃ g : (compModel D j).K, ∀ i : Fin (compModel D j).D.rank,
          IndexTwoCentralizes (modOdd a F₀)
            (rankOneImage (compModel D j).D (componentHom hΩ D j) g (Pi.single i 1))) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralSimpleRoots hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  rintro D j F₀ - hF
  obtain ⟨hsl, g, hT⟩ := htor D j F₀ hF
  have hsingle : FundamentalSingleClass (D.tag j) (compModel D j).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass (D.tag j) (D.rank j) p (D.exp j)
      Fact.out (D.isFundTag j) (D.admissible j) (by rcases hsl with h | h | h | h | h <;> simp [h])
      (by rcases hsl with h | h | h | h | h <;> simp [h])
  refine ⟨g, hT, fun i hnm => absurd ?_ hnm⟩
  exact rankOneImage_isInvolutionMember hΩ hq D j hsingle g
    (isLongestRoot_of_mem_roots_simplyLaced (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (D.isFundTag j) (D.admissible j) hsl (single_mem_roots _ i))

end Provider

end CFSG.ClassicalInvolution.Balance
