module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationToral

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal CFSG.Assembly.LowTwoRank

section RootDatum

variable {K : Type*} [Group K] {X : Type*} [Group X]

@[expose] def rankOneRoot (D : UniversalRootDatum K) (g : K) (γ : Fin D.rank → ℤ) : Subgroup K :=
  (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom

@[expose] def rankOneImage (D : UniversalRootDatum K) (ψ : K →* X) (g : K)
    (γ : Fin D.rank → ℤ) : Subgroup X :=
  (rankOneRoot D g γ).map ψ

theorem iSup_rankOneRoot_eq_top (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p e)
    (g : (modelUniv t n p e hp).K) :
    ⨆ γ ∈ (modelUniv t n p e hp).D.roots, rankOneRoot (modelUniv t n p e hp).D g γ = ⊤ := by
  obtain ⟨_, _, hct, _⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e hp hfund hadm
  have h : ⨆ γ ∈ (modelUniv t n p e hp).D.roots, (modelUniv t n p e hp).D.rootGroup γ = ⊤ :=
    hct.iSup_eq_top
  refine eq_top_iff.mpr ?_
  have hmap : (⨆ γ ∈ (modelUniv t n p e hp).D.roots,
      (modelUniv t n p e hp).D.rootGroup γ).map (MulAut.conj g).toMonoidHom = ⊤ := by
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [← hmap, Subgroup.map_iSup]
  refine iSup_le fun γ => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hγ => ?_
  exact le_iSup₂_of_le γ hγ (Subgroup.map_mono le_sup_left)

theorem iSup_rankOneImage_eq_range (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (ψ : (modelUniv t n p e hp).K →* X)
    (g : (modelUniv t n p e hp).K) :
    ⨆ γ ∈ (modelUniv t n p e hp).D.roots, rankOneImage (modelUniv t n p e hp).D ψ g γ =
      ψ.range := by
  rw [MonoidHom.range_eq_map, ← iSup_rankOneRoot_eq_top t n p e hp hfund hadm g,
    Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  rw [Subgroup.map_iSup]
  rfl

theorem divisible_eq_empty (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hadm : StatedLieAdmissible t n p e)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) :
    (modelUniv t n p e hp).D.divisible = ∅ := by
  have : Fact p.Prime := ⟨hp⟩
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · have hn : 3 ≤ n := by have := hadm.2.2; omega
    show (CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus n p e hp).D.divisible = ∅
    rw [CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn]
    ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)
  · ext i
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hi
    exact absurd hi (Set.notMem_empty i)

theorem isLongestRoot_of_mem_roots_simplyLaced (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    {γ : Fin (modelUniv t n p e hp).D.rank → ℤ} (hγ : γ ∈ (modelUniv t n p e hp).D.roots) :
    IsLongestRoot (modelUniv t n p e hp).D γ := by
  have hdiv := divisible_eq_empty t n p e hp hadm ht
  have hlong : ∀ k : Fin (modelUniv t n p e hp).D.rank,
      CFSG.ClassicalInvolution.ModelFacts.IsLongNode t n k.val := by
    intro k
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> trivial
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · have h : CFSG.ClassicalInvolution.ModelFacts.IsLongest
        (modelUniv t n p e hp).D.isFiniteType (modelUniv t n p e hp).D.divisible
        (Pi.single i 1) :=
      CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single t n p e hp hfund hadm i (hlong i)
    exact h.map_weylAction w
  · exfalso
    rw [hdiv] at hi
    exact Set.notMem_empty i hi

end RootDatum

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def componentHom (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card) : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K →* OddQuot a :=
  (layerQuotientHom hΩ.conjInvariant a).comp (D.hom j)

theorem rankOneImage_mem_memberImages (hΩ : InClass p f Ω) {a : G} (D : LocalLieSystemAt p f Ω a)
    (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (g : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K)
    {γ : Fin (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D γ) :
    rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D (componentHom hΩ D j) g γ ∈
      memberImages Ω a := by
  have hR : rankOneRoot (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D g γ ∈
      fundamentalSubgroups (D.tag j) (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D :=
    ⟨g, γ, Or.inl hγ, rfl⟩
  have hne : (centralizingMembers Ω {a}).Nonempty := by
    obtain ⟨R, -, ⟨_, ⟨K, hK, -, rfl⟩, -⟩⟩ := D.meets j
    exact ⟨K, hK⟩
  have hΦ : ConjInvariant
      (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) (centralizingLayer Ω {a}))) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {a} hne).conjInvariant
  have hmem := D.map_mem_of_single_class hΦ j hsingle hR
  have := map_layerQuotientHom_family (a := a) hΩ.conjInvariant
  rw [← this]
  refine ⟨_, hmem, ?_⟩
  exact Subgroup.map_map _ (layerQuotientHom hΩ.conjInvariant a) (D.hom j)

theorem rankOneImage_isInvolutionMember (hΩ : InClass p f Ω) (hq : 5 ≤ p ^ f) {a : G}
    (D : LocalLieSystemAt p f Ω a) (j : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (g : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K)
    {γ : Fin (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D γ) :
    IsInvolutionMember
      (rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
        (componentHom hΩ D j) g γ) := by
  obtain ⟨K, hK, hKeq⟩ := rankOneImage_mem_memberImages hΩ D j hsingle g hγ
  rw [← hKeq]
  exact isInvolutionMember_modOdd (InClass.isInvolutionMember hΩ hq K hK.1) hK.2

end Members

section Provider

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

theorem LayerGenerationLie.of_toralRoots (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        ∃ g : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K,
          (∀ γ ∈ (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.roots,
            IndexTwoCentralizes (modOdd a E)
              (rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
                (componentHom hΩ D j) g γ)) ∧
          ∀ γ ∈ (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.roots,
            ¬ IsInvolutionMember
              (rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
                (componentHom hΩ D j) g γ) →
            ∀ f ∈ modOdd a F₀, f ≠ 1 →
              (∀ r ∈ rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
                (componentHom hΩ D j) g γ, f * r = r * f) →
              rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
                (componentHom hΩ D j) g γ ≤ centralizerLayer f) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_indexTwoFamily hE2 ha ?_
  intro L hL hlie hjoin F₀ hF
  obtain ⟨D⟩ := hIH {a} hnc
  obtain ⟨D', hcomp, -⟩ := lieDecomposition_localSystem_comp hp2 h0 hA1 hq hΩ D
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · obtain ⟨j, hj⟩ := hcomp i
    have hQ : D'.Q i = (componentHom hΩ D j).range := hj.symm
    rw [hQ] at hF ⊢
    obtain ⟨g, hT, hS⟩ := htor D j F₀ hF
    refine ⟨{R | ∃ γ ∈ (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.roots,
      R = rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
        (componentHom hΩ D j) g γ}, ?_, ?_, ?_, ?_⟩
    · rw [← iSup_rankOneImage_eq_range (D.tag j) (D.rank j) p (D.exp j) Fact.out (D.isFundTag j)
        (D.admissible j) (componentHom hΩ D j) g]
      exact iSup₂_le fun γ hγ => le_iSup₂_of_le _ ⟨γ, hγ, rfl⟩ le_rfl
    · rintro _ ⟨γ, -, rfl⟩
      exact Subgroup.map_le_range _ _
    · rintro _ ⟨γ, hγ, rfl⟩
      exact hT γ hγ
    · rintro _ ⟨γ, hγ, rfl⟩ hnm f hf hf1 hfc
      exact hS γ hγ hnm f hf hf1 hfc
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

theorem LayerGenerationLie.of_toralRoots_simplyLaced (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hE2 : ∀ x ∈ E, x * x = 1) {a : G} (ha : a ∈ E)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    (htor : ∀ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card) (F₀ : Subgroup G),
      IsFaithfulFourGroupAt E a (componentHom hΩ D j).range F₀ →
        (D.tag j = .PSL ∨ D.tag j = .POmegaPlus ∨ D.tag j = .E6 ∨ D.tag j = .E7 ∨
          D.tag j = .E8) ∧
        ∃ g : (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K,
          ∀ γ ∈ (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D.roots,
            IndexTwoCentralizes (modOdd a E)
              (rankOneImage (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D
                (componentHom hΩ D j) g γ)) :
    LayerGenerationLie Ω E a := by
  refine LayerGenerationLie.of_toralRoots hp2 h0 hA1 hq hΩ hIH hE2 ha hnc ?_
  intro D j F₀ hF
  obtain ⟨hsl, g, hT⟩ := htor D j F₀ hF
  have hsingle : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass (D.tag j) (D.rank j) p (D.exp j)
      Fact.out (D.isFundTag j) (D.admissible j) (by rcases hsl with h | h | h | h | h <;> simp [h])
      (by rcases hsl with h | h | h | h | h <;> simp [h])
  refine ⟨g, hT, fun γ hγ hnm => absurd ?_ hnm⟩
  exact rankOneImage_isInvolutionMember hΩ hq D j hsingle g
    (isLongestRoot_of_mem_roots_simplyLaced (D.tag j) (D.rank j) p (D.exp j) Fact.out
      (D.isFundTag j) (D.admissible j) hsl hγ)

end Provider

end CFSG.ClassicalInvolution.Balance
