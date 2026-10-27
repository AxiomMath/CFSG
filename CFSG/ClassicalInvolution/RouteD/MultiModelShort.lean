module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Abstract

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commutes_fund_rootGroup_of_orthogonal_of_longest (hext : SteinbergExtras D n H)
    {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hmax : ∀ ε ∈ D.roots, ModelFacts.lenSq D.isFiniteType ε ≤ ModelFacts.lenSq D.isFiniteType γ)
    (horth : form D.isFiniteType (toRat γ) (toRat δ) = 0) :
    Commutes (D.rootGroup γ ⊔ D.rootGroup (-γ)) (D.rootGroup δ) := by
  have hγ' : -γ ∈ D.roots := OfCartan.neg_mem_roots D.isFiniteType hγ
  have hmax' : ∀ ε ∈ D.roots, ModelFacts.lenSq D.isFiniteType ε ≤
      ModelFacts.lenSq D.isFiniteType (-γ) := by
    intro ε hε
    rw [ModelFacts.lenSq_neg]
    exact hmax ε hε
  have o1 : form D.isFiniteType (toRat (-γ)) (toRat δ) = 0 := by simp [horth]
  rw [commutes_sup_left]
  exact ⟨fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ hδ hmax horth x hx y hy,
    fun x hx y hy => commute_rootGroup_of_orthogonal_of_longest D hext hγ' hδ hmax' o1 x hx y hy⟩

theorem commFamilyConnected_of_shortCriterion [Finite K] (t : StatedLieTag)
    (hext : SteinbergExtras D n H) (hsc : FundamentalSingleClass t D) {α : Fin D.rank → ℤ}
    (hα : ModelFacts.IsLongestRoot D α) {Ψ : Set (Fin D.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, γ ∈ D.roots)
    (hgen : (⨆ γ ∈ Ψ, D.rootGroup γ) = ⊤)
    (hcrit : ∀ γ ∈ Ψ, γ = α ∨ γ = -α ∨ form D.isFiniteType (toRat α) (toRat γ) = 0 ∨
      ∃ ε, ModelFacts.IsLongestRoot D ε ∧ form D.isFiniteType (toRat α) (toRat ε) = 0 ∧
        form D.isFiniteType (toRat ε) (toRat γ) = 0) :
    CommFamilyConnected (fundamentalSubgroups t D) := by
  set R₀ : Subgroup K := D.rootGroup α ⊔ D.rootGroup (-α) with hR₀
  have hRF : ∀ γ, ModelFacts.IsLongestRoot D γ →
      (D.rootGroup γ ⊔ D.rootGroup (-γ)) ∈ fundamentalSubgroups t D := fun γ hγ =>
    ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩
  have hF : ∀ A ∈ fundamentalSubgroups t D, ∀ g : K, conjSub g A ∈ fundamentalSubgroups t D := by
    rintro A ⟨g₀, γ, hγ, rfl⟩ g
    exact ⟨g * g₀, γ, hγ, (conjSub_mul g g₀ _).symm⟩
  have hX : Subgroup.closure {x : K | ∃ γ ∈ Ψ, x ∈ D.rootGroup γ} = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact iSup₂_le fun γ hγ x hx => Subgroup.subset_closure ⟨γ, hγ, hx⟩
  refine commFamilyConnected_of_stable hF hsc hX (R₀ := R₀) (hRF α hα) ?_
  rintro x ⟨γ, hγΨ, hx⟩
  have hmaxα : ∀ ε ∈ D.roots, ModelFacts.lenSq D.isFiniteType ε ≤
      ModelFacts.lenSq D.isFiniteType α := hα.2
  rcases hcrit γ hγΨ with h | h | h | ⟨ε, hε, h1, h2⟩
  · left
    subst h
    exact conjSub_eq_self_of_mem (Subgroup.mem_sup_left hx)
  · left
    subst h
    exact conjSub_eq_self_of_mem (Subgroup.mem_sup_right hx)
  · left
    have hc : Commutes R₀ (D.rootGroup γ) :=
      commutes_fund_rootGroup_of_orthogonal_of_longest hext hα.1 (hΨ γ hγΨ) hmaxα h
    exact conjSub_eq_of_mem_of_commutes hx hc.symm
  · right
    refine ⟨D.rootGroup ε ⊔ D.rootGroup (-ε), hRF ε hε, ?_, ?_⟩
    · exact commutes_fund_of_orthogonal_of_longest D hext hα.1 hε.1 hmaxα h1
    · have hc : Commutes (D.rootGroup ε ⊔ D.rootGroup (-ε)) (D.rootGroup γ) :=
        commutes_fund_rootGroup_of_orthogonal_of_longest hext hε.1 (hΨ γ hγΨ) hε.2 h2
      exact conjSub_eq_of_mem_of_commutes hx hc.symm

end Abstract

section Model

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_modelFund_of_short {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hex : ∃ (α : Fin (modelUniv t n p e Fact.out).D.rank → ℤ)
      (Ψ : Set (Fin (modelUniv t n p e Fact.out).D.rank → ℤ)),
      ModelFacts.IsLongestRoot (modelUniv t n p e Fact.out).D α ∧
      (∀ γ ∈ Ψ, γ ∈ (modelUniv t n p e Fact.out).D.roots) ∧
      (⨆ γ ∈ Ψ, (modelUniv t n p e Fact.out).D.rootGroup γ) = ⊤ ∧
      ∀ γ ∈ Ψ, γ = α ∨ γ = -α ∨
        form (modelUniv t n p e Fact.out).D.isFiniteType (toRat α) (toRat γ) = 0 ∨
        ∃ ε, ModelFacts.IsLongestRoot (modelUniv t n p e Fact.out).D ε ∧
          form (modelUniv t n p e Fact.out).D.isFiniteType (toRat α) (toRat ε) = 0 ∧
          form (modelUniv t n p e Fact.out).D.isFiniteType (toRat ε) (toRat γ) = 0) :
    CommFamilyConnected (ModelFund p t n e) := by
  obtain ⟨α, Ψ, hα, hΨ, hgen, hcrit⟩ := hex
  obtain ⟨nn, HH, -, hext⟩ := ModelFacts.hasBruhatDatum t n p e Fact.out hfund hadm
  have : Finite (modelUniv t n p e Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out hfund hadm
  have hsc := ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm hG2 hD4
  exact commFamilyConnected_of_shortCriterion t hext hsc hα hΨ hgen hcrit

end Model

end CFSG.ClassicalInvolution.RouteD
