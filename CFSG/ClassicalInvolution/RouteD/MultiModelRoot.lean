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

theorem iSup_rankOne_eq_top (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) :
    ⨆ i, rankOne D.rootGroup i = ⊤ := by
  have h := iSup_leviAmalgam_eq_top (isCTRootSystem D.isFiniteType D.divisible) hct
  refine eq_top_iff.mpr ?_
  rw [← h]
  exact iSup_le fun J => iSup₂_le fun j _ => le_iSup (fun i => rankOne D.rootGroup i) j

theorem commFamilyConnected_of_rootCriterion [Finite K] (t : StatedLieTag)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hsc : FundamentalSingleClass t D) {α : Fin D.rank → ℤ}
    (hα : ModelFacts.IsLongestRoot D α)
    (hcrit : ∀ i : Fin D.rank, α = Pi.single i 1 ∨
      form D.isFiniteType (toRat α) (toRat (Pi.single i 1)) = 0 ∨
      ∃ ε, ModelFacts.IsLongestRoot D ε ∧ form D.isFiniteType (toRat α) (toRat ε) = 0 ∧
        form D.isFiniteType (toRat ε) (toRat (Pi.single i 1)) = 0) :
    CommFamilyConnected (fundamentalSubgroups t D) := by
  set R₀ : Subgroup K := D.rootGroup α ⊔ D.rootGroup (-α) with hR₀
  have hRF : ∀ γ, ModelFacts.IsLongestRoot D γ →
      (D.rootGroup γ ⊔ D.rootGroup (-γ)) ∈ fundamentalSubgroups t D := fun γ hγ =>
    ⟨1, γ, Or.inl hγ, (conjSub_one _).symm⟩
  have hF : ∀ A ∈ fundamentalSubgroups t D, ∀ g : K, conjSub g A ∈ fundamentalSubgroups t D := by
    rintro A ⟨g₀, γ, hγ, rfl⟩ g
    exact ⟨g * g₀, γ, hγ, (conjSub_mul g g₀ _).symm⟩
  have hX : Subgroup.closure {x : K | ∃ i, x ∈ rankOne D.rootGroup i} = ⊤ := by
    rw [eq_top_iff, ← iSup_rankOne_eq_top hct]
    exact iSup_le fun i x hx => Subgroup.subset_closure ⟨i, hx⟩
  refine commFamilyConnected_of_stable hF hsc hX (R₀ := R₀) (hRF α hα) ?_
  rintro x ⟨i, hx⟩
  have hmaxα : ∀ ε ∈ D.roots, ModelFacts.lenSq D.isFiniteType ε ≤
      ModelFacts.lenSq D.isFiniteType α := hα.2
  rcases hcrit i with hi | hi | ⟨ε, hε, h1, h2⟩
  · left
    refine conjSub_eq_self_of_mem ?_
    have hx' : x ∈ D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) := hx
    rw [← hi] at hx'
    exact hx'
  · left
    have hc : Commutes R₀ (rankOne D.rootGroup i) :=
      commutes_fund_of_orthogonal_of_longest D hext hα.1 (single_mem_roots D i) hmaxα hi
    exact conjSub_eq_of_mem_of_commutes hx hc.symm
  · right
    refine ⟨D.rootGroup ε ⊔ D.rootGroup (-ε), hRF ε hε, ?_, ?_⟩
    · exact commutes_fund_of_orthogonal_of_longest D hext hα.1 hε.1 hmaxα h1
    · have hc : Commutes (D.rootGroup ε ⊔ D.rootGroup (-ε)) (rankOne D.rootGroup i) :=
        commutes_fund_of_orthogonal_of_longest D hext hε.1 (single_mem_roots D i) hε.2 h2
      exact conjSub_eq_of_mem_of_commutes hx hc.symm

theorem form_single_eq_zero_of_cartan (D : UniversalRootDatum K) {k i : Fin D.rank}
    (h : D.cartan k i = 0) :
    form D.isFiniteType (toRat (Pi.single k 1)) (toRat (Pi.single i 1)) = 0 := by
  rw [toRat_single, toRat_single, form_single_left]
  simp [Pi.single_apply, h]

end Abstract

section Model

variable {p : ℕ} [Fact p.Prime]

theorem commFamilyConnected_modelFund_of_criterion {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hex : ∃ α : Fin (modelUniv t n p e Fact.out).D.rank → ℤ,
      ModelFacts.IsLongestRoot (modelUniv t n p e Fact.out).D α ∧
      ∀ i : Fin (modelUniv t n p e Fact.out).D.rank, α = Pi.single i 1 ∨
        form (modelUniv t n p e Fact.out).D.isFiniteType (toRat α) (toRat (Pi.single i 1)) = 0 ∨
        ∃ ε, ModelFacts.IsLongestRoot (modelUniv t n p e Fact.out).D ε ∧
          form (modelUniv t n p e Fact.out).D.isFiniteType (toRat α) (toRat ε) = 0 ∧
          form (modelUniv t n p e Fact.out).D.isFiniteType (toRat ε) (toRat (Pi.single i 1)) = 0) :
    CommFamilyConnected (ModelFund p t n e) := by
  obtain ⟨α, hα, hcrit⟩ := hex
  obtain ⟨nn, HH, hct, hext⟩ := ModelFacts.hasBruhatDatum t n p e Fact.out hfund hadm
  have : Finite (modelUniv t n p e Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out hfund hadm
  have hsc := ModelFacts.fundamentalSingleClass t n p e Fact.out hfund hadm hG2 hD4
  exact commFamilyConnected_of_rootCriterion t hct hext hsc hα hcrit

theorem commFamilyConnected_modelFund_of_nodes {t : StatedLieTag} {n e : ℕ} (hp2 : p ≠ 2)
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hnodes : ∃ ν : Fin (modelUniv t n p e Fact.out).D.rank, ModelFacts.IsLongNode t n ν.val ∧
      ∀ i : Fin (modelUniv t n p e Fact.out).D.rank, i = ν ∨
        (modelUniv t n p e Fact.out).D.cartan ν i = 0 ∨
        ∃ k : Fin (modelUniv t n p e Fact.out).D.rank, ModelFacts.IsLongNode t n k.val ∧
          (modelUniv t n p e Fact.out).D.cartan ν k = 0 ∧
          (modelUniv t n p e Fact.out).D.cartan k i = 0) :
    CommFamilyConnected (ModelFund p t n e) := by
  obtain ⟨ν, hν, hcrit⟩ := hnodes
  refine commFamilyConnected_modelFund_of_criterion hp2 hfund hadm hG2 hD4
    ⟨Pi.single ν 1, ModelFacts.isLongestRoot_single t n p e Fact.out hfund hadm ν hν, fun i => ?_⟩
  rcases hcrit i with rfl | h | ⟨k, hk, h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl (form_single_eq_zero_of_cartan _ h))
  · exact Or.inr (Or.inr ⟨Pi.single k 1,
      ModelFacts.isLongestRoot_single t n p e Fact.out hfund hadm k hk,
      form_single_eq_zero_of_cartan _ h1, form_single_eq_zero_of_cartan _ h2⟩)

end Model

end CFSG.ClassicalInvolution.RouteD
