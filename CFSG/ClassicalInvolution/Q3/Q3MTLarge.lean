module

public import CFSG.ClassicalInvolution.Q3.Q3MTKind
public import CFSG.ClassicalInvolution.Q3.Q3MTModel1
public import CFSG.ClassicalInvolution.Q3.Q3WAMBase
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTriple
public import CFSG.ClassicalInvolution.Q3.Q3MTDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3MT

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.MuTab
  CFSG.ClassicalInvolution.Uniform CFSG.LieType.RootSystem CFSG.LieType.Universal


section Triple

theorem exists_triple_of_threeOrth3 {t : StatedLieTag} {k : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k 3 1) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (h : ThreeOrth (modelUniv t k 3 1 Fact.out).D) :
    ∃ R₁ ∈ ModelFund 3 t k 1, ∃ R₂ ∈ ModelFund 3 t k 1, ∃ R₃ ∈ ModelFund 3 t k 1,
      R₁ ≠ R₂ ∧ R₁ ≠ R₃ ∧ R₂ ≠ R₃ ∧ Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  obtain ⟨γ, δ, ε, hγ, hδ, hε, h12, h13, h23⟩ := h
  obtain ⟨_, _, _, hext⟩ := ModelFacts.hasBruhatDatum t k 3 1 Fact.out (ih8_isFundTag_mf hfund) hadm
  have hmem : ∀ {γ : Fin (modelUniv t k 3 1 Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k 3 1 Fact.out).D γ →
      ((modelUniv t k 3 1 Fact.out).D.rootGroup γ ⊔
        (modelUniv t k 3 1 Fact.out).D.rootGroup (-γ)) ∈ ModelFund 3 t k 1 :=
    fun hγ => ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
  have hc : ∀ {γ δ : Fin (modelUniv t k 3 1 Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k 3 1 Fact.out).D γ →
      ModelFacts.IsLongestRoot (modelUniv t k 3 1 Fact.out).D δ →
      form (modelUniv t k 3 1 Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0 →
      Commutes ((modelUniv t k 3 1 Fact.out).D.rootGroup γ ⊔
          (modelUniv t k 3 1 Fact.out).D.rootGroup (-γ))
        ((modelUniv t k 3 1 Fact.out).D.rootGroup δ ⊔
          (modelUniv t k 3 1 Fact.out).D.rootGroup (-δ)) :=
    fun hγ hδ h => commutes_fund_of_orthogonal_of_longest _ hext hγ.1 hδ.1 hγ.2 h
  have hne : ∀ {γ δ : Fin (modelUniv t k 3 1 Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t k 3 1 Fact.out).D γ →
      ModelFacts.IsLongestRoot (modelUniv t k 3 1 Fact.out).D δ →
      form (modelUniv t k 3 1 Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0 →
      ((modelUniv t k 3 1 Fact.out).D.rootGroup γ ⊔
          (modelUniv t k 3 1 Fact.out).D.rootGroup (-γ)) ≠
        ((modelUniv t k 3 1 Fact.out).D.rootGroup δ ⊔
          (modelUniv t k 3 1 Fact.out).D.rootGroup (-δ)) :=
    fun hγ hδ h heq => Q3W.not_commutes_self_modelFund3 hfund hadm hG2 hD4 (hmem hγ)
      (fun a ha b hb => hc hγ hδ h a ha b (heq ▸ hb))
  exact ⟨_, hmem hγ, _, hmem hδ, _, hmem hε, hne hγ hδ h12, hne hγ hε h13, hne hδ hε h23,
    hc hγ hδ h12, hc hγ hε h13, hc hδ hε h23⟩

theorem shapeTriple_of_datum3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {t : StatedLieTag} {k e : ℕ} (M : Ih8Model 3 1 Ω t k e) (hne : Ω.Nonempty) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (h : ThreeOrth (modelUniv t k 3 e Fact.out).D) : ShapeTriple Ω := by
  obtain rfl : e = 1 := M.exp_eq_f hD4
  obtain ⟨R₁, h₁, R₂, h₂, R₃, h₃, h12, h13, h23, c12, c13, c23⟩ :=
    exists_triple_of_threeOrth3 M.isFundTag M.admissible hG2 hD4 h
  have hcls := M.fund_subset_cls hne hG2 hD4
  have key : ∀ {R S : Subgroup (modelUniv t k 3 1 Fact.out).K}, R ∈ ModelFund 3 t k 1 →
      S ∈ ModelFund 3 t k 1 → R ≠ S → R.map M.ψ ≠ S.map M.ψ := fun hR hS hRS h =>
    hRS (map_inj3 M hG2 hD4 (hcls hR) (hcls hS) h)
  refine ⟨![R₁.map M.ψ, R₂.map M.ψ, R₃.map M.ψ], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact M.map_mem (hcls h₁)
    · exact M.map_mem (hcls h₂)
    · exact M.map_mem (hcls h₃)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij (key h₁ h₂ h12)
    · exact absurd hij (key h₁ h₃ h13)
    · exact absurd hij.symm (key h₁ h₂ h12)
    · rfl
    · exact absurd hij (key h₂ h₃ h23)
    · exact absurd hij.symm (key h₁ h₃ h13)
    · exact absurd hij.symm (key h₂ h₃ h23)
    · rfl
  · intro i j hij a ha b hb
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact ih8_commutes_map M.ψ c12 a ha b hb
    · exact ih8_commutes_map M.ψ c13 a ha b hb
    · exact (ih8_commutes_map M.ψ c12).symm a ha b hb
    · exact absurd rfl hij
    · exact ih8_commutes_map M.ψ c23 a ha b hb
    · exact (ih8_commutes_map M.ψ c13).symm a ha b hb
    · exact (ih8_commutes_map M.ψ c23).symm a ha b hb
    · exact absurd rfl hij

end Triple

section Large

theorem largeShape3 (t : StatedLieTag) (k : ℕ) (hlarge : muKind false t k = .large) :
    SmallShape3 t k := by
  intro G _ _ _ Ω hΩ _ hne _ hL
  have hshape : KindShape Ω (muKind false t k) = ShapeTriple Ω := by rw [hlarge]; rfl
  rw [hshape]
  obtain ⟨e, ⟨M⟩⟩ := exists_datum_of_hasLieTypeU hΩ hne hL
  have hG2 : t ≠ .G2 := by
    rintro rfl
    obtain ⟨rfl, -⟩ := M.admissible.2.2
    simp [muKind] at hlarge
  have hD4 : t ≠ .trialityD4 := by
    rintro rfl
    obtain rfl : k = 0 := M.admissible.2.2
    simp [muKind] at hlarge
  have hef : e = 1 := M.exp_eq_f hD4
  subst hef
  have hnpsl : ¬ (t = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    exact M.admissible.2.2.2.2 (by simp)
  exact shapeTriple_of_datum3 M hne hG2 hD4
    (threeOrth_of_large (π := false) M.isFundTag M.admissible hnpsl hlarge)

end Large

end CFSG.ClassicalInvolution.Q3.Q3MT
