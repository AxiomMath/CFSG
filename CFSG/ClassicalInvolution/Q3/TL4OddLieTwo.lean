module

public import CFSG.ClassicalInvolution.Q3.TL4OddLieTwoLU
public import CFSG.ClassicalInvolution.Asc77.AscMuTabTriple

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

theorem muKind_eq_large {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (hnamed : ¬ LieKindNamed t m) (h5 : ¬ (t = .PSL ∧ m = 5)) (h5' : ¬ (t = .PSU ∧ m = 5))
    (h4 : ¬ (t = .POmegaPlus ∧ m = 4)) : MuTab.muKind false t m = .large := by
  simp only [LieKindNamed, not_or] at hnamed
  obtain ⟨c1, c4, c7, c2, c5, c8, c10, c11, c12⟩ := hnamed
  simp only [MuTab.muKind, c1, c2, h5, c4, c5, h5', c7, c8, h4, c10, c11, c12, ↓reduceIte]

section Cit3


open CFSG.LieType.Universal CFSG.LieType.Universal.Spin in
theorem threeOrth_pOmegaPlus_four
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 3 1) :
    MuTab.ThreeOrth (modelUniv .POmegaPlus 4 3 1 Fact.out).D := by
  have hl : ∀ i : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      ModelFacts.IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single i 1) :=
    fun i => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm i trivial
  have h : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) (by norm_num)⟩ :=
    ModelFacts.modelUniv_POmegaPlus (by norm_num)
  generalize modelUniv .POmegaPlus 4 3 1 Fact.out = L at h hl ⊢
  subst h
  refine MuTab.threeOrth_of_nodes _ (a := (⟨0, by norm_num⟩ : Fin 4))
    (b := (⟨2, by norm_num⟩ : Fin 4)) (c := (⟨3, by norm_num⟩ : Fin 4)) (hl _) (hl _) (hl _)
    ?_ ?_ ?_ <;>
  · show cartanD 4 _ _ = 0
    simp [cartanD]

open CFSG.LieType.RootSystem in
theorem exists_commuting_triple_of_threeOrth {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (hfund : IsFundTag t) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 3 1)
    (h : MuTab.ThreeOrth (modelUniv t m 3 1 Fact.out).D) :
    ∃ R₁ ∈ RouteD.ModelFund 3 t m 1, ∃ R₂ ∈ RouteD.ModelFund 3 t m 1,
      ∃ R₃ ∈ RouteD.ModelFund 3 t m 1, Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  obtain ⟨γ, δ, ε, hγ, hδ, hε, h12, h13, h23⟩ := h
  obtain ⟨_, _, _, hext⟩ :=
    ModelFacts.hasBruhatDatum t m 3 1 Fact.out (ih8_isFundTag_mf hfund) hadm
  have hmem : ∀ {γ : Fin (modelUniv t m 3 1 Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t m 3 1 Fact.out).D γ →
      ((modelUniv t m 3 1 Fact.out).D.rootGroup γ ⊔
        (modelUniv t m 3 1 Fact.out).D.rootGroup (-γ)) ∈ RouteD.ModelFund 3 t m 1 :=
    fun hγ => ⟨1, _, Or.inl hγ, (conjSub_one _).symm⟩
  have hc : ∀ {γ δ : Fin (modelUniv t m 3 1 Fact.out).D.rank → ℤ},
      ModelFacts.IsLongestRoot (modelUniv t m 3 1 Fact.out).D γ →
      ModelFacts.IsLongestRoot (modelUniv t m 3 1 Fact.out).D δ →
      form (modelUniv t m 3 1 Fact.out).D.isFiniteType (toRat γ) (toRat δ) = 0 →
      Commutes ((modelUniv t m 3 1 Fact.out).D.rootGroup γ ⊔
          (modelUniv t m 3 1 Fact.out).D.rootGroup (-γ))
        ((modelUniv t m 3 1 Fact.out).D.rootGroup δ ⊔
          (modelUniv t m 3 1 Fact.out).D.rootGroup (-δ)) :=
    fun hγ hδ h => RouteD.commutes_fund_of_orthogonal_of_longest _ hext hγ.1 hδ.1 hγ.2 h
  exact ⟨_, hmem hγ, _, hmem hδ, _, hmem hε, hc hγ hδ h12, hc hγ hε h13, hc hδ hε h23⟩

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twoNbrs_of_threeOrth {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m : ℕ}
    (hfund : IsFundTag t) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (h : MuTab.ThreeOrth (modelUniv t m 3 1 Fact.out).D) (hR : TypeRFam 3 Φ)
    (hgen : omegaGen Φ = ⊤) (ψ : (CompData.model t m).G →* X)
    (hker : ψ.ker ≤ Subgroup.center (CompData.model t m).G)
    (hfund' : ∀ L ∈ Φ, ∃ R ∈ (CompData.model t m).fund, IsSylow2In L (R.map ψ)) :
    ∃ L ∈ Φ, ∃ M ∈ omegaNbr Φ L, ∃ M' ∈ omegaNbr Φ L, M ≠ M' := by
  obtain ⟨A, hA, B, hB, C, hC, hAB, hAC, hBC⟩ := exists_commuting_triple_of_threeOrth hfund hadm h
  obtain ⟨L, hL⟩ := nonempty_of_lieLinkSection hgen hker
    (Q3W.not_commutes_self_modelFund3 hfund hadm hG2 hD4 hA)
  obtain ⟨R₀, hR₀, hLR⟩ := hfund' L hL
  exact ⟨L, hL, exists_two_nbrs_of_triple hR ψ
    (ModelFacts.fundamentalSingleClass t m 3 1 Nat.prime_three (ih8_isFundTag_mf hfund) hadm hG2
      hD4) hA hB hC hAB hAC hBC hL hR₀ hLR⟩

theorem lieKindTwoNbrs_proved : LieKindTwoNbrs := by
  intro X _ _ Φ t m hfund hadm hnamed hsec hshape
  obtain ⟨hR, -, hgen, -⟩ := hsec
  obtain ⟨ψ, -, hker, hfund'⟩ := hshape
  by_cases h5 : t = .PSL ∧ m = 5
  · obtain ⟨rfl, rfl⟩ := h5
    exact twoNbrs_psl5 hR hgen ψ hker hfund'
  by_cases h5' : t = .PSU ∧ m = 5
  · obtain ⟨rfl, rfl⟩ := h5'
    exact twoNbrs_psu5 hR hgen ψ hker hfund'
  by_cases h4 : t = .POmegaPlus ∧ m = 4
  · obtain ⟨rfl, rfl⟩ := h4
    exact twoNbrs_of_threeOrth hfund hadm (by decide) (by decide) (threeOrth_pOmegaPlus_four hadm)
      hR hgen ψ hker hfund'
  have hG2 : t ≠ .G2 := by
    rintro rfl
    obtain ⟨rfl, -⟩ := hadm.2.2
    exact hnamed (by simp [LieKindNamed])
  have hD4 : t ≠ .trialityD4 := by
    rintro rfl
    obtain rfl : m = 0 := hadm.2.2
    exact hnamed (by simp [LieKindNamed])
  have hnpsl : ¬ (t = .PSL ∧ m = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 (by simp)
  exact twoNbrs_of_threeOrth hfund hadm hG2 hD4
    (MuTab.threeOrth_of_large (π := false) hfund hadm hnpsl (muKind_eq_large hnamed h5 h5' h4))
    hR hgen ψ hker hfund'

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
