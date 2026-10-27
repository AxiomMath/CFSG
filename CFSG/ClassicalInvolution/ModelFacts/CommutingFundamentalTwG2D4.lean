module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairG2
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Tags

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
open CFSG.LieType.Steinberg.TwistedD4
open scoped MatrixGroups

section Central

variable {K : Type*} [Group K] {F : Type*} [Field F]

theorem fundCentral_sq_of_equiv_sl2 {L : Subgroup K} (e : L ≃* SL(2, F)) {c : K} (hc : c ∈ L)
    (hcc : ∀ r ∈ L, c * r = r * c) : c * c = 1 := by
  have hz : e ⟨c, hc⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨y, rfl⟩ := e.surjective B
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hcc y y.2).symm)
  have hsq : e ⟨c, hc⟩ * e ⟨c, hc⟩ = 1 := by
    rcases (mem_center_sl2_iff _).1 hz with h | h <;> rw [h]
    · simp
    · simp
  have : (⟨c, hc⟩ : L) * ⟨c, hc⟩ = 1 := e.injective (by rw [map_mul, hsq, map_one])
  exact congrArg Subtype.val this

end Central

section Nodes

theorem fundCentral_sq_of_all_nodes (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hdiv : (modelUniv t n p e hp.out).D.divisible = ∅)
    (hnode : ∀ i : Fin (modelUniv t n p e hp.out).D.rank,
      ∀ c ∈ rankOne (modelUniv t n p e hp.out).D.rootGroup i,
        (∀ r ∈ rankOne (modelUniv t n p e hp.out).D.rootGroup i, c * r = r * c) →
          c * c = 1) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, ∀ c ∈ R,
      (∀ r ∈ R, c * r = r * c) → c * c = 1 := by
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum t n p e hp.out hfund hadm
  intro R hR c hcR hcc
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨w, i, rfl⟩ : ∃ (w : (CFSG.LieType.RootSystem.coxeterMatrix
      (modelUniv t n p e hp.out).D.isFiniteType).Group)
      (i : Fin (modelUniv t n p e hp.out).D.rank),
      γ = CFSG.LieType.RootSystem.weylAction
        (modelUniv t n p e hp.out).D.isFiniteType w (Pi.single i 1) := by
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · exact ⟨w, i, rfl⟩
    · rw [hdiv] at hi
      exact absurd hi (Set.notMem_empty i)
  obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
  have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
  rw [← h1, CFSG.LieType.Chevalley.map_conj_map_conj] at hcR hcc
  obtain ⟨c₀, hc₀, rfl⟩ := hcR
  have hc₀c : ∀ r ∈ rankOne (modelUniv t n p e hp.out).D.rootGroup i,
      c₀ * r = r * c₀ := by
    intro r hr
    have h := hcc _ ⟨r, hr, rfl⟩
    have h' : (g * g') * (c₀ * r) * (g * g')⁻¹ = (g * g') * (r * c₀) * (g * g')⁻¹ := by
      calc (g * g') * (c₀ * r) * (g * g')⁻¹
          = ((g * g') * c₀ * (g * g')⁻¹) * ((g * g') * r * (g * g')⁻¹) := by group
        _ = ((g * g') * r * (g * g')⁻¹) * ((g * g') * c₀ * (g * g')⁻¹) := h
        _ = (g * g') * (r * c₀) * (g * g')⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hsq := hnode i c₀ hc₀ hc₀c
  show (g * g') * c₀ * (g * g')⁻¹ * ((g * g') * c₀ * (g * g')⁻¹) = 1
  calc (g * g') * c₀ * (g * g')⁻¹ * ((g * g') * c₀ * (g * g')⁻¹)
      = (g * g') * (c₀ * c₀) * (g * g')⁻¹ := by group
    _ = 1 := by rw [hsq]; group

end Nodes

section G2

theorem fundCentral_sq_G2 (n p e : ℕ) [hp : Fact p.Prime] (hadm : StatedLieAdmissible .G2 n p e) :
    ∀ R ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p e hp.out).D, ∀ c ∈ R,
      (∀ r ∈ R, c * r = r * c) → c * c = 1 := by
  refine fundCentral_sq_of_all_nodes .G2 n p e trivial hadm rfl ?_
  intro l c hc hcc
  obtain ⟨e'⟩ := g2_rankOne_equiv (K := GaloisField p e) l
  exact fundCentral_sq_of_equiv_sl2 e' hc hcc

end G2

section D4

theorem fundCentral_sq_trialityD4 (n p e : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible .trialityD4 n p e) :
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D, ∀ c ∈ R,
      (∀ r ∈ R, c * r = r * c) → c * c = 1 := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  refine fundCentral_sq_of_all_nodes .trialityD4 n p e trivial hadm rfl ?_
  intro k c hc hcc
  match k with
  | ⟨0, _⟩ =>
    exact fundCentral_sq_of_equiv_sl2
      ((MulEquiv.subgroupCongr (rankOne_long_eq_range hσ)).trans
        (MonoidHom.ofInjective (slLong_injective hσ)).symm) hc hcc
  | ⟨1, _⟩ =>
    exact fundCentral_sq_of_equiv_sl2
      ((MulEquiv.subgroupCongr (rankOne_short_eq_range hσ)).trans
        (MonoidHom.ofInjective (slShort_injective hσ)).symm) hc hcc

end D4

section Main

variable {p : ℕ} [hp : Fact p.Prime] {n e : ℕ}

theorem commutingGeneration_of_degenerate_pair {X : Type*} [Group X] {𝓕 : Set (Subgroup X)}
    {c₁ c₂ : X}
    (h : c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1) (hall : (⊤ : Subgroup X) ≤ ⨆ R ∈ 𝓕, R) :
    (⊤ : Subgroup X) ≤ ⨆ R ∈ 𝓕,
      ⨆ (_ : R ≤ Subgroup.centralizer ({c₁} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₂} : Set X) ∨
        R ≤ Subgroup.centralizer ({c₁ * c₂} : Set X)), R := by
  refine hall.trans (iSup₂_le fun R hR => le_iSup₂_of_le R hR (le_iSup_of_le ?_ le_rfl))
  have h1 : ∀ x : X, x = 1 → R ≤ Subgroup.centralizer ({x} : Set X) := fun x hx r _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (by simp [hx])
  rcases h with h | h | h
  · exact Or.inl (h1 _ h)
  · exact Or.inr (Or.inl (h1 _ h))
  · exact Or.inr (Or.inr (h1 _ h))

theorem iSup_fundamentalSubgroups_eq_top_of_all_roots (t : StatedLieTag)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hall : ∀ γ ∈ (Generic.modelUniv t n p e hp.out).D.roots,
      ∀ g, CFSG.ClassicalInvolution.Balance.rankOneRoot (Generic.modelUniv t n p e hp.out).D g γ ∈
        Generic.fundamentalSubgroups t (Generic.modelUniv t n p e hp.out).D) :
    (⊤ : Subgroup (Generic.modelUniv t n p e hp.out).K) ≤
      ⨆ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e hp.out).D, R := by
  have h := CFSG.ClassicalInvolution.Balance.iSup_rankOneRoot_simple_eq_top t n p e hp.out
    hfund hadm 1
  refine (le_of_eq h.symm).trans (iSup_le fun i => le_iSup₂_of_le _ (hall _
    (CFSG.ClassicalInvolution.Balance.single_mem_roots _ i) 1) le_rfl)

theorem commutingFundamentalGeneration_g2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .G2 n p e) : CommutingFundamentalGeneration p .G2 n e := by
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ _ hx₂₁
  obtain ⟨hodd, -⟩ := card_galoisField_facts (f := e) hp2 hq
  have hperf := CFSG.ClassicalInvolution.Balance.Bootstrap.fundamentalSubgroups_commutator_eq
    (t := .G2) (n := n) (p := p) (e := e) hp2 trivial hadm (by omega)
  have hdeg : c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1 := by
    by_cases h1 : c₁ = 1
    · exact Or.inl h1
    by_cases h2 : c₂ = 1
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have hsq₁ : c₁ * c₁ = 1 := by
      have key := fundCentral_sq_G2 n p e hadm
      exact key R₁ hR₁ c₁ hc₁ hz₁
    rcases CFSG.ClassicalInvolution.Balance.Bootstrap.g2_eq_one_or_eq_of_central_in_perfect
      (K := GaloisField p e) hodd hsq₁ h1 hx₂₁ (hperf R₂ hR₂) hc₂ hz₂ with h | h
    · exact absurd h h2
    · rw [h]
      exact hsq₁
  refine commutingGeneration_of_degenerate_pair hdeg ?_
  exact iSup_fundamentalSubgroups_eq_top_of_all_roots (n := n) (p := p) (e := e) .G2 trivial hadm
    fun γ hγ g => ⟨g, γ, Or.inr (Or.inl ⟨rfl, hγ⟩), rfl⟩

theorem commutingFundamentalGeneration_trialityD4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .trialityD4 n p e) :
    CommutingFundamentalGeneration p .trialityD4 n e := by
  intro R₁ hR₁ R₂ hR₂ c₁ hc₁ c₂ hc₂ hz₁ hz₂ _ hx₂₁
  have he : 1 ≤ e := hadm.2.1
  have hperf := CFSG.ClassicalInvolution.Balance.Bootstrap.fundamentalSubgroups_commutator_eq
    (t := .trialityD4) (n := n) (p := p) (e := e) hp2 trivial hadm (by omega)
  have hdeg : c₁ = 1 ∨ c₂ = 1 ∨ c₁ * c₂ = 1 := by
    by_cases h1 : c₁ = 1
    · exact Or.inl h1
    by_cases h2 : c₂ = 1
    · exact Or.inr (Or.inl h2)
    refine Or.inr (Or.inr ?_)
    have hsq₁ : c₁ * c₁ = 1 := by
      have key := fundCentral_sq_trialityD4 n p e hadm
      exact key R₁ hR₁ c₁ hc₁ hz₁
    have h := trialityD4_eq_of_central_in_perfect p e hp2 he (hperf R₂ hR₂) hsq₁ h1 h2 hc₂ hz₂
      hx₂₁
    rw [h]
    exact hsq₁
  refine commutingGeneration_of_degenerate_pair hdeg ?_
  exact iSup_fundamentalSubgroups_eq_top_of_all_roots (n := n) (p := p) (e := e) .trialityD4 trivial
    hadm fun γ hγ g => ⟨g, γ, Or.inr (Or.inr ⟨rfl, hγ⟩), rfl⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts
