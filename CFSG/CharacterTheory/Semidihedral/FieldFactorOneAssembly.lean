module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneAssemblyInvariance
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps

public section

namespace CFSG.Semidihedral.FieldFactorOne

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def SimpleCentralizerLinearCharacterTrivialStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G))
      (t : G), t = (fS (r n) : G) ^ 2 ^ (n - 2) →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
      (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
      Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
      (∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 7 ≤ p ^ f →
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f →
    ∀ (θ : C t →* ℂˣ), (∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) →
      (∀ g ∈ Subgroup.normalizer
          ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G),
        ∀ c c' : C t,
          (c : G) ∈ Subgroup.centralizer
            ((Subgroup.closure {t, (fS (s n) : G)} : Subgroup G) : Set G) →
          (c' : G) = g * c * g⁻¹ → θ c' = θ c) →
      ∀ c : C t, θ c = 1

theorem exists_fieldAut_character_ne_one (F : Type) [Field F] [Finite F] {σ : F ≃+* F}
    (hσ : σ ≠ 1) : ∃ χ : (F ≃+* F) →* ℂˣ, χ σ ≠ 1 := by
  have := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic F
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  have hpos : Monoid.exponent (F ≃+* F) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero (Monoid.exponent (F ≃+* F) : ℂ) := ⟨by exact_mod_cast hpos⟩
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent (F ≃+* F)) :=
    IsSepClosed.hasEnoughRootsOfUnity ℂ _
  exact CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (F ≃+* F) ℂ hσ

theorem field_group_card_eq_one {G : Type} [Group G] (n p f : ℕ) (S : Sylow 2 G) (t : G)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (rho : Gamma t →* CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (data : ActualMatrixData t n p f F A rho)
    (htriv : ∀ θ : C t →* ℂˣ,
      (∀ c ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t), θ c = 1) →
      (∀ c : C t, (c : G) ∈ (S : Subgroup G) → θ c = 1) → ∀ c, θ c = 1) :
    Nat.card A = 1 := by
  set π : C t →* (F ≃+* F) :=
    (SemilinearOuterQuotient.fieldProjection F).comp (rho.comp (kappa t)) with hπ
  have hGammaA : (OddFieldLift.Gamma F A).map (SemilinearOuterQuotient.fieldProjection F) ≤ A := by
    rw [Subgroup.map_sup, sup_le_iff]
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ (SemilinearOuterQuotient.fieldProjection F).ker := by
        rw [SemilinearOuterQuotient.fieldProjection_ker]
        exact hx
      rw [MonoidHom.mem_ker.mp hx']
      exact A.one_mem
    · rintro _ ⟨x, ⟨σ, hσ, rfl⟩, rfl⟩
      rw [SemilinearOuterQuotient.fieldProjection_fieldLift]
      exact hσ
  have hmem : ∀ c, π c ∈ A := by
    intro c
    have h : rho (kappa t c) ∈ rho.range := MonoidHom.mem_range.mpr ⟨kappa t c, rfl⟩
    rw [data.full_image] at h
    exact hGammaA (Subgroup.mem_map_of_mem _ h)
  have hsurj : ∀ σ ∈ A, ∃ c, π c = σ := by
    intro σ hσ
    have h : SemilinearOuterQuotient.fieldLift F σ ∈ rho.range := by
      rw [data.full_image]
      exact Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hσ)
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp h
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (NZ t) γ
    refine ⟨c, ?_⟩
    change SemilinearOuterQuotient.fieldProjection F (rho (QuotientGroup.mk' (NZ t) c)) = σ
    rw [hγ, SemilinearOuterQuotient.fieldProjection_fieldLift]
  have hY : ∀ c ∈ ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t),
      π c = 1 := by
    intro c hc
    have h1 : rho (kappa t c) ∈ SemilinearOddExtensions.specialLayer F := by
      rw [← data.layer_image]
      exact Subgroup.mem_map_of_mem rho (show kappa t c ∈ CFSG.generalizedFitting (Gamma t) from hc)
    have h2 : rho (kappa t c) ∈ (SemilinearOuterQuotient.fieldProjection F).ker := by
      rw [SemilinearOuterQuotient.fieldProjection_ker, Subgroup.mem_subgroupOf]
      exact CFSG.ComponentClassification.CatalogueSchreierLinearTwo.coordinateG_le_D F
        (Subgroup.mem_subgroupOf.mp h1)
    exact h2
  have hS : ∀ c : C t, (c : G) ∈ (S : Subgroup G) → π c = 1 := by
    intro c hc
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨c, hc⟩
    have hck : c ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    have h1 : π c ^ 2 ^ k = 1 := by rw [← map_pow, hck, map_one]
    have h2 : π c ^ Nat.card A = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard A (hmem c))
    have hcop : Nat.Coprime (2 ^ k) (Nat.card A) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr data.field_group_odd)
    have h := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at h
  by_contra hA
  have hAne : A ≠ ⊥ := fun h => hA (Subgroup.card_eq_one.mpr h)
  obtain ⟨⟨σ, hσA⟩, hσ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have hσ1' : σ ≠ 1 := fun h => hσ1 (Subtype.ext h)
  obtain ⟨χ, hχ⟩ := exists_fieldAut_character_ne_one F hσ1'
  obtain ⟨c₀, hc₀⟩ := hsurj σ hσA
  apply hχ
  have h := htriv (χ.comp π) (fun c hc => by rw [MonoidHom.comp_apply, hY c hc, map_one])
    (fun c hc => by rw [MonoidHom.comp_apply, hS c hc, map_one]) c₀
  rwa [MonoidHom.comp_apply, hc₀] at h

theorem field_factor_one_of_trivial
    (h : SimpleCentralizerLinearCharacterTrivialStatement) :
    SimpleLayerFrontier.FieldFactorOneStatement := by
  intro G _ _ _ hGnonab hrec n hn S fS t ht _ hLnonab hcentral hnc p f hp hpodd hf hq hmodel hcov
  obtain ⟨-, ht2, -, -, -, -⟩ := Principal.supplied_t_s_facts hn fS ht
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := Principal.index_ne_two_of_isSimpleGroup hGnonab
  have hq7 : 7 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := hpodd.pow (n := f)
    omega
  obtain ⟨F, _, _, A, rho, data⟩ := actual_simple_layer_matrix_data n hn S fS hG t ht2 hLnonab
    hcentral hnc p f hp hpodd hf hmodel
  have hA : Nat.card A = 1 := field_group_card_eq_one n p f S t F A rho data fun θ hθY hθS =>
    h G hGnonab n hn S fS t ht hLnonab hcentral hnc p f hp hpodd hf hq7 hmodel θ hθS
      (invariant_of_trivial_on_layer G hGnonab hrec n hn S fS t ht hLnonab hcentral hnc p f hp
        hpodd hf hq hmodel hcov θ hθY hθS)
  obtain ⟨-, hJindex, -⟩ := actual_quotient_inputs n hn S fS hG t ht2
  have hLJ : CFSG.generalizedFitting (Gamma t) ≤ J t := simple_le_index_two _ _ hJindex hLnonab
  obtain ⟨eta, -, -, hcard⟩ := data.compatible_layer
  rw [hA] at hcard
  have hJL : J t ≤ CFSG.generalizedFitting (Gamma t) :=
    (Subgroup.comap_le_comap_of_surjective (barKappa_surjective t)).mp
      (Subgroup.relIndex_eq_one.mp hcard)
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.index_comap_of_surjective _ (barKappa_surjective t), le_antisymm hLJ hJL, hJindex]

end CFSG.Semidihedral.FieldFactorOne
