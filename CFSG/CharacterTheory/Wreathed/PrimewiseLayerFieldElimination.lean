module

public import CFSG.CharacterTheory.Wreathed.PrimewiseLayerFieldEliminationSupport
public import CFSG.CharacterTheory.Wreathed.NormalComponentLift

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.PrimewiseLayerFieldElimination


open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem original_primewise_layer_coverage_eliminates_odd_field_factor
    {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e),
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
            (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e)) :
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let M := CFSG.layer (centralizerOddCoreQuotient n S e)
    let Y := M.comap π
    let H₀ := Y ⊓ Subgroup.centralizer (R : Set N)
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let E := J ⊓ R
    Group.IsPerfect J ∧ J.Normal ∧ J ≤ Y ∧ J.map π = M ∧ ⁅J, R⁆ = ⊥ ∧ J ⊔ R = Y ∧
      (Y : Set N) = (J : Set N) * (R : Set N) ∧
      (p ^ f ≠ 9 → E = ⊥ ∧ ∃ μ : J × R ≃* Y, ∀ z : J × R, (μ z : N) = z.1 * z.2) ∧
      (p ^ f = 9 → IsCyclic E ∧ (Nat.card E = 1 ∨ Nat.card E = 3) ∧
        E.subgroupOf J ≤ Subgroup.center J ∧ E.subgroupOf R ≤ Subgroup.center R) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
        (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
        (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma ≃* centralizerOddCoreQuotient n S e),
        ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
      ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
        (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
        (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma ≃* centralizerOddCoreQuotient n S e),
        ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
          Nat.card Sigma = 1 := by
  intro N R π M Y H₀ J E
  obtain ⟨hJperf, hJnormal, hJY, hJM, hJR, hJRY, hYset, hEodd, hEJ, hER⟩ :=
    canonical_lift hnonab n hn S e hfour hcov
  have hbound := kernel_bound hnonab n hn S e hfour p f hp hpodd hf hmodel J hJperf hJM hEJ
  refine ⟨hJperf, hJnormal, hJY, hJM, hJR, hJRY, hYset, fun hne => ?_, fun h9 => ?_,
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel, ?_⟩
  · have hE := hbound.1 hne
    exact ⟨hE, exists_prod_mulEquiv J R Y hJR hJRY hE⟩
  · obtain ⟨hcyc, hcard⟩ := hbound.2 h9
    exact ⟨hcyc, hcard, hEJ, hER⟩
  · intro F _ _ Sigma b hSigma ρ Ψ hdata
    by_cases h9 : p ^ f = 9
    · exact sigma_card_eq_one_of_nine n hn S e p f hp h9 F Sigma b hSigma ρ Ψ hdata
    · let : J.Normal := hJnormal
      exact (NormalComponentLift.actual_normal_component_lift_eliminates_odd_field_factor hnonab
        n hn S e hfour p f hp hpodd hf hmodel J hJM (hbound.1 h9) F Sigma b hSigma ρ Ψ hdata).1

end CFSG.Wreathed.PrimewiseLayerFieldElimination
