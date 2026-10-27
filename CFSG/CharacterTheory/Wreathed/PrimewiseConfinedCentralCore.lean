module

public import CFSG.CharacterTheory.Wreathed.PrimewiseLayerFieldElimination
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreOrder
public import CFSG.CharacterTheory.Wreathed.PrimewiseConfinedCentralCoreSupport

public section

open scoped Classical Pointwise

namespace CFSG.Wreathed.PrimewiseConfinedCentralCore

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem original_primewise_coverage_and_confinement_give_central_cyclic_odd_core
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hcov : ∀ ell : ℕ, ell.Prime → ell ∣ Nat.card (centralizerOddCore n S e) →
      ∃ P : Sylow ell (centralizerOddCore n S e),
        (Subgroup.centralizer (((P : Subgroup (centralizerOddCore n S e)).map
            (centralizerOddCore n S e).subtype) : Set (involutionCentralizer n S e)) ⊓
          (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e)).map
            (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e) :
    let m : ℕ := 2 ^ n
    let q : ℕ := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let M := CFSG.layer (centralizerOddCoreQuotient n S e)
    let Y := M.comap π
    let H₀ := Y ⊓ Subgroup.centralizer (R : Set N)
    let J := (CFSG.perfectResidual H₀).map H₀.subtype
    let SN : Subgroup N := (centralizerSylow n hn S e : Subgroup N)
    J.Normal ∧ (∃ φ : J ≃* M, ∀ j : J, (φ j : centralizerOddCoreQuotient n S e) = π j) ∧
      ⁅J, R⁆ = ⊥ ∧ (∃ μ : J × R ≃* Y, ∀ z : J × R, (μ z : N) = z.1 * z.2) ∧
      IsCyclic R ∧ R ≤ Subgroup.center N ∧ (Nat.card R : ℤ) ∣ (q - ε) / m ∧
      (∀ y₁ : N, orderOf y₁ = 2 → y₁ ∉ Subgroup.center N → ∀ r ∈ R, y₁ * r = r * y₁) ∧
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
        (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
        (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma ≃* centralizerOddCoreQuotient n S e),
        ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) ∧
      (∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
        (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
        (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma ≃* centralizerOddCoreQuotient n S e),
        ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ →
          Nat.card Sigma = 1) ∧
      Nat.card N = Nat.card R * m * q * (q ^ 2 - 1) ∧
      (Nat.card G : ℤ) = Nat.card R * m * q ^ 3 * ((q : ℤ) ^ 2 - 1) * Qd ∧
      (N.index : ℤ) = q ^ 2 * Qd ∧
      ∃ JS : Subgroup N, (JS : Set N) = (J : Set N) * (SN : Set N) ∧
        (∃ μ : R × JS ≃* N, ∀ z : R × JS, (μ z : N) = z.1 * z.2) ∧
        ∃ φ : JS ≃* centralizerOddCoreQuotient n S e, ∀ k : JS, φ k = π k := by
  intro m q ε Qd N R π M Y H₀ J SN
  obtain ⟨-, hJnormal, -, hJM, hJR, hJRY, hYset, hne9, h9, hex, hall⟩ :=
    PrimewiseLayerFieldElimination.original_primewise_layer_coverage_eliminates_odd_field_factor
      hnonab n hn S e hfour p f hp hpodd hf hmodel hcov
  have : J.Normal := hJnormal
  have hE : J ⊓ R = ⊥ := by
    by_cases hq : p ^ f = 9
    · obtain ⟨-, hcard, -, hER⟩ := h9 hq
      exact ConfinedOddCore.lift_inter_oddCore_eq_bot_of_nine hnonab n hn S e hfour p f hp hpodd
        hf hmodel hq hconf J hJR hYset hER hcard
    · exact (hne9 hq).1
  obtain ⟨hRcyc, hRcent, hRdvd, hnoncentral, -, -, -, hNcard, hGcard, hidx, -, JS, hJSset, -,
      hμ, hφ⟩ :=
    ConfinedOddCore.confined_original_odd_core_is_central_cyclic_with_exact_order_formula hnonab
      n hn S e hfour p f hp hpodd hf hmodel J hJM hE hconf
  have hφJ : ∃ φ : J ≃* M, ∀ j : J, (φ j : centralizerOddCoreQuotient n S e) = π j := by
    have hmem : ∀ j : J, π j ∈ M := fun j => by
      show π j ∈ CFSG.layer (centralizerOddCoreQuotient n S e)
      rw [← hJM]
      exact Subgroup.mem_map_of_mem _ j.2
    let πJ : J →* M := (π.comp J.subtype).codRestrict M hmem
    have hinj : Function.Injective πJ := by
      rw [injective_iff_map_eq_one]
      intro j hj
      have h1 : (j : N) ∈ R := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hj)
      have h2 : (j : N) ∈ J ⊓ R := ⟨j.2, h1⟩
      rw [hE, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have hsurj : Function.Surjective πJ := by
      intro u
      have hu : (u : centralizerOddCoreQuotient n S e) ∈ J.map π := by
        rw [hJM]
        exact u.2
      obtain ⟨j, hj, hju⟩ := Subgroup.mem_map.mp hu
      exact ⟨⟨j, hj⟩, Subtype.ext hju⟩
    exact ⟨MulEquiv.ofBijective πJ ⟨hinj, hsurj⟩, fun j => rfl⟩
  exact ⟨hJnormal, hφJ, hJR, PrimewiseLayerFieldElimination.exists_prod_mulEquiv J R Y hJR hJRY hE,
    hRcyc, hRcent, hRdvd, hnoncentral, hex, hall, hNcard, hGcard, hidx, JS, hJSset, hμ, hφ⟩

end CFSG.Wreathed.PrimewiseConfinedCentralCore
