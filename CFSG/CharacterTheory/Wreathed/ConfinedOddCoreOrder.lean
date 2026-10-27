module

public import CFSG.CharacterTheory.Wreathed.ConfinedOddCore
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreOrderSupport
public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrder

public section

open scoped Classical Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.TorusSplitting

theorem confined_original_odd_core_is_central_cyclic_with_exact_order_formula
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e) :
    let m := 2 ^ n
    let q := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let s : G := wreathModelHom S e (Original.s m)
    let t : G := wreathModelHom S e (Original.t m)
    let y : G := wreathModelHom S e (Original.x2 m)
    let w : G := wreathModelHom S e (Original.z m)
    let SN : Subgroup N := (centralizerSylow n hn S e : Subgroup N)
    IsCyclic R ∧ R ≤ Subgroup.center N ∧ (Nat.card R : ℤ) ∣ (q - ε) / m ∧
      (∀ y₁ : N, orderOf y₁ = 2 → y₁ ∉ Subgroup.center N → ∀ r ∈ R, y₁ * r = r * y₁) ∧
      (∀ y₁ : N, orderOf y₁ = 2 → y₁ ∉ Subgroup.center N →
        (OddNormalQuotientInvolutions.kernelCentralizer R y₁).index = 1) ∧
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
      J.map N.subtype ⊓ (S : Subgroup G) = Subgroup.closure {s * t⁻¹, y * w} ∧
      ∃ JS : Subgroup N, (JS : Set N) = (J : Set N) * (SN : Set N) ∧ JS ⊓ R = ⊥ ∧
        (∃ μ : R × JS ≃* N, ∀ z : R × JS, (μ z : N) = z.1 * z.2) ∧
        ∃ φ : JS ≃* centralizerOddCoreQuotient n S e, ∀ k : JS, φ k = π k := by
  intro m q ε Qd N R π s t y w SN
  obtain ⟨hA₀mem, W₀, hW₀mem, hsup, hW₀A, hW₀Ac, -, hW₀c, -, hA₀c, hA₀dvd, B, -, hBR, -, hBchar,
      -, -, hBsup, -, -, hinvB, -⟩ :=
    confined_original_odd_core_has_cyclic_fixed_factor_and_abelian_inverted_kernel hnonab n hn S e
      hfour p f hp hpodd hf hmodel J hJM hJR hconf
  have hall : ∀ (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ → Nat.card Sigma = 1 :=
    fun F _ _ Sigma b hSigma ρ Ψ hdata =>
      (NormalComponentLift.actual_normal_component_lift_eliminates_odd_field_factor hnonab n hn S
        e hfour p f hp hpodd hf hmodel J hJM hJR F Sigma b hSigma ρ Ψ hdata).1
  have hex := exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel
  obtain ⟨F, hF, hFfin, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hex
  let : Field F := hF
  let : Finite F := hFfin
  obtain ⟨hd1, -, -, -, -, -, -, -, -, hwA, -⟩ :=
    NormalComponentLift.actual_normal_component_lift_eliminates_odd_field_factor hnonab n hn S e
      hfour p f hp hpodd hf hmodel J hJM hJR F Sigma b hSigma ρ Ψ hdata
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (centralizerOddCoreQuotient n S e) := Fintype.ofFinite _
  obtain ⟨-, hord⟩ := ConditionalExactOrder.conditional_exact_group_order_with_original_odd_factors
    hnonab n hn S e hfour p f hp hpodd hf ((pslTwoClassicalModel_iff_stated _ p f).mp hmodel)
  obtain ⟨-, -, ⟨y₁, hy₁2, hy₁π⟩, hall₁⟩ := hord F Sigma b hSigma ρ Ψ hdata
  obtain ⟨hNcard, hGcard, hidx⟩ := hall₁ y₁ hy₁2 hy₁π
  have h4 : 4 ∣ 2 ^ n := by
    have : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [this]
    exact Nat.pow_dvd_pow 2 hn
  have hy₁x : y₁ ≠ centralInvolution n S e := by
    intro h
    apply model_y0_not_mem_center hp hpodd hf hdata.card b hdata.nonsquare (2 ^ n)
      (wreathModulus_pos n) (wreathModulus_even hn) h4 Sigma hSigma hdata.sigma_odd
    have hcen : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
        Subgroup.center (centralizerOddCoreQuotient n S e) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨g, rfl⟩ := centralizerOddCoreMap_surjective n S e z
      rw [← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.mp (centralInvolution_mem_center n S e) g)]
    rw [← h, hy₁π] at hcen
    rw [Subgroup.mem_center_iff]
    intro z
    apply Ψ.injective
    rw [map_mul Ψ z, map_mul Ψ _ z]
    exact Subgroup.mem_center_iff.mp hcen (Ψ z)
  have hy₁G2 : orderOf (y₁ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy₁2
  have hy₁xG : (y₁ : G) ≠ wreathModelHom S e (Original.x m) := fun h => hy₁x (Subtype.ext h)
  have hBN : ∀ k ∈ N, ∀ v ∈ B, k * v * k⁻¹ ∈ B := fun k hk v hv =>
    conj_mem_of_characteristic n S e hBchar hBR hk hv
  have hBbot : B = ⊥ := by
    by_contra hB
    obtain ⟨ℓ, hℓ, hℓB, hℓI⟩ := exists_prime_dvd_not_dvd_index n hn S e hconf hBR hB
      (fun g hg h2 hgx => (hinvB g hg h2 hgx).2)
    have hdvd := card_dvd_kernelCentralizer_index n S e hBR hBN y₁ (hinvB y₁ y₁.2 hy₁G2 hy₁xG).2
    apply hℓI
    have h1 : (ℓ : ℤ) ∣ (N.index : ℤ) := by
      rw [hidx]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.pow
        (Int.natCast_dvd_natCast.mpr (hℓB.trans hdvd)) two_ne_zero) _) _
    exact Int.natCast_dvd_natCast.mp h1
  have hRA : (centralizerOddCore n S e).map N.subtype = torusFixedCore n S e := by
    rw [← hBsup, hBbot, bot_sup_eq]
  have hRGcard : Nat.card ((centralizerOddCore n S e).map N.subtype) = Nat.card R :=
    Subgroup.card_map_of_injective N.subtype_injective
  have hRcyc : IsCyclic R := by
    have : IsCyclic ((centralizerOddCore n S e).map N.subtype) := by
      rw [hRA]
      exact hA₀c
    exact isCyclic_of_injective
      ((centralizerOddCore n S e).equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
      (MulEquiv.injective _)
  have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((inferInstance : IsMulCommutative R).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinvR : ∀ g ∈ N, orderOf g = 2 → g ≠ wreathModelHom S e (Original.x m) →
      ∀ r ∈ (centralizerOddCore n S e).map N.subtype, g * r = r * g := by
    intro g hg h2 hgx r hr
    obtain ⟨⟨k, hk, hkg⟩, -⟩ := hinvB g hg h2 hgx
    exact involution_centralizes_oddCore n S e hRA hA₀mem hk hkg hr
  have hnoncentral : ∀ y₂ : N, orderOf y₂ = 2 → y₂ ∉ Subgroup.center N →
      ∀ r ∈ R, y₂ * r = r * y₂ := by
    intro y₂ h2 hc r hr
    have hy₂x : (y₂ : G) ≠ wreathModelHom S e (Original.x m) := by
      intro h
      apply hc
      have : y₂ = centralInvolution n S e := Subtype.ext h
      rw [this]
      exact centralInvolution_mem_center n S e
    exact Subtype.ext (hinvR y₂ y₂.2 (by rw [Subgroup.orderOf_coe]; exact h2) hy₂x r ⟨r, hr, rfl⟩)
  have hindex1 : ∀ y₂ : N, (∀ r ∈ R, y₂ * r = r * y₂) →
      (OddNormalQuotientInvolutions.kernelCentralizer R y₂).index = 1 := by
    intro y₂ hy₂
    apply Subgroup.index_eq_one.mpr
    rw [Subgroup.eq_top_iff']
    intro r
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hy₂ r r.2).symm)
  have : IsCyclic W₀ := hW₀c
  have : IsCyclic (torusFixedCore n S e) := hA₀c
  have hUW : ∀ u ∈ modelBase S e, ∀ g ∈ W₀, u * g = g * u := fun u hu g hg =>
    base_commute_lift_core n hn S e p f hp hpodd hf F Sigma b hSigma ρ Ψ hdata hd1 J hJR hu
      ((hW₀mem g).mp hg).1 ((hW₀mem g).mp hg).2.1
  have hCT := fourCentralizer_centralizes_torusCore hnonab n hn S e hconf W₀ hRA hsup hW₀A
    hW₀Ac hUW
  have hSR := sylow_centralizes_oddCore n hn S e hRA hCT hwA
  have hprod := lift_sylow_product hnonab n hn S e hfour p f hp hpodd hf hmodel F Sigma b hSigma
    ρ Ψ hdata hd1 J hJM
  have hRcent := oddCore_le_center n hn S e J hJR hprod hSR hRcomm
  obtain ⟨JS, hJSset, hJSR, hμ, hφ⟩ := lift_sylow_complement n hn S e J hJR hRcent hprod
  have he1 := hindex1 y₁ (fun r hr => Subtype.ext (hinvR y₁ y₁.2 hy₁G2 hy₁xG r ⟨r, hr, rfl⟩))
  rw [hd1, hdata.card, mul_one] at hNcard
  rw [he1, hd1, hdata.card] at hGcard
  rw [he1, hdata.card] at hidx
  simp only [Nat.cast_one, one_pow, mul_one, one_mul] at hGcard hidx
  refine ⟨hRcyc, hRcent, ?_, hnoncentral, fun y₂ h2 hc => hindex1 y₂ (hnoncentral y₂ h2 hc),
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hpodd hf hmodel, hall,
    hNcard, hGcard, hidx, lift_inf_sylow hnonab n hn S e hfour J hJM hJR, JS, hJSset, hJSR, hμ,
    hφ⟩
  rw [← hRGcard, hRA]
  exact hA₀dvd

end CFSG.Wreathed.ConfinedOddCore
