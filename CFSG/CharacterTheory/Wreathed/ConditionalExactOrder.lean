module

public import CFSG.CharacterTheory.Wreathed.ConditionalExactOrderPrincipal
public import CFSG.CharacterTheory.Wreathed.ConditionalExplicitPrincipalOrder
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalExactOrder

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
  CFSG.Wreathed.CentralSL2 CFSG.Wreathed.OddNormalQuotientInvolutions
  CFSG.Wreathed.ConditionalGlobalDegrees

theorem conditional_exact_group_order_with_original_odd_factors_of_localHyp
    {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)] :
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
      let m := 2 ^ n
      let q := Nat.card F
      let d := Nat.card Sigma
      let N := involutionCentralizer n S e
      let R := centralizerOddCore n S e
      let π := centralizerOddCoreMap n S e
      let x : G := wreathModelHom S e (Original.x m)
      let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →*
          SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
        SemidirectProduct.inl
      let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
      let yK := (u ^ 2) ^ (m / 4) *
        specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
      let ε : ℤ := if q % 4 = 1 then 1 else -1
      let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
      (∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
          (basis.representation principal).character = 1 →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 =
          (((m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd : ℝ) : ℂ)) ∧
      (0 : ℝ) < (m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd ∧
      (∃ y : N, orderOf y = 2 ∧ π y = Ψ (ι yK)) ∧
      ∀ y : N, orderOf y = 2 → π y = Ψ (ι yK) →
        let eR : ℕ := (kernelCentralizer R y).index
        Nat.card N = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card G : ℤ) = Nat.card R * m * d * eR ^ 2 * q ^ 3 * ((q : ℤ) ^ 2 - 1) * Qd ∧
        (N.index : ℤ) = eR ^ 2 * q ^ 2 * Qd := by
  refine ⟨hloc.modelData, ?_⟩
  intro F _ _ Sigma b hSigma ρ Ψ hdata m q d N R π x ι u yK ε Qd
  have hx : x = wreathModelHom S e (Original.a (2 ^ n)) ^ (2 ^ n / 2) := wreathModelHom_x_eq n S e
  have hq3 : 3 ≤ q := by
    rw [show q = p ^ f from hdata.card]
    exact three_le_prime_pow hp hpodd hf
  have hεs : ε = 1 ∨ ε = -1 := by
    simp only [ε]
    split_ifs <;> simp
  have hQpos : (0 : ℤ) < Qd := by
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    simp only [Qd]
    rcases hεs with h | h <;> rw [h] <;> nlinarith
  have hqεpos : (0 : ℤ) < q + ε := by
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    rcases hεs with h | h <;> rw [h] <;> omega
  have hcube : ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
      (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 =
        (((m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd : ℝ) : ℂ) := by
    intro ideal _ _ basis principal hprincipal
    rw [hx, conditional_principal_cubic_sum_of_localHyp n hn S e p f hp hpodd hf hloc ideal
      basis principal hprincipal F Sigma b hSigma ρ Ψ hdata]
    simp only [Qd, ε, q, m]
    push_cast
    split_ifs <;> push_cast <;> ring
  have hpos : (0 : ℝ) < (m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd := by
    have hm : (0 : ℝ) < m := by positivity
    have h1 : (0 : ℝ) < (q : ℝ) + ε := by exact_mod_cast hqεpos
    have h2 : (0 : ℝ) < Qd := by exact_mod_cast hQpos
    positivity
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basisG⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principalG, hprincipalG⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisG
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := centralizerOddCoreQuotient n S e)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisH
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := involutionCentralizer n S e)
  obtain ⟨principalN, hprincipalN⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisN
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨-, hyex, hyall⟩ := (conditional_explicit_global_principal_order_identity_of_localHyp n hn
    S e p f hp hpodd hf hloc ideal basisG principalG hprincipalG basisH principalH hprincipalH
    basisN principalN hprincipalN).2 F Sigma b hSigma ρ Ψ hdata
  refine ⟨hcube, hpos, hyex, fun y hy2 hyπ => ?_⟩
  intro eR
  obtain ⟨hc, -, -, -, hGS⟩ := hyall y hy2 hyπ
  have hc' : Nat.card N = Nat.card R * m * d * q * (q ^ 2 - 1) := hc
  have key : (Nat.card G : ℂ) * (((m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd : ℝ) : ℂ) =
      (Nat.card N : ℂ) * m ^ 2 * ((eR * q * (q + ε) : ℤ) : ℂ) ^ 2 := by
    rw [← hcube ideal basisG principalG hprincipalG]
    exact hGS
  push_cast at key
  have hQ0 : ((Qd : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  have hQinv : ((Qd : ℤ) : ℂ) * ((Qd : ℤ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hQ0
  have hA : ((m : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2) ≠ 0 := by
    have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero _ two_ne_zero)
    have hqε : (q : ℂ) + ε ≠ 0 := by exact_mod_cast hqεpos.ne'
    exact mul_ne_zero (pow_ne_zero 2 hm) (pow_ne_zero 2 hqε)
  have key' : (Nat.card G : ℂ) * ((m : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2) =
      ((Nat.card N : ℂ) * eR ^ 2 * q ^ 2 * Qd) * ((m : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2) := by
    linear_combination ((Qd : ℤ) : ℂ) * key -
      ((Nat.card G : ℂ) * ((m : ℂ) ^ 2 * ((q : ℂ) + ε) ^ 2)) * hQinv
  have hG : (Nat.card G : ℂ) = (Nat.card N : ℂ) * eR ^ 2 * q ^ 2 * Qd :=
    mul_right_cancel₀ hA key'
  have hGZ : (Nat.card G : ℤ) = Nat.card N * eR ^ 2 * q ^ 2 * Qd := by exact_mod_cast hG
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hNZ : (Nat.card N : ℤ) = Nat.card R * m * d * q * ((q : ℤ) ^ 2 - 1) := by
    rw [hc']
    push_cast [Nat.cast_sub hq1]
    ring
  have hNpos : (0 : ℤ) < Nat.card N := by exact_mod_cast Nat.card_pos
  refine ⟨hc', ?_, ?_⟩
  · rw [hGZ, hNZ]
    ring
  · have hidx : (Nat.card N : ℤ) * N.index = Nat.card G := by
      exact_mod_cast Subgroup.card_mul_index N
    rw [hGZ] at hidx
    have h := mul_left_cancel₀ hNpos.ne' (hidx.trans (by ring :
      (Nat.card N : ℤ) * eR ^ 2 * q ^ 2 * Qd = Nat.card N * (eR ^ 2 * q ^ 2 * Qd)))
    exact h

theorem conditional_exact_group_order_with_original_odd_factors
    {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (centralizerSimpleLayer n hn S e)
      .PSL 2 p f)
    [Fintype (centralizerOddCoreQuotient n S e)] :
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
      let m := 2 ^ n
      let q := Nat.card F
      let d := Nat.card Sigma
      let N := involutionCentralizer n S e
      let R := centralizerOddCore n S e
      let π := centralizerOddCoreMap n S e
      let x : G := wreathModelHom S e (Original.x m)
      let ι : CentralExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) →*
          SemilinearExtension F b m (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma :=
        SemidirectProduct.inl
      let u := cyclicGenerator F b m (wreathModulus_pos n) (wreathModulus_even hn)
      let yK := (u ^ 2) ^ (m / 4) *
        specialInclusion F b m (wreathModulus_pos n) (wreathModulus_even hn) (weyl F)
      let ε : ℤ := if q % 4 = 1 then 1 else -1
      let Qd : ℤ := (q : ℤ) ^ 2 + ε * q + 1
      (∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
          (basis.representation principal).character = 1 →
        ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 =
          (((m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd : ℝ) : ℂ)) ∧
      (0 : ℝ) < (m : ℝ) ^ 2 * ((q : ℝ) + ε) ^ 2 / Qd ∧
      (∃ y : N, orderOf y = 2 ∧ π y = Ψ (ι yK)) ∧
      ∀ y : N, orderOf y = 2 → π y = Ψ (ι yK) →
        let eR : ℕ := (kernelCentralizer R y).index
        Nat.card N = Nat.card R * m * d * q * (q ^ 2 - 1) ∧
        (Nat.card G : ℤ) = Nat.card R * m * d * eR ^ 2 * q ^ 3 * ((q : ℤ) ^ 2 - 1) * Qd ∧
        (N.index : ℤ) = eR ^ 2 * q ^ 2 * Qd :=
  conditional_exact_group_order_with_original_odd_factors_of_localHyp n hn S e p f hp hpodd hf
    (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)

end CFSG.Wreathed.ConditionalExactOrder
