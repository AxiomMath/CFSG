module

public import CFSG.CharacterTheory.Wreathed.FourPointPrincipalDegreesBlock
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo

public noncomputable section

namespace CFSG.Wreathed.FourPointPrincipalDegrees

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour
  CFSG.Wreathed.OddNormalQuotientInvolutions

open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_principal_degrees_and_original_odd_core_order
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let aN : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let a : G := wreathModelHom S e (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let C := orderFourCentralizer n S e
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let U₀ : W := iF (CentralSL2.upperSL (ZMod 3) 1)
    let y₀ : W := u ^ 2 * iF (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π aN) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π aN →
      (∃ z : N, (z : G) ∈ C ∧ Odd (orderOf z) ∧ π z = Φ U₀) ∧
      (∃ y : N, orderOf y = 2 ∧ π y = Φ y₀) ∧
      (∀ y : N, orderOf y = 2 → π y = Φ y₀ →
        let eR : ℕ := (kernelCentralizer R y).index
        Nat.card G = 6048 * Nat.card R * eR ^ 2 ∧ Nat.card N = 96 * Nat.card R ∧
          N.index = 63 * eR ^ 2) ∧
      ∀ z : N, (z : G) ∈ C → Odd (orderOf z) → π z = Φ U₀ →
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1),
          let B₀ := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
          let X : basis.index → G → ℂ := fun χ => (basis.representation χ).character
          let deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
          B₀.card = 12 ∧ B₀.val.map deg = {1, 6, 7, 7, 7, 14, 21, 21, 21, 27, 28, 28} ∧
          (∃ (β κ lam γ ψ η η' ξκ ξκ' ξl ξl' : basis.index),
            [principal, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'].Nodup ∧
            B₀ = {principal, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} ∧
            B₀.filter (fun χ => ∀ g, conj (X χ g) = X χ g) = {principal, β, κ, lam, γ, ψ} ∧
            (∀ g, X η' g = conj (X η g)) ∧ (∀ g, X ξκ' g = conj (X ξκ g)) ∧
            (∀ g, X ξl' g = conj (X ξl g)) ∧
            deg principal = 1 ∧ deg β = 27 ∧ deg κ = 7 ∧ deg lam = 21 ∧ deg γ = 6 ∧
            deg ψ = 14 ∧ deg η = 28 ∧ deg η' = 28 ∧ deg ξκ = 7 ∧ deg ξκ' = 7 ∧ deg ξl = 21 ∧
            deg ξl' = 21 ∧
            B₀.filter (fun χ => Odd (deg χ)) = {principal, β, κ, lam, ξκ, ξκ', ξl, ξl'}) ∧
          (B₀.filter (fun χ => Odd (deg χ))).val.map deg = {1, 7, 7, 7, 21, 21, 21, 27} ∧
          ∑ χ ∈ B₀, X χ x ^ 3 / X χ 1 = 64 / 7 ∧
          ∃ γ ∈ B₀, deg γ = 6 ∧ (∀ χ ∈ B₀, deg χ = 6 → χ = γ) ∧
            X γ x = -2 ∧ X γ a = -2 ∧ X γ (x * z) = 1 ∧ X γ (a * z) = 1 := by
  intro H N R π aN a x C W u iF U₀ y₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, hΦex, htw⟩ :=
    FourPointTwelveCharacters.four_point_twelve_principal_characters_and_signed_degree_table
      hnonab 2 hn S e alpha
  obtain ⟨-, -, hord⟩ :=
    FourPointPrincipalOrderScalar.four_point_actual_principal_order_scalar hnonab 2 hn S e alpha
  have hblock := four_point_principal_block_degrees hnonab 2 hn S e alpha
  refine ⟨rfl, hΦex, fun Φ hΦ => ?_⟩
  obtain ⟨hyex, hyall⟩ := hord Φ hΦ
  have hzex := (htw Φ hΦ).1
  refine ⟨hzex, hyex, fun y hy2 hyΦ => ?_, fun z hzC hzodd hπz ideal _ _ basis principal
    hprincipal => hblock Φ hΦ z hzC hzodd hπz ideal basis principal hprincipal⟩
  intro eR
  obtain ⟨hc, -, -, -, -, -, hsum⟩ := hyall y hy2 hyΦ
  have hc' : Nat.card N = 96 * Nat.card R := hc
  obtain ⟨z, hzC, hzodd, hπz⟩ := hzex
  obtain ⟨ideal, hmax, hchar⟩ := CFSG.RankTwoShapes.exists_maximal_ideal_residue_two
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨hG, hG', -⟩ := hsum ideal basis principal hprincipal
  have h64 : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 = 64 / 7 :=
    (hblock Φ hΦ z hzC hzodd hπz ideal basis principal hprincipal).2.2.2.2.1
  have hG₁ : (Nat.card G : ℂ) *
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character x ^ 3 / (basis.representation χ).character 1 =
      16 * (Nat.card N : ℂ) * (6 * (eR : ℂ)) ^ 2 := hG
  have hG₂ : 16 * Nat.card N * (6 * eR) ^ 2 = 55296 * Nat.card R * eR ^ 2 := hG'
  have hG₃ : 16 * (Nat.card N : ℂ) * (6 * (eR : ℂ)) ^ 2 =
      55296 * (Nat.card R : ℂ) * (eR : ℂ) ^ 2 := by
    exact_mod_cast hG₂
  rw [h64] at hG₁
  have hGc : (Nat.card G : ℂ) = 6048 * (Nat.card R : ℂ) * (eR : ℂ) ^ 2 := by
    linear_combination (7 / 64 : ℂ) * hG₁ + (7 / 64 : ℂ) * hG₃
  have hGn : Nat.card G = 6048 * Nat.card R * eR ^ 2 := by exact_mod_cast hGc
  refine ⟨hGn, hc', ?_⟩
  have hR : 0 < 96 * Nat.card R := Nat.mul_pos (by norm_num) Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hR
  rw [← hc', Subgroup.card_mul_index, hGn, hc']
  ring

end CFSG.Wreathed.FourPointPrincipalDegrees
