module

public import CFSG.CharacterTheory.Wreathed.FourPointPrincipalDegreesArith
public import CFSG.CharacterTheory.Wreathed.FourPointTwelveCharacters
public import CFSG.CharacterTheory.Semidihedral.Principal.NonrealSectionVanishing

public noncomputable section

namespace CFSG.Wreathed.FourPointPrincipalDegrees

open Equiv CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.FourPointOrderFour

open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

theorem four_point_principal_block_degrees
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
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
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π aN →
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
  intro H N π aN a x C W u iF U₀ Φ hΦ z hzC hzodd hπz ideal _ _ basis principal hprincipal B₀ X
    deg
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  subst hn2
  obtain ⟨-, -, htw⟩ :=
    FourPointTwelveCharacters.four_point_twelve_principal_characters_and_signed_degree_table
      hnonab 2 hn S e alpha
  obtain ⟨β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl', pβ, pκ, pl, δ, ε, ζ, hpβ, hpκ, hpl, hδ, hε,
    hζ, r₀, rβ, rκ, rl, rγ, rψ, cη, cξκ, cξl, nη, nξκ, nξl, hnd, hB, P₀, Pβ, Pκ, Pl, Pγ, Pη, Pη',
    Pψ, Pξκ, Pξκ', Pξl, Pξl', -, -, -, -, -, -, -, -, -, -, -, -, A₀, Aβ, Aκ, Al, Aγ, Aη, Aη',
    Aψ, Aξκ, Aξκ', Aξl, Aξl', -, -, -, -, Bγ, -, -, -, -, -, -, -, T₀, Tβ, Tκ, Tl, Tγ, Tη, Tψ,
    Tξκ, Tξl, Tη', Tξκ', Tξl', U₀', Uβ, Uκ, Ul, Uγ, Uη, Uψ, Uξκ, Uξl, Uη', Uξκ', Uξl', -, -,
    hodd, h0, dξκ, dξl, dη, dγ, dψ, hfaith⟩ :=
    (htw Φ hΦ).2 z hzC hzodd hπz ideal basis principal hprincipal Complex.I Complex.I_sq
  have hB' : B₀ = {principal, β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} := hB
  have hX1 : ∀ χ, X χ 1 = (deg χ : ℂ) := fun χ => by
    show (basis.representation χ).character 1 = _
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  have hd₀ : deg principal = 1 := by
    have h := hX1 principal
    rw [show X principal 1 = 1 by
      show (basis.representation principal).character 1 = 1
      rw [hprincipal]
      rfl] at h
    exact_mod_cast h.symm
  have hpair : ∀ χ χ' : basis.index, (∀ g, X χ' g = conj (X χ g)) → deg χ' = deg χ :=
    fun χ χ' h => by
      have h1 := h 1
      rw [hX1, hX1, map_natCast] at h1
      exact_mod_cast h1
  have dη' : deg η' = deg η := hpair η η' cη
  have dξκ₀ : deg ξκ = deg κ := dξκ
  have dξl₀ : deg ξl = deg lam := dξl
  have dξκ' : deg ξκ' = deg κ := (hpair ξκ ξκ' cξκ).trans dξκ₀
  have dξl' : deg ξl' = deg lam := (hpair ξl ξl' cξl).trans dξl₀
  have ha4 : orderOf a = 2 ^ 2 := orderOf_wreathModelHom_a 2 S e
  have hx2 : orderOf x = 2 := by
    rw [show x = a ^ (2 ^ 2 / 2) from wreathModelHom_x_eq 2 S e,
      orderOf_pow_of_dvd (by norm_num) (by rw [ha4]; norm_num), ha4]
    norm_num
  have hxinv : x⁻¹ = x := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← hx2, pow_orderOf_eq_one]
  have hAreal : ∀ χ, conj (X χ x) = X χ x := fun χ => by
    show conj ((basis.representation χ).character x) = _
    rw [finite_character_conjugate_inverse, hxinv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : G := wreathModelHom S e (Original.s (2 ^ 2)) * wreathModelHom S e (Original.z (2 ^ 2))
    with hρ
  have hρ8 : ∃ k : ℕ, orderOf ρ = 2 ^ k := ⟨3, by
    rw [hρ, ← WreathCentralSquare.actualRoot_eq, WreathCentralSquare.actualRoot_orderOf 2 hn S e]
    norm_num⟩
  have hρnc : ¬ IsConj ρ ρ⁻¹ := by
    rw [hρ, ← WreathCentralSquare.actualRoot_eq]
    exact FourPointOrderEight.root_not_isConj_inv S e
  have hanc : ¬ IsConj a a⁻¹ := not_isConj_a_inv 2 hn S e
  have h1c : Nat.Coprime 2 (orderOf (1 : G)) := by
    rw [orderOf_one]
    norm_num
  have hzc : Nat.Coprime 2 (orderOf (z : G)) :=
    Nat.coprime_two_left.mpr (by rwa [Subgroup.orderOf_coe])
  have V1 := (Semidihedral.Principal.nonreal_primary_section_block_involution_product_vanishing
    basis ideal 2 principal hx2 hx2 hρ8 hρnc 1 (Subgroup.one_mem _) h1c).1
  have V2 := (Semidihedral.Principal.nonreal_primary_section_block_involution_product_vanishing
    basis ideal 2 principal hx2 hx2 ⟨2, ha4⟩ hanc 1 (Subgroup.one_mem _) h1c).1
  have V3 := (Semidihedral.Principal.nonreal_primary_section_block_involution_product_vanishing
    basis ideal 2 principal hx2 hx2 ⟨2, ha4⟩ hanc (z : G) hzC hzc).1
  simp only [mul_one] at V1 V2
  rw [hB] at V1 V2 V3
  have E1 := first_equation (fun χ => X χ x) (fun χ => X χ ρ) (fun χ => X χ 1) deg hpβ hpκ hpl
    hnd hAreal hX1 V1 A₀ Aβ Aκ Al Aγ Aψ Aη Aη' Aξκ Aξκ' Aξl Aξl' P₀ Pβ Pκ Pl Pγ Pψ Pη Pη' Pξκ
    Pξκ' Pξl Pξl' hd₀
  have E2 := second_equation (fun χ => X χ x) (fun χ => X χ a) (fun χ => X χ (a * z))
    (fun χ => X χ 1) deg Complex.I hpβ hpκ hpl hnd hX1 V2 V3 A₀ Aβ Aκ Al Aγ Aψ Aη Aη' Aξκ Aξκ'
    Aξl Aξl' T₀ Tβ Tκ Tl Tγ Tη Tψ Tξκ Tξl Tη' Tξκ' Tξl' U₀' Uβ Uκ Ul Uγ Uη Uψ Uξκ Uξl Uη' Uξκ'
    Uξl' hd₀ dη' dξκ₀ dξκ' dξl₀ dξl'
  have two_le : ∀ χ ∈ ({β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl'} : Finset basis.index),
      2 ≤ deg χ := fun χ hχ => (hfaith χ hχ).2
  have hdβ : deg β ≠ 0 := by have := two_le β (by simp); omega
  have hdκ : deg κ ≠ 0 := by have := two_le κ (by simp); omega
  have hdl : deg lam ≠ 0 := by have := two_le lam (by simp); omega
  have h0' : 1 + pβ * (deg β : ℤ) + pκ * deg κ + pl * deg lam = 0 := h0
  obtain ⟨sβ, sκ, sl, eβ, eκ, el⟩ :=
    signed_degrees_solve (dβ := deg β) (dκ := deg κ) (dl := deg lam) hpβ hpκ hpl hdβ hdκ hdl h0'
      E1 E2
  have dη₀ : ε * (deg η : ℤ) = 1 + pβ * deg β := dη
  have dγ₀ : δ * (deg γ : ℤ) = -1 - pκ * deg κ := dγ
  have dψ₀ : ζ * (deg ψ : ℤ) = 1 + pβ * deg β + 2 * (pκ * deg κ) := dψ
  rw [sβ, eβ] at dη₀
  rw [sκ, eκ] at dγ₀
  rw [sβ, sκ, eβ, eκ] at dψ₀
  obtain ⟨sε, eη⟩ := sign_mul_eq hε (by rw [dη₀]; norm_num : ε * (deg η : ℤ) = 28) (by norm_num)
  obtain ⟨sδ, eγ⟩ := sign_mul_eq hδ (by rw [dγ₀]; norm_num : δ * (deg γ : ℤ) = 6) (by norm_num)
  obtain ⟨sζ, eψ⟩ := sign_mul_eq hζ (by rw [dψ₀]; norm_num : ζ * (deg ψ : ℤ) = 14) (by norm_num)
  have eη' : deg η' = 28 := by omega
  have eγ' : deg γ = 6 := by omega
  have eψ' : deg ψ = 14 := by omega
  have eη'' : deg η = 28 := by omega
  have eξκ : deg ξκ = 7 := by omega
  have eξκ' : deg ξκ' = 7 := by omega
  have eξl : deg ξl = 21 := by omega
  have eξl' : deg ξl' = 21 := by omega
  have hodd' : B₀.filter (fun χ => Odd (deg χ)) = {principal, β, κ, lam, ξκ, ξκ', ξl, ξl'} :=
    hodd
  have nrη := not_real_of_pair (X η) (X η') cη nη
  have nrξκ := not_real_of_pair (X ξκ) (X ξκ') cξκ nξκ
  have nrξl := not_real_of_pair (X ξl) (X ξl') cξl nξl
  refine ⟨?_, ?_, ⟨β, κ, lam, γ, ψ, η, η', ξκ, ξκ', ξl, ξl', hnd, hB', ?_, cη, cξκ, cξl, hd₀,
    eβ, eκ, el, eγ', eψ', eη'', eη', eξκ, eξκ', eξl, eξl', hodd'⟩, ?_, ?_, ?_⟩
  · rw [hB']
    exact card_twelve hnd
  · rw [hB', map_val_twelve deg hnd, hd₀, eβ, eκ, el, eγ', eψ', eη'', eη', eξκ, eξκ', eξl, eξl']
    decide
  · rw [hB']
    exact filter_twelve _ r₀ rβ rκ rl rγ rψ nrη.1 nrη.2 nrξκ.1 nrξκ.2 nrξl.1 nrξl.2
  · rw [hodd', map_val_eight deg (nodup_drop_middle hnd), hd₀, eβ, eκ, el, eξκ, eξκ', eξl, eξl']
    decide
  · rw [hB']
    exact cube_sum (fun χ => X χ x) (fun χ => X χ 1) deg hnd hX1 sβ sκ sl sδ sε sζ A₀ Aβ Aκ Al Aγ
      Aψ Aη Aη' Aξκ Aξκ' Aξl Aξl' hd₀ eβ eκ el eγ' eψ' eη'' eη' eξκ eξκ' eξl eξl'
  · have hγ : γ ∈ B₀ := by
      rw [hB']
      simp
    refine ⟨γ, hγ, eγ', fun χ hχ h6 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hB'] at hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rcases hχ with h | h | h | h | h | h | h | h | h | h | h | h <;>
        first | exact h | (rw [h] at h6; omega)
    · have h : X γ x = -2 * (δ : ℂ) := Aγ
      rw [h, sδ]
      norm_num
    · have h : X γ a = -2 * (δ : ℂ) := Tγ
      rw [h, sδ]
      norm_num
    · have h : X γ (x * z) = (δ : ℂ) := Bγ
      rw [h, sδ]
      norm_num
    · have h : X γ (a * z) = (δ : ℂ) := Uγ
      rw [h, sδ]
      norm_num

end CFSG.Wreathed.FourPointPrincipalDegrees
