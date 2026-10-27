module

public import CFSG.CharacterTheory.Wreathed.FourPointOddSectionIndicatorSupport
public import CFSG.CharacterTheory.Wreathed.FourPointPrincipalOrderScalar
public import CFSG.CharacterTheory.Wreathed.NormalTwoWeightedOddSection

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FourPointOddSectionIndicator

open Equiv CFSG.Wreathed CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.FourPointCompleteModel CFSG.Wreathed.OddNormalQuotientInvolutions
  CFSG.Wreathed.InvolutionInducedCharacters CFSG.Semidihedral.FourPointLifts

theorem four_point_principal_odd_section_odd_core_indicator {G : Type} [Group G] [Fintype G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    [Fintype (centralizerOddCoreQuotient n S e)] :
    let H := centralizerOddCoreQuotient n S e
    let N := involutionCentralizer n S e
    let R := centralizerOddCore n S e
    let π := centralizerOddCoreMap n S e
    let st : N := wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n))
    let x : G := wreathModelHom S e (Original.x (2 ^ n))
    let W := CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let u := cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let iF := specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
    let y₀ : W := u ^ 2 * iF (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))
    n = 2 ∧ (∃ Φ : W ≃* H, Φ (u ^ 2) = π st) ∧
    ∀ Φ : W ≃* H, Φ (u ^ 2) = π st →
      (∃ y : N, orderOf y = 2 ∧ π y = Φ y₀) ∧
      ∀ y : N, orderOf y = 2 → π y = Φ y₀ →
        let eR : ℕ := (kernelCentralizer R y).index
        ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
          [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
          (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
          (_ : (basis.representation principal).character = 1) (z : N), Odd (orderOf z) →
          (Nat.card G : ℂ) * ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal,
            (basis.representation χ).character x ^ 2 * (basis.representation χ).character (x * z) /
              (basis.representation χ).character 1 =
            55296 * Nat.card R * eR ^ 2 * (if z ∈ R then 1 else 0) := by
  intro H N R π st x W u iF y₀
  have hn2 : n = 2 := FourPointResidual.four_point_parameter n hn S e alpha
  obtain ⟨Φ₀, hΦ₀, -⟩ := exists_four_point_model_equiv hnonab n hn S e alpha
  refine ⟨hn2, ⟨Φ₀, hΦ₀⟩, ?_⟩
  intro Φ hΦ
  subst hn2
  have hbot : ∀ σ ∈ (⊥ : Subgroup (ZMod 3 ≃+* ZMod 3)),
      σ ((twoUnit : (ZMod 3)ˣ) : ZMod 3) = twoUnit := by
    intro σ hσ
    rw [Subgroup.mem_bot] at hσ
    subst hσ
    rfl
  let Φ' : SemilinearExtension (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2)
      (wreathModulus_even hn) ⊥ hbot ≃* involutionCentralizer 2 S e ⧸ centralizerOddCore 2 S e :=
    (semidirectBotEquiv _).symm.trans Φ
  have hΦ'inl : ∀ w, Φ' (SemidirectProduct.inl w) = Φ w := by
    intro w
    change Φ ((semidirectBotEquiv _).symm (SemidirectProduct.inl w)) = Φ w
    congr 1
    exact (semidirectBotEquiv _).symm_apply_eq.mpr rfl
  set xN : N := centralInvolution 2 S e with hxN
  have hst2 : st ^ 2 = xN := by
    apply Subtype.ext
    change (wreathModelHom S e (Original.a (2 ^ 2))) ^ 2 = wreathModelHom S e (Original.x (2 ^ 2))
    rw [← map_pow]
    rfl
  have hΦ' : Φ' (SemidirectProduct.inl (cyclicGenerator (ZMod 3) twoUnit (2 ^ 2)
      (wreathModulus_pos 2) (wreathModulus_even hn) ^ (2 ^ 2))) =
      QuotientGroup.mk' (centralizerOddCore 2 S e)
        ⟨wreathModelHom S e (Original.x (2 ^ 2)),
          Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
    rw [hΦ'inl]
    change Φ (u ^ 4) = π xN
    have hu4 : u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
    rw [hu4, map_pow, hΦ, ← map_pow, hst2]
  have hR : Odd (Nat.card (centralizerOddCore 2 S e)) := centralizerOddCore_card_odd 2 S e
  have hII := actual_centralizer_involution_induced_characters_and_principal_order_identity
    hnonab 2 hn S e (centralizerOddCore 2 S e) hR (F := ZMod 3) (p := 3) (f := 1)
    Nat.prime_three (by decide) le_rfl (by simp) twoUnit twoUnit_not_isSquare ⊥ hbot
    (by simp) Φ' hΦ'
  have hpow : (2 : ℕ) ^ 2 / 4 = 1 := by norm_num
  simp only [hpow, pow_one] at hII
  obtain ⟨hyex, hII⟩ := hII
  have hy₀ : ∀ v, v = Φ' (SemidirectProduct.inl (cyclicGenerator (ZMod 3) twoUnit (2 ^ 2)
      (wreathModulus_pos 2) (wreathModulus_even hn) ^ 2 *
      specialInclusion (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2) (wreathModulus_even hn)
        (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3)))) ↔ v = Φ y₀ := by
    intro v
    rw [hΦ'inl]
    rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy2, hyΦ⟩ := hyex
    exact ⟨y, hy2, (hy₀ _).mp hyΦ⟩
  intro y hy2 hyΦ eR ideal _ _ basis principal hprincipal z hz
  obtain ⟨⟨hclasses, -, -, -, -, hxyconj⟩, -, horder⟩ := hII y hy2 ((hy₀ _).mpr hyΦ)
  obtain ⟨-, -, hscalar⟩ :=
    FourPointPrincipalOrderScalar.four_point_actual_principal_order_scalar hnonab 2 hn S e alpha
  obtain ⟨hc96, -, hcentH, -⟩ := (hscalar Φ hΦ).2 y hy2 hyΦ
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := H)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisH
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalH
  obtain ⟨basisN⟩ := finiteIrreducibleCharacterBasis_exists (G := N)
  obtain ⟨principalN, hprincipalN⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisN
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hprincipalN
  obtain ⟨-, -, -, -, -, hQnormal, hQcard, -, -, -, -, hinflI, hinflE, -⟩ :=
    four_point_actual_centralizer_complete_model_and_principal_block hnonab 2 hn S e alpha ideal
      basisH principalH hprincipalH basisN principalN hprincipalN
  obtain ⟨hzid, -⟩ := horder ideal basis principal hprincipal basisN principalN hprincipalN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 (fourKlein.comap (alpha.toMonoidHom.comp
      (centralizerFullQuotientMap 2 hn S e))) := IsPGroup.of_card (n := 4) hQcard
  have hx2N : orderOf xN = 2 := (hclasses xN).mpr (Or.inl rfl)
  have hπsurj : Function.Surjective π := centralizerOddCoreMap_surjective 2 S e
  have hcen : π xN ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro h
    obtain ⟨g, rfl⟩ := hπsurj h
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  have hinvH : orderOf (π xN) = 2 := orderOf_mk_eq_two R hR hx2N
  have helH : orderOf (π y) = 2 := orderOf_mk_eq_two R hR hy2
  have hconjH : IsConj (π xN * π y) (π y) := by
    have h := MonoidHom.map_isConj π hxyconj
    rw [map_mul] at h
    exact h.symm
  have htQ := centralInvolution_mem_fourPointQ 2 hn S e alpha
  have hvQ := model_weyl_mem_fourPointQ hn S e alpha Φ hΦ (π y) hyΦ
    (by rw [← orderOf_dvd_iff_pow_eq_one, helH])
  obtain ⟨-, hFodd⟩ := normal_two_subgroup_weighted_odd_section_support basisH _ hQp (π xN) (π y)
    htQ hcen hinvH hvQ helH hconjH (6 * eR : ℂ)
  have hπz : Odd (orderOf (π z)) := hz.of_dvd_nat (orderOf_map_dvd π z)
  have hFz := hFodd (π z) hπz
  beta_reduce at hFz
  have hq : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have hε : (if Nat.card (ZMod 3) % 4 = 1 then (1 : ℤ) else -1) = -1 := by rw [hq]; rfl
  have hAC : (((kernelCentralizer R y).index * Nat.card (ZMod 3) *
      (Nat.card (ZMod 3) + if Nat.card (ZMod 3) % 4 = 1 then (1 : ℤ) else -1) : ℤ) : ℂ) =
      6 * eR := by
    rw [hε, hq]
    push_cast
    simp only [eR]
    ring
  rw [hzid z hz, hAC]
  change (Nat.card N : ℂ) * ∑ ψ ∈ coefficientBlock basisN (localizedComplexIntegerRing ideal)
      principalN, ((basisN.representation ψ).character xN +
        6 * (eR : ℂ) * (basisN.representation ψ).character y) ^ 2 *
        (basisN.representation ψ).character (xN * z) / (basisN.representation ψ).character 1 = _
  rw [FourPointPrincipalOrderScalar.sum_inflated_block basisN basisH π hπsurj _ hinflI hinflE
    (fun f => (f xN + (6 * eR : ℂ) * f y) ^ 2 * f (xN * z) / f 1)]
  simp only [Function.comp_apply, map_one, map_mul]
  rw [hFz, hcentH]
  by_cases hzR : z ∈ R
  · rw [ite_eq_left (show π z = 1 from (QuotientGroup.eq_one_iff z).mpr hzR), ite_eq_left hzR,
      hc96]
    push_cast
    ring
  · rw [ite_eq_right (show ¬ π z = 1 from fun h => hzR ((QuotientGroup.eq_one_iff z).mp h)),
      ite_eq_right hzR]
    ring

end CFSG.Wreathed.FourPointOddSectionIndicator
