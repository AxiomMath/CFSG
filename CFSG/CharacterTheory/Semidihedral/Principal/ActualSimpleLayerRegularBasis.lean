module

public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage
public import CFSG.CharacterTheory.Semidihedral.Principal.ProjectiveCentralDoubleCoverRegularBasis
public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOuterQuotient CFSG.Semidihedral.SemilinearOddExtensions
  CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Wreathed CFSG.Open

theorem actual_simple_layer_centralizer_principal_regular_basis {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G) (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2) (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (C t)) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : Gamma t →* coordinateE F),
      Nat.card F = p ^ f ∧ Function.Injective ρ ∧
      (CFSG.generalizedFitting (Gamma t)).map ρ = specialLayer F ∧ linearLayer F ≤ ρ.range ∧
      (let φ : C t → ℂ := fun c =>
        (Nat.card {x : Omega F // ((ρ (kappa t c) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let e : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
      (∃ lφ ∈ B, (basis.representation lφ).IsIrreducible ∧
        (basis.representation lφ).character = φ ∧
        Module.finrank ℂ (basis.representation lφ).vector = Nat.card F ∧
        MonoidHom.ker (basis.representation lφ).representation = NZ t) ∧
      (∀ χ ∈ B, ∃ a b : ℤ, (∀ y : C t, Odd (orderOf y) →
          (basis.representation χ).character y = a + b * φ y) ∧ 0 ≤ b ∧ 0 ≤ a + b ∧
        ∀ a' b' : ℤ, (∀ y : C t, Odd (orderOf y) →
          (basis.representation χ).character y = a' + b' * φ y) → a' = a ∧ b' = b) ∧
      LinearIndependent ℤ ![oddRestriction (1 : C t → ℂ), oddRestriction (1 + (e : ℂ) • φ)] ∧
      Submodule.span ℤ {oddRestriction (1 : C t → ℂ), oddRestriction (1 + (e : ℂ) • φ)} =
        oddRestrictionLattice basis B ∧
      (∃ D : Matrix B (Fin 2) ℤ, ∀ χ : B,
        oddRestriction (basis.representation χ).character =
          D χ 0 • oddRestriction (1 : C t → ℂ) + D χ 1 • oddRestriction (1 + (e : ℂ) • φ)) ∧
      ∀ D : Matrix B (Fin 2) ℤ, (∀ χ : B,
        oddRestriction (basis.representation χ).character =
          D χ 0 • oddRestriction (1 : C t → ℂ) + D χ 1 • oddRestriction (1 + (e : ℂ) • φ)) →
        D.transpose * D = !![8, -4; -4, ((2 ^ (n - 2) + 2 : ℕ) : ℤ)]) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hfield, hfinite, A, ρ, hdata⟩ := actual_simple_layer_matrix_data n hn S0 f0 hG t ht
    hnonab hcentral hnc p f hp hpodd hf hmodel
  obtain ⟨-, -, hz, hzc, -, ⟨P, ⟨eP⟩⟩, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  let _ := hfield
  let _ := hfinite
  let _ : Fintype F := Fintype.ofFinite F
  have hρ := hdata.faithful
  have hDρ : linearLayer F ≤ ρ.range := by
    rw [hdata.full_image]
    exact le_sup_left
  refine ⟨F, hfield, hfinite, ρ, hdata.field_card, hρ, hdata.layer_image, hDρ, ?_⟩
  intro φ e B
  set ψ : Gamma t →* Equiv.Perm (Omega F) := (coordinateE F).subtype.comp ρ with hψdef
  have hψ : Function.Injective ψ := (coordinateE F).subtype_injective.comp hρ
  set Δ := ψ.range with hΔdef
  set πH : H t →* Δ := ψ.rangeRestrict.comp (barKappa t) with hπHdef
  have hπH : Function.Surjective πH :=
    ψ.rangeRestrict_surjective.comp (barKappa_surjective t)
  have hker : πH.ker = Subgroup.zpowers (nu t (tInC t)) := by
    rw [hπHdef, MonoidHom.ker_comp_of_injective _ _
      ((MonoidHom.rangeRestrict_injective_iff).mpr hψ)]
    exact barKappa_kernel t
  have hZ : πH.ker ≤ Subgroup.center (H t) := by
    rw [hker, Subgroup.zpowers_le]
    exact hzc
  have hZcard : Nat.card πH.ker = 2 := by
    rw [hker, Nat.card_zpowers, hz]
  have hDΔ : coordinateD F ≤ Δ := by
    intro d hd
    have hmem : (⟨d, coordinateD_le_E F hd⟩ : coordinateE F) ∈ ρ.range := hDρ hd
    obtain ⟨γ, hγ⟩ := hmem
    exact ⟨γ, by rw [hψdef, MonoidHom.comp_apply, hγ]; rfl⟩
  have hΔE : Δ ≤ coordinateE F := by
    rintro _ ⟨γ, rfl⟩
    exact (ρ γ).2
  have hbij : Function.Bijective ψ.rangeRestrict :=
    ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hψ, ψ.rangeRestrict_surjective⟩
  have hS : ∃ T : Sylow 2 Δ,
      Nonempty ((T : Subgroup Δ) ≃* DihedralGroup (2 ^ ((n - 1) - 1))) := by
    refine ⟨P.mapSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective, ⟨?_⟩⟩
    rw [Sylow.coe_mapSurjective, show n - 1 - 1 = n - 2 by omega]
    exact ((MulEquiv.ofBijective ψ.rangeRestrict hbij).subgroupMap
      (P : Subgroup (Gamma t))).symm.trans eP
  have hGnc : ∃ T : Sylow 2 (coordinateG F), ¬ IsCyclic (T : Subgroup (coordinateG F)) := by
    let iso : CFSG.generalizedFitting (Gamma t) ≃* coordinateG F :=
      (((CFSG.generalizedFitting (Gamma t)).equivMapOfInjective ρ hρ).trans
        (MulEquiv.subgroupCongr hdata.layer_image)).trans
        (Subgroup.subgroupOfEquivOfLe ((coordinateG_le_D F).trans (coordinateD_le_E F)))
    let U : Sylow 2 (CFSG.generalizedFitting (Gamma t)) := Classical.choice Sylow.nonempty
    refine ⟨U.mapSurjective (f := iso.toMonoidHom) iso.surjective, fun hcyc => hnc U ?_⟩
    have hcyc' : IsCyclic ((U : Subgroup (CFSG.generalizedFitting (Gamma t))).map
        iso.toMonoidHom) := hcyc
    exact ((iso.subgroupMap (U : Subgroup (CFSG.generalizedFitting (Gamma t)))).isCyclic).mpr
      hcyc'
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := H t)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisH
  obtain ⟨-, hΦ, hcoeff, hind, hspan, hrows, hgram⟩ :=
    projective_central_double_cover_principal_regular_integral_basis hp hpodd hf F
      hdata.field_card Δ hDΔ hΔE (k := n - 1) (by omega) hS hGnc πH hπH hZ hZcard basisH ideal
      principalH hprincipalH
  set ΦH : H t → ℂ := fun h =>
    (Nat.card {x : Omega F // ((πH h : Δ) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 with hΦHdef
  have hΦ1 : ΦH 1 = Nat.card F := by
    have hfix : Nat.card {x : Omega F // ((πH 1 : Δ) : Equiv.Perm (Omega F)) x = x} =
        Nat.card (Omega F) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
      rw [map_one]
      rfl)
    simp only [ΦH]
    rw [hfix, card_omega]
    push_cast
    ring
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![8, -4; -4, ((2 ^ (n - 2) + 2 : ℕ) : ℤ)]
  have hHdata : PrincipalRegularIntegralBasisData basisH ideal principalH ΦH e (Nat.card F) M := by
    refine ⟨hΦ, hΦ1, fun χ hχ => ?_, hind, hspan, hrows, fun D hD => ?_⟩
    · obtain ⟨a, b, hab, hb, hab0, huniq⟩ := hcoeff χ hχ
      refine ⟨a, b, hab, hb, hab0, ?_, huniq⟩
      have h1 := hab 1 (by rw [orderOf_one]; exact odd_one)
      rw [h1, hΦ1]
    · rw [hgram D hD, show n - 1 - 1 = n - 2 by omega]
  have hNodd : Odd (Nat.card (nu t).ker) := by
    rw [show (nu t).ker = N t from QuotientGroup.ker_mk' _]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp CFSG.pPrimeCore_coprime_card h2)
  have hνsurj : Function.Surjective (nu t) := QuotientGroup.mk'_surjective _
  obtain ⟨hN1, -, -, -⟩ := normal_prime_kernel_principal_block_inflation_of_surjective (nu t)
    hνsurj basis ideal 2 hNodd.not_two_dvd_nat basisH principal hprincipal principalH
    hprincipalH
  obtain ⟨bij, hbij⟩ := exists_inflation_equiv (nu t) hνsurj basis basisH _ _ hN1
  obtain ⟨hCdata, -⟩ := principalRegularIntegralBasisData_comp (nu t) hνsurj hNodd basis basisH
    ideal principal principalH bij hbij hHdata
  have hφeq : (fun y => ΦH (nu t y)) = φ := rfl
  rw [hφeq] at hCdata
  set ρC : C t →* Δ := πH.comp (nu t) with hρCdef
  have hρC : Function.Surjective ρC := hπH.comp hνsurj
  obtain ⟨_hnf, _hlam, _hc₀, _hδsq, ⟨_lδ, lφ, _lδφ, _hδchar, hφchar, _hδφchar, _hnodup,
      hP, _hdeg1, _hdegδ, hdegφ, _hdegδφ, hkerφ, _hkerδφ⟩, _hrest⟩ :=
    projective_linear_two_four_principal_odd_degree_characters hp hpodd hf F hdata.field_card Δ
      hDΔ hΔE ρC hρC basis ideal principal hprincipal
  have hρCker : ρC.ker = NZ t := by
    rw [hρCdef, ← MonoidHom.comap_ker, hker, ← MonoidHom.map_zpowers, Subgroup.comap_map_eq,
      show (nu t).ker = N t from QuotientGroup.ker_mk' _, sup_comm]
  refine ⟨⟨lφ, (hP lφ (by simp)).2.1, (hP lφ (by simp)).1, funext hφchar, hdegφ,
    hkerφ.trans hρCker⟩,
    fun χ hχ => ?_, hCdata.linearIndependent, hCdata.span, hCdata.rows, hCdata.gram⟩
  obtain ⟨a, b, hab, hb, hab0, -, huniq⟩ := hCdata.coefficients χ hχ
  exact ⟨a, b, hab, hb, hab0, huniq⟩

end CFSG.Semidihedral.Principal
