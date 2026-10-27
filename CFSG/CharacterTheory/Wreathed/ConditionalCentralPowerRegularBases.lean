module

public import CFSG.CharacterTheory.Wreathed.GeneralCentralTwoCoverRegularBasis
public import CFSG.CharacterTheory.Wreathed.ConditionalLocalHyp

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.Principal
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.ActualProjectiveLayer

universe u v

structure PrincipalRegularIntegralBasisData {E : Type u} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (Φ : E → ℂ) (ε : ℤ) (q : ℕ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  irreducible : ∃ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    (basis.representation l).character = Φ
  degree : Φ 1 = q
  coefficients : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    ∃ a b : ℤ, (∀ y : E, Odd (orderOf y) →
        (basis.representation χ).character y = a + b * Φ y) ∧
      0 ≤ b ∧ 0 ≤ a + b ∧ (basis.representation χ).character 1 = a + b * q ∧
      ∀ a' b' : ℤ, (∀ y : E, Odd (orderOf y) →
        (basis.representation χ).character y = a' + b' * Φ y) → a' = a ∧ b' = b
  linearIndependent :
    LinearIndependent ℤ ![oddRestriction (1 : E → ℂ), oddRestriction (1 + (ε : ℂ) • Φ)]
  span : Submodule.span ℤ {oddRestriction (1 : E → ℂ), oddRestriction (1 + (ε : ℂ) • Φ)} =
    oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
  rows : ∃ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (Fin 2) ℤ, ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddRestriction (basis.representation χ).character =
        D χ 0 • oddRestriction (1 : E → ℂ) + D χ 1 • oddRestriction (1 + (ε : ℂ) • Φ)
  gram : ∀ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (Fin 2) ℤ, (∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddRestriction (basis.representation χ).character =
        D χ 0 • oddRestriction (1 : E → ℂ) + D χ 1 • oddRestriction (1 + (ε : ℂ) • Φ)) →
      D.transpose * D = M

@[expose] def RegularRowCorrespondence {E E' : Type u} [Group E] [Fintype E] [Group E']
    [Fintype E'] (σ : E' →* E) (basis : FiniteIrreducibleCharacterBasis E)
    (basis' : FiniteIrreducibleCharacterBasis E') (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index) (principal' : basis'.index) (Φ : E → ℂ)
    (Φ' : E' → ℂ) (ε : ℤ) : Prop :=
  ∃ bij : coefficientBlock basis (localizedComplexIntegerRing ideal) principal ≃
      coefficientBlock basis' (localizedComplexIntegerRing ideal) principal',
    (∀ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis'.representation (bij θ)).character = (basis.representation θ).character ∘ σ) ∧
    (∀ (θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (a b : ℤ),
      (∀ y : E, Odd (orderOf y) →
        (basis.representation θ).character y = a + b * Φ y) ↔
      ∀ y : E', Odd (orderOf y) → (basis'.representation (bij θ)).character y = a + b * Φ' y) ∧
    ∀ (θ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (r₀ r₁ : ℤ),
      oddRestriction (basis.representation θ).character =
        r₀ • oddRestriction (1 : E → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • Φ) ↔
      oddRestriction (basis'.representation (bij θ)).character =
        r₀ • oddRestriction (1 : E' → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • Φ')

section Quotient

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem centralizerOddCoreQuotient_principal_regular_integral_basis_of_layerNoncyclic
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsyl : ∃ U : Sylow 2 (centralizerSimpleLayer n hn S e),
      ¬ IsCyclic (U : Subgroup (centralizerSimpleLayer n hn S e)))
    {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (sigmaGroup : Subgroup (F ≃+* F)) (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hρ : Function.Injective ρ)
    (hlayer : (centralizerSimpleLayer n hn S e).map ρ = specialLayer F)
    (hrange : ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    PrincipalRegularIntegralBasisData basis ideal principal
      (fun h => (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
        coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
      (if Nat.card F % 4 = 1 then 1 else -1) (Nat.card F)
      ((2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)]) := by
  let : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set τ := centralizerFullQuotientMap n hn S e with hτ
  set ψ : centralizerFullQuotient n hn S e →* Equiv.Perm (Omega F) :=
    (coordinateE F).subtype.comp ρ with hψdef
  have hψ : Function.Injective ψ := (coordinateE F).subtype_injective.comp hρ
  set Δ := ψ.range with hΔdef
  set πH : centralizerOddCoreQuotient n S e →* Δ := ψ.rangeRestrict.comp τ with hπHdef
  have hπH : Function.Surjective πH :=
    ψ.rangeRestrict_surjective.comp (centralizerFullQuotientMap_surjective n hn S e)
  have hker : πH.ker = centralizerFullCenterImage n hn S e := by
    rw [hπHdef, MonoidHom.ker_comp_of_injective _ _
      ((MonoidHom.rangeRestrict_injective_iff).mpr hψ)]
    exact QuotientGroup.ker_mk' _
  have hZ : πH.ker ≤ Subgroup.center (centralizerOddCoreQuotient n S e) := by
    rw [hker, centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e]
  have hZcard : Nat.card πH.ker = 2 ^ n := by
    rw [hker]
    exact centralizerFullCenterImage_card n hn S e
  have hZ2 : IsPGroup 2 πH.ker := IsPGroup.of_card hZcard
  have hDΔ : coordinateD F ≤ Δ := by
    intro d hd
    have hmem : (⟨d, coordinateD_le_E F hd⟩ : coordinateE F) ∈ ρ.range := by
      rw [hrange]
      exact Subgroup.mem_sup_left hd
    obtain ⟨γ, hγ⟩ := hmem
    exact ⟨γ, by rw [hψdef, MonoidHom.comp_apply, hγ]; rfl⟩
  have hΔE : Δ ≤ coordinateE F := by
    rintro _ ⟨γ, rfl⟩
    exact (ρ γ).2
  have hbij : Function.Bijective ψ.rangeRestrict :=
    ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hψ, ψ.rangeRestrict_surjective⟩
  have hS : ∃ T : Sylow 2 Δ,
      Nonempty ((T : Subgroup Δ) ≃* DihedralGroup (2 ^ ((n + 1) - 1))) := by
    refine ⟨(centralizerFullQuotientSylow n hn S e).mapSurjective
      (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective, ⟨?_⟩⟩
    rw [Sylow.coe_mapSurjective, show n + 1 - 1 = n by omega]
    exact ((MulEquiv.ofBijective ψ.rangeRestrict hbij).subgroupMap
      (centralizerFullQuotientSylow n hn S e : Subgroup _)).symm.trans
        (centralizerFullQuotientSylowEquiv n hn S e)
  have hG : ∃ T : Sylow 2 (coordinateG F), ¬ IsCyclic (T : Subgroup (coordinateG F)) := by
    obtain ⟨U, hU⟩ := hsyl
    let iso : centralizerSimpleLayer n hn S e ≃* coordinateG F :=
      (((centralizerSimpleLayer n hn S e).equivMapOfInjective ρ hρ).trans
        (MulEquiv.subgroupCongr hlayer)).trans
        (Subgroup.subgroupOfEquivOfLe ((coordinateG_le_D F).trans (coordinateD_le_E F)))
    refine ⟨U.mapSurjective (f := iso.toMonoidHom) iso.surjective, fun hcyc => hU ?_⟩
    exact (iso.subgroupMap (U : Subgroup (centralizerSimpleLayer n hn S e))).isCyclic.mpr hcyc
  obtain ⟨-, hΦ, hcoeff, hind, hspan, hrows, hgram⟩ :=
    general_central_two_cover_principal_regular_integral_basis hp (hp.odd_of_ne_two hpodd) hf F
      hcard Δ hDΔ hΔE (k := n + 1) (by omega) hS hG πH hπH hZ hZ2 basis ideal principal hprincipal
  have hΦ1 : (Nat.card {x : Omega F // ((ρ (τ 1) : coordinateE F) : Equiv.Perm (Omega F)) x = x} :
      ℂ) - 1 = Nat.card F := by
    have hfix : Nat.card {x : Omega F // ((ρ (τ 1) : coordinateE F) : Equiv.Perm (Omega F)) x =
        x} = Nat.card (Omega F) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by
      rw [map_one, map_one]
      rfl)
    rw [hfix, card_omega]
    push_cast
    ring
  refine ⟨hΦ, hΦ1, fun χ hχ => ?_, hind, hspan, hrows, fun D hD => ?_⟩
  · obtain ⟨a, b, hab, hb, hab0, huniq⟩ := hcoeff χ hχ
    refine ⟨a, b, hab, hb, hab0, ?_, huniq⟩
    have h1 := hab 1 (by rw [orderOf_one]; exact odd_one)
    rw [h1]
    congr 1
    exact congrArg _ hΦ1
  · rw [hgram D hD, hZcard, show n + 1 - 2 = n - 1 by omega,
      ← wreathed_two_pow_div_two n (by omega)]
    push_cast
    rfl

theorem centralizerOddCoreQuotient_principal_regular_integral_basis
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {p f : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (F : Type) [Field F] [Finite F] (hcard : Nat.card F = p ^ f)
    (sigmaGroup : Subgroup (F ≃+* F)) (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (hρ : Function.Injective ρ)
    (hlayer : (centralizerSimpleLayer n hn S e).map ρ = specialLayer F)
    (hrange : ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    PrincipalRegularIntegralBasisData basis ideal principal
      (fun h => (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) :
        coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1)
      (if Nat.card F % 4 = 1 then 1 else -1) (Nat.card F)
      ((2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)]) :=
  by
  obtain ⟨-, -, -, -, -, hSylow, -⟩ :=
    centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  let U : Sylow 2 (centralizerSimpleLayer n hn S e) := Classical.choice Sylow.nonempty
  obtain ⟨eU⟩ := hSylow U
  exact centralizerOddCoreQuotient_principal_regular_integral_basis_of_layerNoncyclic n hn S e
    ⟨U, dihedral_sylow_not_isCyclic n hn eU⟩ hp hpodd hf F hcard sigmaGroup ρ hρ hlayer hrange
    ideal basis principal hprincipal

end Quotient

section Transport

variable {E H : Type u} [Group E] [Fintype E] [Group H] [Fintype H]

omit [Fintype E] [Fintype H] in
theorem forall_odd_iff_of_surjective (σ : E →* H) (hσ : Function.Surjective (oddElementsMap σ))
    (P : H → Prop) :
    (∀ z : H, Odd (orderOf z) → P z) ↔ ∀ y : E, Odd (orderOf y) → P (σ y) := by
  constructor
  · intro h y hy
    exact h (σ y) (hy.of_dvd_nat (orderOf_map_dvd σ y))
  · intro h z hz
    obtain ⟨y, hy⟩ := hσ ⟨z, hz⟩
    have hyz : σ y.1 = z := congrArg Subtype.val hy
    have := h y.1 y.2
    rwa [hyz] at this

theorem principalRegularIntegralBasisData_comp (σ : E →* H) (hσ : Function.Surjective σ)
    (hodd : Odd (Nat.card σ.ker)) (basisE : FiniteIrreducibleCharacterBasis E)
    (basisH : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principalE : basisE.index) (principalH : basisH.index)
    (bij : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ≃
      coefficientBlock basisE (localizedComplexIntegerRing ideal) principalE)
    (hbij : ∀ θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisE.representation (bij θ)).character = (basisH.representation θ).character ∘ σ)
    {Φ : H → ℂ} {ε : ℤ} {q : ℕ} {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hH : PrincipalRegularIntegralBasisData basisH ideal principalH Φ ε q M) :
    PrincipalRegularIntegralBasisData basisE ideal principalE (fun y => Φ (σ y)) ε q M ∧
      RegularRowCorrespondence σ basisH basisE ideal principalH principalE Φ
        (fun y => Φ (σ y)) ε := by
  have hsurj := oddElementsMap_surjective σ hσ hodd
  have hinj : Function.Injective (oddPullback σ) := oddPullback_injective σ hσ hodd
  have hab : ∀ (θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)
      (a b : ℤ), (∀ y : H, Odd (orderOf y) →
      (basisH.representation θ).character y = a + b * Φ y) ↔
      ∀ y : E, Odd (orderOf y) → (basisE.representation (bij θ)).character y = a + b * Φ (σ y) := by
    intro θ a b
    rw [hbij θ]
    exact forall_odd_iff_of_surjective σ hsurj _
  have hrow : ∀ (θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH)
      (r₀ r₁ : ℤ), oddRestriction (basisH.representation θ).character =
      r₀ • oddRestriction (1 : H → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • Φ) ↔
      oddRestriction (basisE.representation (bij θ)).character =
        r₀ • oddRestriction (1 : E → ℂ) + r₁ • oddRestriction (1 + (ε : ℂ) • fun y => Φ (σ y)) := by
    intro θ r₀ r₁
    rw [oddRestriction_eq_zsmul_add_iff, oddRestriction_eq_zsmul_add_iff, hbij θ]
    exact forall_odd_iff_of_surjective σ hsurj _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, bij, hbij, hab, hrow⟩
  · obtain ⟨l, hl, hlΦ⟩ := hH.irreducible
    refine ⟨bij ⟨l, hl⟩, (bij ⟨l, hl⟩).2, ?_⟩
    rw [hbij, hlΦ]
    rfl
  · rw [map_one]
    exact hH.degree
  · intro χ hχ
    set θ := bij.symm ⟨χ, hχ⟩ with hθ
    have hbijθ : bij θ = ⟨χ, hχ⟩ := bij.apply_symm_apply _
    obtain ⟨a, b, habθ, hb, hab0, h1, huniq⟩ := hH.coefficients θ θ.2
    have hχθ : (basisE.representation χ).character = (basisH.representation θ).character ∘ σ := by
      have := hbij θ
      rwa [hbijθ] at this
    refine ⟨a, b, ?_, hb, hab0, ?_, fun a' b' h' => huniq a' b' ?_⟩
    · have := (hab θ a b).mp habθ
      rwa [hbijθ] at this
    · rw [hχθ]
      change (basisH.representation θ).character (σ 1) = _
      rw [map_one]
      exact h1
    · refine (hab θ a' b').mpr ?_
      rwa [hbijθ]
  · have h := hH.linearIndependent.map' (oddPullback σ) (LinearMap.ker_eq_bot.mpr hinj)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  · have himage : (oddPullback σ) '' {oddRestriction (1 : H → ℂ),
        oddRestriction (1 + (ε : ℂ) • Φ)} = {oddRestriction (1 : E → ℂ),
          oddRestriction (1 + (ε : ℂ) • fun y => Φ (σ y))} := by
      rw [Set.image_pair]
      rfl
    rw [← himage, ← Submodule.map_span, hH.span]
    exact oddRestrictionLattice_map_oddPullback σ basisE basisH _ _ bij hbij
  · obtain ⟨D, hD⟩ := hH.rows
    refine ⟨fun χ j => D (bij.symm χ) j, fun χ => ?_⟩
    have := (hrow (bij.symm χ) _ _).mp (hD (bij.symm χ))
    rwa [bij.apply_symm_apply] at this
  · intro D hD
    have hDH := hH.gram (fun θ j => D (bij θ) j) fun θ => (hrow θ _ _).mpr (hD (bij θ))
    rw [← hDH]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact (Equiv.sum_comp bij fun χ => D χ i * D χ j).symm

theorem regularRowCorrespondence_restriction {N C : Type u} [Group N] [Fintype N] [Group C]
    [Fintype C] (σN : N →* H) (ι : C →* N)
    (hσN : Function.Surjective (oddElementsMap σN))
    (hσC : Function.Surjective (oddElementsMap (σN.comp ι)))
    (basisH : FiniteIrreducibleCharacterBasis H) (basisN : FiniteIrreducibleCharacterBasis N)
    (basisC : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principalH : basisH.index) (principalN : basisN.index)
    (principalC : basisC.index)
    (bijN : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ≃
      coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN)
    (hbijN : ∀ θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisN.representation (bijN θ)).character = (basisH.representation θ).character ∘ σN)
    (bijC : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH ≃
      coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
    (hbijC : ∀ θ : coefficientBlock basisH (localizedComplexIntegerRing ideal) principalH,
      (basisC.representation (bijC θ)).character =
        (basisH.representation θ).character ∘ (σN.comp ι))
    (ρ : coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN ≃
      coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)
    (hρ : ∀ χ : coefficientBlock basisN (localizedComplexIntegerRing ideal) principalN,
      (basisC.representation (ρ χ)).character = (basisN.representation χ).character ∘ ι)
    (hρbij : ∀ θ, ρ (bijN θ) = bijC θ) (Φ : H → ℂ) (ε : ℤ) :
    RegularRowCorrespondence ι basisN basisC ideal principalN principalC (fun y => Φ (σN y))
      (fun c => Φ (σN (ι c))) ε := by
  refine ⟨ρ, hρ, fun χ a b => ?_, fun χ r₀ r₁ => ?_⟩
  · obtain ⟨θ, rfl⟩ := bijN.surjective χ
    rw [hρbij, hbijN θ, hbijC θ]
    exact (forall_odd_iff_of_surjective σN hσN
      (fun z => (basisH.representation θ).character z = a + b * Φ z)).symm.trans
        (forall_odd_iff_of_surjective (σN.comp ι) hσC _)
  · obtain ⟨θ, rfl⟩ := bijN.surjective χ
    rw [hρbij, oddRestriction_eq_zsmul_add_iff, oddRestriction_eq_zsmul_add_iff, hbijN θ, hbijC θ]
    exact (forall_odd_iff_of_surjective σN hσN
      (fun z => (basisH.representation θ).character z = r₀ * (1 : H → ℂ) z +
        r₁ * (1 + (ε : ℂ) • Φ) z)).symm.trans
        (forall_odd_iff_of_surjective (σN.comp ι) hσC _)

end Transport

section Assembly

variable {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]

omit [IsSimpleGroup G] in
theorem conditional_actual_central_power_principal_regular_integral_bases_of_localHyp
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hloc : ConditionalLocalHyp n hn S e p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index) (hprincipalN : (basisN.representation principalN).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (sigmaGroup : Subgroup (F ≃+* F))
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f ∧ Odd (Nat.card sigmaGroup) ∧ Function.Injective ρ ∧
        (centralizerSimpleLayer n hn S e).map ρ = specialLayer F ∧
        ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup) ∧
    ∀ (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f → Odd (Nat.card sigmaGroup) → Function.Injective ρ →
      (centralizerSimpleLayer n hn S e).map ρ = specialLayer F →
      ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup →
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : involutionCentralizer n S e → ℂ := fun y => ΦH (centralizerOddCoreMap n S e y)
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let M : Matrix (Fin 2) (Fin 2) ℤ := (2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)]
      PrincipalRegularIntegralBasisData basisH ideal principalH ΦH ε (Nat.card F) M ∧
      PrincipalRegularIntegralBasisData basisN ideal principalN ΦN ε (Nat.card F) M ∧
      RegularRowCorrespondence (centralizerOddCoreMap n S e) basisH basisN ideal principalH
        principalN ΦH ΦN ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index),
        (basisC.representation principalC).character = 1 →
        let ι := Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        PrincipalRegularIntegralBasisData basisC ideal principalC (fun c => ΦN (ι c)) ε
          (Nat.card F) M ∧
        RegularRowCorrespondence ι basisN basisC ideal principalN principalC ΦN
          (fun c => ΦN (ι c)) ε := by
  refine ⟨?_, ?_⟩
  · obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ := hloc.modelData
    exact ⟨F, hfield, hfinite, Sigma, ρ, hdata.card, hdata.sigma_odd, hdata.rho_injective,
      hdata.rho_layer, hdata.rho_range⟩
  · intro F _ _ sigmaGroup ρ hcard _ hρ hlayer hrange ΦH ΦN ε M
    have hH := centralizerOddCoreQuotient_principal_regular_integral_basis_of_layerNoncyclic n hn
      S e hloc.layerNoncyclic hp hpodd hf F hcard sigmaGroup ρ hρ hlayer hrange ideal basisH
      principalH hprincipalH
    have hπN : Function.Surjective (centralizerOddCoreMap n S e) :=
      centralizerOddCoreMap_surjective n S e
    have hRodd : Odd (Nat.card (centralizerOddCoreMap n S e).ker) := by
      rw [show (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e from
        QuotientGroup.ker_mk' _]
      exact centralizerOddCore_card_odd n S e
    obtain ⟨hN1, -, -, -⟩ := normal_prime_kernel_principal_block_inflation_of_surjective
      (centralizerOddCoreMap n S e) hπN basisN ideal 2 hRodd.not_two_dvd_nat basisH principalN
      hprincipalN principalH hprincipalH
    obtain ⟨bijN, hbijN⟩ := exists_inflation_equiv (centralizerOddCoreMap n S e) hπN basisN basisH
      _ _ hN1
    obtain ⟨hNdata, hNcorr⟩ := principalRegularIntegralBasisData_comp
      (centralizerOddCoreMap n S e) hπN hRodd basisN basisH ideal principalN principalH bijN hbijN
      hH
    refine ⟨hH, hNdata, hNcorr, fun j hj basisC principalC hprincipalC => ?_⟩
    have hdata := central_sylow_powers_share_odd_quotient_and_principal_block.{0, v} n hn S e j hj
      ideal basisN basisH basisC principalN hprincipalN principalH hprincipalH principalC
      hprincipalC
    obtain ⟨bijN', bijC, ρj, -, -, -, hbijN', hbijC, hρj, -, -, hρbij, -⟩ := hdata.correspondence
    have hπj := hdata.map_surjective
    have hRjodd : Odd (Nat.card (centralSylowPowerMap n hn S e j hj).ker) := by
      rw [hdata.map_ker]
      exact weakClosure_oddCore_card _
    obtain ⟨hCdata, -⟩ := principalRegularIntegralBasisData_comp
      (centralSylowPowerMap n hn S e j hj) hπj hRjodd basisC basisH ideal principalC principalH
      bijC hbijC hH
    exact ⟨hdata, hCdata, regularRowCorrespondence_restriction (centralizerOddCoreMap n S e)
      (Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj))
      (oddElementsMap_surjective _ hπN hRodd) (oddElementsMap_surjective _ hπj hRjodd) basisH
      basisN basisC ideal principalH principalN principalC bijN' hbijN' bijC hbijC ρj hρj hρbij
      ΦH ε⟩

theorem conditional_actual_central_power_principal_regular_integral_bases
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    [Fintype (centralizerOddCoreQuotient n S e)] (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basisH : FiniteIrreducibleCharacterBasis (centralizerOddCoreQuotient n S e))
    (principalH : basisH.index) (hprincipalH : (basisH.representation principalH).character = 1)
    (basisN : FiniteIrreducibleCharacterBasis (involutionCentralizer n S e))
    (principalN : basisN.index) (hprincipalN : (basisN.representation principalN).character = 1) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F) (sigmaGroup : Subgroup (F ≃+* F))
        (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f ∧ Odd (Nat.card sigmaGroup) ∧ Function.Injective ρ ∧
        (centralizerSimpleLayer n hn S e).map ρ = specialLayer F ∧
        ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup) ∧
    ∀ (F : Type) [Field F] [Finite F] (sigmaGroup : Subgroup (F ≃+* F))
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F),
      Nat.card F = p ^ f → Odd (Nat.card sigmaGroup) → Function.Injective ρ →
      (centralizerSimpleLayer n hn S e).map ρ = specialLayer F →
      ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F sigmaGroup →
      let ΦH : centralizerOddCoreQuotient n S e → ℂ := fun h =>
        (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e h) : coordinateE F) :
          Equiv.Perm (Omega F)) x = x} : ℂ) - 1
      let ΦN : involutionCentralizer n S e → ℂ := fun y => ΦH (centralizerOddCoreMap n S e y)
      let ε : ℤ := if Nat.card F % 4 = 1 then 1 else -1
      let M : Matrix (Fin 2) (Fin 2) ℤ := (2 ^ n : ℤ) • !![4, -2; -2, ((2 ^ n / 2 + 1 : ℕ) : ℤ)]
      PrincipalRegularIntegralBasisData basisH ideal principalH ΦH ε (Nat.card F) M ∧
      PrincipalRegularIntegralBasisData basisN ideal principalN ΦN ε (Nat.card F) M ∧
      RegularRowCorrespondence (centralizerOddCoreMap n S e) basisH basisN ideal principalH
        principalN ΦH ΦN ε ∧
      ∀ (j : ℤ) (hj : ¬ ((2 ^ n : ℕ) : ℤ) ∣ j)
        (basisC : FiniteIrreducibleCharacterBasis (centralSylowPowerCentralizer n S e j))
        (principalC : basisC.index),
        (basisC.representation principalC).character = 1 →
        let ι := Subgroup.inclusion (centralizer_zpow_le_involutionCentralizer n hn S e j hj)
        CentralSylowPowerQuotientData.{0, v} n hn S e j hj ideal basisN basisH basisC principalN
          principalH principalC ∧
        PrincipalRegularIntegralBasisData basisC ideal principalC (fun c => ΦN (ι c)) ε
          (Nat.card F) M ∧
        RegularRowCorrespondence ι basisN basisC ideal principalN principalC ΦN
          (fun c => ΦN (ι c)) ε :=
  conditional_actual_central_power_principal_regular_integral_bases_of_localHyp n hn S e p f hp
    hpodd hf (ConditionalLocalHyp.of_isSimpleGroup hnonab n hn S e hfour p f hp hpodd hf hmodel)
    ideal basisH principalH hprincipalH basisN principalN hprincipalN

end Assembly

end CFSG.Wreathed
