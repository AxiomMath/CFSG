module

public import CFSG.CharacterTheory.Wreathed.CompatibleCentralizerLinearFamily
public import CFSG.CharacterTheory.Wreathed.ConditionalCentralPowerRegularBases
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseSections

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.CompatibleFamily

universe u

structure TwistedRegularIntegralBasisData {E : Type u} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (lamLabel : basis.index) (lam Φ : E → ℂ) (ε : ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) : Prop where
  linearIndependent :
    LinearIndependent ℤ ![oddRestriction lam, oddRestriction (lam * (1 + (ε : ℂ) • Φ))]
  span : Submodule.span ℤ {oddRestriction lam, oddRestriction (lam * (1 + (ε : ℂ) • Φ))} =
    oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
  rows : ∃ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
      (Fin 2) ℤ, ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
        oddRestriction (basis.representation χ).character =
        D χ 0 • oddRestriction lam + D χ 1 • oddRestriction (lam * (1 + (ε : ℂ) • Φ))
  gram : ∀ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
      (Fin 2) ℤ, (∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
        oddRestriction (basis.representation χ).character =
        D χ 0 • oddRestriction lam + D χ 1 • oddRestriction (lam * (1 + (ε : ℂ) • Φ))) →
      D.transpose * D = M

structure SingletonTwistedBasisData {E : Type u} [Group E] [Fintype E]
    (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (lamLabel : basis.index) (lam : E → ℂ) (c : ℕ) : Prop where
  linearIndependent : LinearIndependent ℤ ![oddRestriction lam]
  span : Submodule.span ℤ {oddRestriction lam} =
    oddRestrictionLattice basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
  restriction : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
    oddRestriction (basis.representation χ).character = oddRestriction lam
  card : (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel).card = c
  rows : ∃ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
      (Fin 1) ℤ, ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
        oddRestriction (basis.representation χ).character = D χ 0 • oddRestriction lam
  gram : ∀ D : Matrix (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
      (Fin 1) ℤ, (∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
        oddRestriction (basis.representation χ).character = D χ 0 • oddRestriction lam) →
      (∀ χ, D χ 0 = 1) ∧ D.transpose * D = !![(c : ℤ)]

namespace FlatTwistedBases

variable {E : Type u} [Group E]

@[expose] noncomputable def oddTwist (lam : E →* ℂˣ) :
    (OddElements E → ℂ) →ₗ[ℤ] (OddElements E → ℂ) where
  toFun f g := (lam g.1 : ℂ) * f g
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, mul_add]
  map_smul' k f := by
    funext g
    simp only [Pi.smul_apply, zsmul_eq_mul, eq_intCast, Int.cast_id]
    ring

theorem oddTwist_apply (lam : E →* ℂˣ) (f : OddElements E → ℂ) (g : OddElements E) :
    oddTwist lam f g = (lam g.1 : ℂ) * f g := rfl

theorem oddTwist_injective (lam : E →* ℂˣ) : Function.Injective (oddTwist lam) := by
  intro f f' h
  funext g
  have hg := congrFun h g
  rw [oddTwist_apply, oddTwist_apply] at hg
  exact mul_left_cancel₀ (lam g.1).ne_zero hg

theorem oddTwist_oddRestriction (lam : E →* ℂˣ) (φ : E → ℂ) :
    oddTwist lam (oddRestriction φ) = oddRestriction ((fun k => (lam k : ℂ)) * φ) := rfl

@[expose] def oddOne (E : Type u) [Group E] : OddElements E :=
  ⟨1, by rw [orderOf_one]; exact odd_one⟩

theorem oddRestriction_linear_ne_zero (lam : E →* ℂˣ) :
    oddRestriction (fun k => (lam k : ℂ)) ≠ 0 := by
  intro h
  have h1 := congrFun h (oddOne E)
  simp only [oddRestriction, oddOne, map_one, Units.val_one, Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem zsmul_oddRestriction_linear_eq (lam : E →* ℂˣ) {r : ℤ}
    (h : r • oddRestriction (fun k => (lam k : ℂ)) = oddRestriction (fun k => (lam k : ℂ))) :
    r = 1 := by
  have h1 := congrFun h (oddOne E)
  simp only [Pi.smul_apply, oddRestriction, oddOne, map_one, Units.val_one, zsmul_eq_mul,
    mul_one] at h1
  exact_mod_cast h1

variable [Fintype E]

theorem exists_twist_equiv (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (lam : E →* ℂˣ)
    (lamLabel principal : basis.index)
    (hlam : ∀ k, (basis.representation lamLabel).character k = lam k)
    (hprincipal : (basis.representation principal).character = 1) :
    ∃ τ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal ≃
        coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
      ∀ χ k, (basis.representation (τ χ)).character k =
        (lam k : ℂ) * (basis.representation χ).character k := by
  have hblock := linear_block_eq_twist_principal basis ideal lam lamLabel principal hlam
    hprincipal
  have hlift : ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ θ : coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
        ∀ k, (basis.representation θ).character k =
          (lam k : ℂ) * (basis.representation χ).character k := by
    intro χ
    obtain ⟨θ, hθ⟩ := exists_twisted_label basis lam χ
    exact ⟨⟨θ, (hblock θ).mpr ⟨χ, χ.2, hθ⟩⟩, hθ⟩
  choose τ hτ using hlift
  have hinj : Function.Injective τ := by
    intro χ χ' h
    apply Subtype.ext
    apply basis.distinct
    funext k
    have h1 := hτ χ k
    have h2 := hτ χ' k
    rw [h] at h1
    exact mul_left_cancel₀ (lam k).ne_zero (h1.symm.trans h2)
  have hsurj : Function.Surjective τ := by
    intro θ
    obtain ⟨χ, hχ, hθχ⟩ := (hblock θ).mp θ.2
    refine ⟨⟨χ, hχ⟩, Subtype.ext (basis.distinct ?_)⟩
    funext k
    change (basis.representation (τ ⟨χ, hχ⟩ : basis.index)).character k =
      (basis.representation θ).character k
    rw [hτ, hθχ]
  exact ⟨Equiv.ofBijective τ ⟨hinj, hsurj⟩, hτ⟩

theorem oddRestrictionLattice_map_oddTwist (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (lam : E →* ℂˣ)
    (lamLabel principal : basis.index)
    (τ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal ≃
        coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel)
    (hτ : ∀ χ k, (basis.representation (τ χ)).character k =
        (lam k : ℂ) * (basis.representation χ).character k) :
    (oddRestrictionLattice basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)).map
        (oddTwist lam) =
      oddRestrictionLattice basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel) := by
  have hL : ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      oddTwist lam (oddRestriction (basis.representation χ).character) =
        oddRestriction (basis.representation (τ χ)).character := by
    intro χ
    funext g
    rw [oddTwist_apply]
    exact (hτ χ g.1).symm
  rw [oddRestrictionLattice, oddRestrictionLattice, Submodule.map_span]
  congr 1
  ext φ
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨_, ⟨χ, hχ, rfl⟩, rfl⟩
    exact ⟨(τ ⟨χ, hχ⟩ : basis.index), (τ ⟨χ, hχ⟩).2, (hL ⟨χ, hχ⟩).symm⟩
  · rintro ⟨θ, hθ, rfl⟩
    obtain ⟨χ, hχ⟩ := τ.surjective ⟨θ, hθ⟩
    refine ⟨_, ⟨χ, χ.2, rfl⟩, ?_⟩
    rw [hL χ, hχ]

theorem twistedRegularIntegralBasisData_of_principal (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (lam : E →* ℂˣ)
    (lamLabel principal : basis.index)
    (hlam : ∀ k, (basis.representation lamLabel).character k = lam k)
    (hprincipal : (basis.representation principal).character = 1) {Φ : E → ℂ} {ε : ℤ} {q : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℤ}
    (hdata : PrincipalRegularIntegralBasisData basis ideal principal Φ ε q M) :
    TwistedRegularIntegralBasisData basis ideal lamLabel (fun k => (lam k : ℂ)) Φ ε M := by
  obtain ⟨τ, hτ⟩ := exists_twist_equiv basis ideal lam lamLabel principal hlam hprincipal
  have hL0 : oddTwist lam (oddRestriction (1 : E → ℂ)) =
      oddRestriction (fun k => (lam k : ℂ)) := by
    funext g
    rw [oddTwist_apply]
    simp only [oddRestriction, Pi.one_apply, mul_one]
  have hL1 : oddTwist lam (oddRestriction (1 + (ε : ℂ) • Φ)) =
      oddRestriction ((fun k => (lam k : ℂ)) * (1 + (ε : ℂ) • Φ)) := rfl
  have hLχ : ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      oddTwist lam (oddRestriction (basis.representation χ).character) =
        oddRestriction (basis.representation (τ χ)).character := by
    intro χ
    funext g
    rw [oddTwist_apply]
    exact (hτ χ g.1).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hdata.linearIndependent.map' (oddTwist lam)
      (LinearMap.ker_eq_bot.mpr (oddTwist_injective lam))
    convert h using 1
    funext i
    fin_cases i
    · exact hL0.symm
    · exact hL1.symm
  · rw [← hL0, ← hL1, ← Set.image_pair, ← Submodule.map_span, hdata.span]
    exact oddRestrictionLattice_map_oddTwist basis ideal lam lamLabel principal τ hτ
  · obtain ⟨D, hD⟩ := hdata.rows
    refine ⟨fun θ j => D (τ.symm θ) j, fun θ => ?_⟩
    have h := congrArg (oddTwist lam) (hD (τ.symm θ))
    rw [hLχ, Equiv.apply_symm_apply, map_add, map_zsmul, map_zsmul, hL0, hL1] at h
    exact h
  · intro D hD
    have hrows : ∀ χ : coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddRestriction (basis.representation χ).character =
          D (τ χ) 0 • oddRestriction (1 : E → ℂ) +
            D (τ χ) 1 • oddRestriction (1 + (ε : ℂ) • Φ) := by
      intro χ
      apply oddTwist_injective lam
      rw [hLχ, map_add, map_zsmul, map_zsmul, hL0, hL1]
      exact hD (τ χ)
    rw [← hdata.gram (fun χ j => D (τ χ) j) hrows]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact (Equiv.sum_comp τ fun θ => D θ i * D θ j).symm

theorem singletonTwistedBasisData_of_comm {D : Type} [Group D] [Fintype D]
    (basis : FiniteIrreducibleCharacterBasis D) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (lam : D →* ℂˣ)
    (lamLabel : basis.index) (hlam : ∀ k, (basis.representation lamLabel).character k = lam k)
    (N : Subgroup D) [N.Normal] (hN : Odd (Nat.card N)) (hquotient : IsPGroup 2 (D ⧸ N))
    [IsMulCommutative (D ⧸ N)] :
    SingletonTwistedBasisData basis ideal lamLabel (fun k => (lam k : ℂ)) (Nat.card (D ⧸ N)) := by
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation D) (principalFiniteComplexRepresentation_isIrreducible D)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨τ, hτ⟩ := exists_twist_equiv basis ideal lam lamLabel principal hlam hprincipal
  have hres : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel,
      oddRestriction (basis.representation χ).character =
        oddRestriction (fun k => (lam k : ℂ)) := by
    intro χ hχ
    obtain ⟨θ, hθ⟩ := τ.surjective ⟨χ, hχ⟩
    funext g
    change (basis.representation χ).character g.1 = (lam g.1 : ℂ)
    have h := hτ θ g.1
    rw [hθ] at h
    change (basis.representation χ).character g.1 = _ at h
    rw [h, ConditionalGeneralBase.principal_character_one_on_odd_of_comm basis ideal principal
      hprincipal N hN hquotient θ.2 g.2, mul_one]
  have hcard : (coefficientBlock basis (localizedComplexIntegerRing ideal) lamLabel).card =
      Nat.card (D ⧸ N) := by
    rw [← ConditionalGeneralBase.card_principal_block_of_comm basis ideal principal hprincipal N
      hN hquotient, ← Fintype.card_coe, ← Fintype.card_coe]
    exact (Fintype.card_congr τ).symm
  refine ⟨linearIndependent_unique_iff.mpr (oddRestriction_linear_ne_zero lam), ?_, hres,
    hcard, ⟨fun _ _ => 1, fun χ => by rw [one_zsmul]; exact hres χ χ.2⟩, ?_⟩
  · rw [oddRestrictionLattice]
    congr 1
    ext φ
    simp only [Set.mem_singleton_iff, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro rfl
      exact ⟨lamLabel, coefficientBlock_self_mem basis _ lamLabel, hres _
        (coefficientBlock_self_mem basis _ lamLabel)⟩
    · rintro ⟨χ, hχ, rfl⟩
      exact hres χ hχ
  · intro Dm hDm
    have hone : ∀ χ, Dm χ 0 = 1 := fun χ =>
      zsmul_oddRestriction_linear_eq lam ((hDm χ).symm.trans (hres χ χ.2))
    refine ⟨hone, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hone, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_coe, hcard, nsmul_eq_mul, Fin.zero_eta, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.empty_val']

end FlatTwistedBases

end CFSG.Wreathed
