module

public import CFSG.CharacterTheory.Wreathed.FourPointPrincipalOrderScalar
public import CFSG.CharacterTheory.Wreathed.PrincipalSectionColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.TwoRankLowerBound.Helpers

theorem principal_character_one_on_odd_of_comm {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsMulCommutative (C ⧸ N)]
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {c : C} (hc : Odd (orderOf c)) : (basis.representation χ).character c = 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨data, hirr, hchar⟩ :=
    (CFSG.LyonsUnitaryFour.normal_p_complement_principal_block basis ideal 2 principal
      hprincipal N (Nat.coprime_two_left.mpr hN) hquotient).2.1 χ |>.mp hχ
  let : data.representation.IsIrreducible := hirr
  have hd := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative data.representation
  rw [hchar, Function.comp_apply, CFSG.Semidihedral.Principal.hom_eq_one_of_odd_orderOf hquotient
    (QuotientGroup.mk' N) c hc]
  change data.representation.character 1 = 1
  rw [Representation.char_one, hd, Nat.cast_one]

theorem principal_singleton_integral_basis_of_comm {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsMulCommutative (C ⧸ N)] :
    (∀ _ : Fin 1, ∃ c : basis.index → ℂ, ∀ y : C, ¬ 2 ∣ orderOf y →
      (1 : ℂ) = ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        c θ * (basis.representation θ).character y) ∧
    (∀ c : Fin 1 → ℂ, (∀ y : C, ¬ 2 ∣ orderOf y → ∑ j : Fin 1, c j * (1 : ℂ) = 0) →
      c = 0) ∧
    (∀ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ y : C, ¬ 2 ∣ orderOf y →
        (basis.representation θ).character y = ∑ _ : Fin 1, ((1 : ℤ) : ℂ) * 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    refine ⟨fun θ => if θ = principal then 1 else 0, fun y _ => ?_⟩
    rw [Finset.sum_eq_single principal]
    · simp only [ite_true, one_mul, hprincipal, Pi.one_apply]
    · intro θ _ hθ
      simp only [hθ, ite_false, zero_mul]
    · exact fun h => (h (coefficientBlock_self_mem basis _ principal)).elim
  · intro c hc
    have h0 := hc 1 (by norm_num)
    simp only [Fin.sum_univ_one, mul_one] at h0
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj, Pi.zero_apply] using h0
  · intro θ hθ y hy
    rw [principal_character_one_on_odd_of_comm basis ideal principal hprincipal N hN hquotient hθ
      (Nat.coprime_two_left.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hy))]
    simp

theorem card_index_of_comm {Q : Type} [Group Q] [Fintype Q] [IsMulCommutative Q]
    (basisQ : FiniteIrreducibleCharacterBasis Q) : Fintype.card basisQ.index = Nat.card Q := by
  have h := finiteIrreducibleCharacterBasis_sum_finrank_sq basisQ
  have h1 : ∀ l, Module.finrank ℂ (basisQ.representation l).vector = 1 := fun l => by
    let : (basisQ.representation l).representation.IsIrreducible := basisQ.irreducible l
    exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      (basisQ.representation l).representation
  simp only [h1, one_pow, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  exact h

theorem card_principal_block_of_comm {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsMulCommutative (C ⧸ N)] :
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).card =
      Nat.card (C ⧸ N) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hblock := CFSG.LyonsUnitaryFour.normal_p_complement_principal_block basis ideal 2
    principal hprincipal N (Nat.coprime_two_left.mpr hN) hquotient
  let basisQ : FiniteIrreducibleCharacterBasis (C ⧸ N) :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  have hB : ∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ θ : basisQ.index, (basis.representation χ).character =
        (basisQ.representation θ).character ∘ QuotientGroup.mk' N := by
    intro χ
    rw [hblock.2.1 χ]
    constructor
    · rintro ⟨data, hirr, hchar⟩
      obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisQ data hirr
      exact ⟨θ, by rw [hchar, hθ]⟩
    · rintro ⟨θ, hθ⟩
      exact ⟨basisQ.representation θ, basisQ.irreducible θ, hθ⟩
  have hB' : ∀ θ : basisQ.index, ∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal)
      principal, (basis.representation χ).character =
        (basisQ.representation θ).character ∘ QuotientGroup.mk' N := fun θ =>
    hblock.2.2 (basisQ.representation θ) (basisQ.irreducible θ)
  have hsum := CFSG.Wreathed.FourPointPrincipalOrderScalar.sum_inflated_block basis basisQ
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) _ hB hB' (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at hsum
  rw [card_index_of_comm basisQ] at hsum
  exact_mod_cast hsum

theorem abelian_section_value_column {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {u : G} {r : ℕ} (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r)
    (N : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) [N.Normal]
    (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N))
    [IsMulCommutative ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N)] :
    (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        conj ((basis.representation χ).character u) * (basis.representation χ).character u =
      Nat.card ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N)) ∧
    ∀ g : G, (∀ a c : G, a * c = g → Commute a c →
      (∃ e : ℕ, orderOf a = 2 ^ e) → ¬ 2 ∣ orderOf c → ¬ IsConj a u) →
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character u *
          conj ((basis.representation χ).character g) = 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ (2 ^ r)
  let localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers u : Set G)) :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hbmem, hbindep, hd⟩ := principal_singleton_integral_basis_of_comm localBasis ideal
    localPrincipal hlocalPrincipal N hN hquotient
  obtain ⟨U, m, lam, _, _, _, _, hvalues, _, hgram, hoff⟩ :=
    CFSG.Wreathed.principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal
      hprincipal hr hu localBasis localPrincipal hlocalPrincipal hζ 1 (by omega)
      (fun _ _ => 1) hbmem hbindep (fun _ _ => 1) hd
  have hU : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      U χ 0 = (basis.representation χ).character u := by
    intro χ hχ
    simpa using (hvalues χ hχ 1 (by norm_num)).symm
  refine ⟨?_, fun g hg => ?_⟩
  · have h := hgram 0 0
    rw [Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]] at h
    rw [h]
    simp only [mul_one, Int.cast_one, Finset.sum_const, nsmul_eq_mul]
    rw [card_principal_block_of_comm localBasis ideal localPrincipal hlocalPrincipal N hN
      hquotient]
  · have h := hoff g hg 0
    rwa [Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]] at h

end CFSG.Wreathed.ConditionalGeneralBase
