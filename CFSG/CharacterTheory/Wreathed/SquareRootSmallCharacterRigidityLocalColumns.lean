module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityActualColumns
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCentralProduct
public import CFSG.CharacterTheory.BrauerBlocksColumnRelation

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem cyclic_two_quotient_principal_card {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsCyclic (C ⧸ N)] :
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).card = N.index := by
  have hsum := (CFSG.BrauerBlocks.brauer_blocks_nonreal_involution_column_relation
    basis ideal principal hprincipal).2.1 N hN hquotient |>.2.2.1
  have hdeg : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character 1 = 1 :=
    fun χ hχ => principal_character_one_on_odd basis ideal principal hprincipal N hN
      hquotient hχ (by simp)
  have hcard :
      ((coefficientBlock basis (localizedComplexIntegerRing ideal) principal).card : ℂ) =
        (N.index : ℂ) := by
    calc
      _ = ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation χ).character 1 ^ 2 := by
        calc
          _ = ∑ _χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
              (1 : ℂ) := by simp
          _ = _ := Finset.sum_congr rfl fun χ hχ => by rw [hdeg χ hχ]; simp
      _ = _ := hsum
  exact_mod_cast hcard

theorem cyclic_two_quotient_singleton_gram {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsCyclic (C ⧸ N)] :
    ∑ _χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (((1 : ℤ) * 1 : ℤ) : ℂ) = (N.index : ℂ) := by
  simp only [mul_one, Int.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one,
    cyclic_two_quotient_principal_card basis ideal principal hprincipal N hN hquotient]

theorem cyclic_two_principal_column_values_norm {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {u : G} {r : ℕ} (hr : 1 ≤ r) (hu : orderOf u = 2 ^ r)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (N : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) [N.Normal]
    (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N))
    [IsCyclic ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N)] :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ v : Subgroup.centralizer (Subgroup.zpowers u : Set G), Odd (orderOf v) →
        (basis.representation χ).character (u * v) = (basis.representation χ).character u) ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        starRingEnd ℂ ((basis.representation χ).character u) *
          (basis.representation χ).character u = (N.index : ℂ) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ (2 ^ r)
  obtain ⟨hbmem, hbindep, hd⟩ := principal_singleton_integral_basis localBasis ideal
    localPrincipal hlocalPrincipal N hN hquotient
  obtain ⟨U, _, _, _, _, _, _, hvalues, _, hgram, _⟩ :=
    CFSG.Wreathed.principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal
      hprincipal hr hu localBasis localPrincipal hlocalPrincipal hζ 1 (by omega)
      (fun _ _ => 1) hbmem hbindep (fun _ _ => 1) hd
  have hU : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      U χ 0 = (basis.representation χ).character u := by
    intro χ hχ
    simpa using (hvalues χ hχ 1 (by norm_num)).symm
  refine ⟨?_, ?_⟩
  · intro χ hχ v hv
    simpa only [Fin.sum_univ_one, mul_one, hU χ hχ] using
      hvalues χ hχ v (by
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
          (Nat.coprime_two_left.mpr hv))
  · have hg := hgram 0 0
    rw [Finset.sum_congr rfl (fun χ hχ => by rw [hU χ hχ])] at hg
    exact hg.trans (cyclic_two_quotient_singleton_gram localBasis ideal
      localPrincipal hlocalPrincipal N hN hquotient)

theorem original_principal_odd_power_column_values_norm {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h : ℤ} (hh : Odd h) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ v : G, v ∈ Subgroup.centralizer ({y} : Set G) → Odd (orderOf v) →
        (basis.representation χ).character (y ^ h * v) =
          (basis.representation χ).character (y ^ h)) ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        starRingEnd ℂ ((basis.representation χ).character (y ^ h)) *
          (basis.representation χ).character (y ^ h) = (2 * 2 ^ n : ℕ) := by
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hyh := orderOf_odd_power hy2 hh
  have hyh' : orderOf (y ^ h) = 2 * 2 ^ n := by
    rw [hyh, pow_succ, Nat.mul_comm]
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers (y ^ h) : Set G)
  have hC : C = Subgroup.centralizer ({y ^ h} : Set G) := by
    dsimp only [C]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hneeded : ∃ (N : Subgroup (Subgroup.centralizer ({y ^ h} : Set G)))
      (_ : N.Normal), Odd (Nat.card N) ∧
      IsPGroup 2 ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) ∧
      IsCyclic ((Subgroup.centralizer ({y ^ h} : Set G)) ⧸ N) ∧ N.index = 2 * 2 ^ n := by
    obtain ⟨hodd, _, hchar, _, _, hquot, hcyc, _⟩ :=
      maximal_root_centralizer_direct_product n hn S e (y ^ h) hyh'
    exact ⟨CFSG.oddCore _, inferInstance, hodd, hquot, hcyc,
      (maximal_root_centralizer_index n hn S e (y ^ h) hyh').1⟩
  rw [← hC] at hneeded
  obtain ⟨N, hnormal, hN, hquot, hcyc, hindex⟩ := hneeded
  let : N.Normal := hnormal
  let : IsCyclic (C ⧸ N) := hcyc
  let localBasis : FiniteIrreducibleCharacterBasis C :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation C)
      (principalFiniteComplexRepresentation_isIrreducible C)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hvalues, hnorm⟩ := cyclic_two_principal_column_values_norm basis ideal
    principal hprincipal (by omega) hyh localBasis localPrincipal hlocalPrincipal N hN hquot
  refine ⟨?_, ?_⟩
  · intro χ hχ v hv hvodd
    have hvC : v ∈ C := by
      rw [hC]
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hcomm : Commute v y := Subgroup.mem_centralizer_singleton_iff.mp hv
      exact hcomm.zpow_right h
    exact hvalues χ hχ ⟨v, hvC⟩ (by simpa only [Subgroup.orderOf_mk] using hvodd)
  · simpa only [hindex] using hnorm

theorem one_not_mem_squareRootSection {G : Type} [Group G] {y : G} {a : ℕ}
    (ha : 1 ≤ a) (hy : orderOf y = 2 ^ a) : (1 : G) ∉ squareRootSection y := by
  intro hmem
  have hfactor : Commute (1 : G) 1 := rfl
  obtain ⟨h, hh, hconj⟩ :=
    (mem_squareRootSection_iff_primary_conjugate hy hfactor (one_mul 1)
      (show orderOf (1 : G) ∣ 2 ^ 0 by simp) (by simp)).mp hmem
  have hpow : y ^ h = 1 := isConj_one_right.mp hconj
  have horder := orderOf_odd_power hy hh
  rw [hpow, orderOf_one] at horder
  have hlt : 1 < 2 ^ a := Nat.one_lt_pow (by omega) (by omega)
  omega

theorem original_principal_odd_power_column_degree_zero {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {h : ℤ} (hh : Odd h) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character (y ^ h) *
        (basis.representation χ).character 1 = 0 := by
  have hy2 : orderOf y = 2 ^ (n + 1) := by rw [hy, pow_succ, Nat.mul_comm]
  have hoff := original_principal_odd_power_column_off_section n hn S e y hy basis ideal
    principal hprincipal hh 1 (one_not_mem_squareRootSection (by omega) hy2)
  simpa only [FiniteComplexRepresentation.character, Representation.char_one,
    map_natCast] using hoff

theorem actual_root_principal_columns {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ∀ h : ℤ, Odd h →
      (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ v : G, v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) → Odd (orderOf v) →
          (basis.representation χ).character (actualRoot S e ^ h * v) =
            (basis.representation χ).character (actualRoot S e ^ h)) ∧
      (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        starRingEnd ℂ ((basis.representation χ).character (actualRoot S e ^ h)) *
          (basis.representation χ).character (actualRoot S e ^ h) = (2 * 2 ^ n : ℕ)) ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation χ).character (actualRoot S e ^ h) *
          (basis.representation χ).character 1 = 0 := by
  intro h hh
  obtain ⟨hvalues, hnorm⟩ := original_principal_odd_power_column_values_norm n hn S e
    (actualRoot S e) (actualRoot_orderOf n hn S e) basis ideal principal hprincipal hh
  exact ⟨hvalues, hnorm, original_principal_odd_power_column_degree_zero n hn S e
    (actualRoot S e) (actualRoot_orderOf n hn S e) basis ideal principal hprincipal hh⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity


