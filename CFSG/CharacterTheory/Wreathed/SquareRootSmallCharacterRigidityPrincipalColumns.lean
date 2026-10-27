module

public import CFSG.CharacterTheory.Wreathed.PrincipalSectionColumns
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem principal_character_one_on_odd {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsCyclic (C ⧸ N)]
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

theorem principal_singleton_integral_basis {C : Type} [Group C] [Fintype C]
    (basis : FiniteIrreducibleCharacterBasis C) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (N : Subgroup C) [N.Normal] (hN : Odd (Nat.card N))
    (hquotient : IsPGroup 2 (C ⧸ N)) [IsCyclic (C ⧸ N)] :
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
    rw [principal_character_one_on_odd basis ideal principal hprincipal N hN hquotient hθ
      (Nat.coprime_two_left.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hy))]
    simp

theorem principal_value_column_off_section {G : Type} [Group G] [Fintype G]
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
    [IsCyclic ((Subgroup.centralizer (Subgroup.zpowers u : Set G)) ⧸ N)]
    (g : G) (hg : ∀ a c : G, a * c = g → Commute a c →
      (∃ e : ℕ, orderOf a = 2 ^ e) → ¬ 2 ∣ orderOf c → ¬ IsConj a u) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u *
        starRingEnd ℂ ((basis.representation χ).character g) = 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : NeZero (2 ^ r) := ⟨pow_ne_zero _ (by decide)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ (2 ^ r)
  obtain ⟨hbmem, hbindep, hd⟩ := principal_singleton_integral_basis localBasis ideal
    localPrincipal hlocalPrincipal N hN hquotient
  obtain ⟨U, m, lam, _, _, _, _, hvalues, _, _, hoff⟩ :=
    CFSG.Wreathed.principal_primary_section_cyclotomic_basis_columns basis ideal 2 principal
      hprincipal hr hu localBasis localPrincipal hlocalPrincipal hζ 1 (by omega)
      (fun _ _ => 1) hbmem hbindep (fun _ _ => 1) hd
  have hU : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      U χ 0 = (basis.representation χ).character u := by
    intro χ hχ
    simpa using (hvalues χ hχ 1 (by norm_num)).symm
  have h := hoff g hg 0
  rwa [Finset.sum_congr rfl fun χ hχ => by rw [hU χ hχ]] at h

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
