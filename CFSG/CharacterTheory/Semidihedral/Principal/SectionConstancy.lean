module

public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G] [Fintype G]

theorem principal_character_section_projection (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {u : G} {e : ℕ}
    (hu : orderOf u ∣ p ^ e)
    (localBasis :
      FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers u : Set G)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (y : Subgroup.centralizer (Subgroup.zpowers u : Set G)) (hy : Nat.Coprime p (orderOf y)) :
    (basis.representation χ).character (u * y) =
      ∑ θ ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
        characterPairing
          (fun c : Subgroup.centralizer (Subgroup.zpowers u : Set G) =>
            (basis.representation χ).character c) (localBasis.representation θ).character *
          (localBasis.representation θ).character (y * centralizerSelf u) := by
  have h := principal_local_section_projection_character basis ideal p principal hprincipal u e
    hu localBasis localPrincipal hlocalPrincipal y (by rw [Subgroup.orderOf_coe]; exact hy) χ
  have hpt : ((⟨u, element_mem_centralizer_zpowers u⟩ :
      Subgroup.centralizer (Subgroup.zpowers u : Set G)) * y) = y * centralizerSelf u :=
    (centralizerSelf_commute u y).eq
  rw [hpt, characterSubsetProjection_character basis _ χ hχ,
    characterSubsetProjection_apply'] at h
  have h' := congrArg (starRingEnd ℂ) h
  rw [map_sum, Subgroup.coe_inv, ← finite_character_conjugate_inverse, Complex.conj_conj] at h'
  have hcomm : u * (y : G) =
      ((y * centralizerSelf u : Subgroup.centralizer (Subgroup.zpowers u : Set G)) : G) := by
    rw [Subgroup.coe_mul]
    exact Subgroup.mem_centralizer_iff.mp y.2 u (Subgroup.mem_zpowers u)
  rw [hcomm, ← h']
  refine Finset.sum_congr rfl fun θ _ => ?_
  obtain ⟨m, hm⟩ := restriction_pairing_nat basis localBasis χ θ
  rw [map_mul, finite_character_conjugate_inverse, inv_inv, hm, Complex.conj_natCast]

theorem principal_character_section_constant_of_normal_complement
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {u : G} {e : ℕ} (hu : orderOf u ∣ p ^ e)
    (R : Subgroup (Subgroup.centralizer (Subgroup.zpowers u : Set G))) [R.Normal]
    (hR : Nat.Coprime p (Nat.card R))
    (hquot : IsPGroup p (Subgroup.centralizer (Subgroup.zpowers u : Set G) ⧸ R))
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    {y : Subgroup.centralizer (Subgroup.zpowers u : Set G)} (hy : y ∈ R) :
    (basis.representation χ).character (u * y) = (basis.representation χ).character u := by
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers u : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  have hyreg : Nat.Coprime p (orderOf y) := by
    have hdvd : orderOf y ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : R)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_right hdvd hR
  have hker := (CFSG.LyonsUnitaryFour.normal_p_complement_principal_block localBasis ideal p
    localPrincipal hlocalPrincipal R hR hquot).1
  rw [principal_character_section_projection basis ideal p principal hprincipal hu localBasis
      localPrincipal hlocalPrincipal hχ y hyreg]
  have h1 := principal_character_section_projection basis ideal p principal hprincipal hu
    localBasis localPrincipal hlocalPrincipal hχ 1
    (by rw [orderOf_one]; exact Nat.coprime_one_right p)
  rw [Subgroup.coe_one, mul_one] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  congr 1
  have hyker : y ∈ MonoidHom.ker (localBasis.representation θ).representation :=
    (hker θ).mp hθ hy
  rw [MonoidHom.mem_ker] at hyker
  rw [one_mul, FiniteComplexRepresentation.character, Representation.character,
    Representation.character, map_mul, hyker, one_mul]

end CFSG.Semidihedral.Principal
