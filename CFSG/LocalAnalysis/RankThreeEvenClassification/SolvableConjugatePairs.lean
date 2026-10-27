module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallFoundations
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ConjugatePairFoundations

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem solvable_conjugate_pair_mem_primeCore {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G] (prime : ℕ) (hprime : prime.Prime) (member : G)
    (hpairs : PrimeConjugatePairs prime member) : member ∈ pCore prime G := by
  classical
  induction hsize : Nat.card G using Nat.strong_induction_on generalizing G with
  | h size ih =>
    by_cases htrivial : Subsingleton G
    · have : Subsingleton G := htrivial
      have heq : member = 1 := Subsingleton.elim _ _
      rw [heq]
      exact Subgroup.one_mem _
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp htrivial
    obtain ⟨kernel, hminimal⟩ := exists_minimal_nontrivial_normal (G := G)
    have : kernel.Normal := hminimal.1.1
    obtain ⟨kernelPrime, hkernelPrime, helementary, dimension, _, hkernelCard⟩ :=
      minimal_normal_solvable_elementary kernel hminimal inferInstance
    let quotient := QuotientGroup.mk' kernel
    have hquotientSmall : Nat.card (G ⧸ kernel) < size := by
      rw [← hsize]
      exact quotient_card_lt_of_nontrivial_subgroup kernel hminimal.1.2
    have hquotientPairs := hpairs.map_surjective prime member quotient (QuotientGroup.mk'_surjective kernel)
    have hquotientCore : quotient member ∈ pCore prime (G ⧸ kernel) :=
      ih (Nat.card (G ⧸ kernel)) hquotientSmall (G := G ⧸ kernel)
        (quotient member) hquotientPairs rfl
    let preimage := (pCore prime (G ⧸ kernel)).comap quotient
    have : (pCore prime (G ⧸ kernel)).Normal := pCore_normal (G ⧸ kernel) prime
    have : preimage.Normal := inferInstance
    have hmemberPreimage : member ∈ preimage := hquotientCore
    by_cases hsame : kernelPrime = prime
    · have hkernelPGroup : IsPGroup prime kernel := by
        rw [← hsame]
        exact isElemAbelian_isPGroup kernelPrime kernel helementary
      have hquotientKernel : IsPGroup prime quotient.ker := by
        rw [QuotientGroup.ker_mk']
        exact hkernelPGroup
      have hpreimagePGroup := (pCore_isPGroup (G ⧸ kernel) prime).comap_of_ker_isPGroup quotient hquotientKernel
      exact le_pCore_of_normal prime preimage inferInstance hpreimagePGroup hmemberPreimage
    have hcomplement : ¬prime ∣ Nat.card kernel := by
      rw [hkernelCard]
      intro hdivisor
      exact hsame (Nat.prime_eq_prime_of_dvd_pow hprime hkernelPrime hdivisor).symm
    let centralizer := Subgroup.centralizer (kernel : Set G)
    have : centralizer.Normal := Subgroup.normal_centralizer
    let intersection := preimage ⊓ centralizer
    have : intersection.Normal := inferInstance
    have hmember : member ∈ intersection :=
      ⟨hmemberPreimage, hpairs.centralizes_normal_complement prime hprime member kernel hcomplement⟩
    let restriction : intersection →* pCore prime (G ⧸ kernel) :=
      { toFun := fun element => ⟨quotient (element : G), element.property.1⟩
        map_one' := Subtype.ext (map_one quotient)
        map_mul' := fun first second => Subtype.ext (map_mul quotient (first : G) (second : G)) }
    have hcentral : restriction.ker ≤ Subgroup.center intersection := by
      intro element helement
      have hzero := congrArg Subtype.val (MonoidHom.mem_ker.mp helement)
      have hkernelMem : (element : G) ∈ kernel := by
        rw [← QuotientGroup.ker_mk' kernel]
        exact MonoidHom.mem_ker.mpr hzero
      apply Subgroup.mem_center_iff.mpr
      intro other
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp other.property.2 (element : G) hkernelMem).symm
    let internal : intersection := ⟨member, hmember⟩
    have hinternalCyclic := cyclic_subtype_isPGroup prime intersection internal (hpairs.cyclic prime member)
    have hinternalCore := pElement_mem_primeCore_of_central_kernel_pTarget prime hprime restriction hcentral
      (pCore_isPGroup (G ⧸ kernel) prime) internal hinternalCyclic
    have hambientCore : member ∈ pCoreOf prime intersection :=
      Subgroup.mem_map_of_mem intersection.subtype hinternalCore
    exact le_pCore_of_normal prime (pCoreOf prime intersection)
      (pCoreOf_normal_of_normal prime intersection inferInstance)
      (pCoreOf_isPGroup prime intersection) hambientCore

end CFSG.RankThreeEvenClassification.Helpers
