module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AbelianComplementConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallTransport

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem hall_containment_of_solvable {G : Type u} [Group G] [Finite G] [Group.IsSolvable G]
    (primes : Set ℕ) (subgroup : Subgroup G) (horder : PrimeSetOrder primes (Nat.card subgroup)) :
    ∃ hall : Subgroup G, HallFor primes hall ∧ subgroup ≤ hall := by
  classical
  induction hsize : Nat.card G using Nat.strong_induction_on generalizing G with
  | h size ih =>
    by_cases htrivial : Subsingleton G
    · have : Subsingleton G := htrivial
      have htop : subgroup = ⊤ := Subsingleton.elim _ _
      refine ⟨⊤, HallFor.top_of_primeSetOrder primes ?_, le_top⟩
      simpa only [htop, Subgroup.card_top] using horder
    have : Nontrivial G := not_subsingleton_iff_nontrivial.mp htrivial
    obtain ⟨kernel, hminimal⟩ := exists_minimal_nontrivial_normal (G := G)
    have : kernel.Normal := hminimal.1.1
    obtain ⟨kernelPrime, hkernelPrime, _, dimension, _, hkernelCard⟩ :=
      minimal_normal_solvable_elementary kernel hminimal inferInstance
    let quotient := QuotientGroup.mk' kernel
    have hquotientSmall : Nat.card (G ⧸ kernel) < size := by
      rw [← hsize]
      exact quotient_card_lt_of_nontrivial_subgroup kernel hminimal.1.2
    obtain ⟨quotientHall, hquotientHall, hquotientLe⟩ :=
      ih (Nat.card (G ⧸ kernel)) hquotientSmall (G := G ⧸ kernel) (subgroup.map quotient)
        (PrimeSetOrder.map primes subgroup quotient horder) rfl
    let overgroup := quotientHall.comap quotient
    have hsubgroupLe : subgroup ≤ overgroup := Subgroup.map_le_iff_le_comap.mp hquotientLe
    have hovergroupIndex : PrimeSetOrder primesᶜ overgroup.index := by
      rw [Subgroup.index_comap_of_surjective quotientHall (QuotientGroup.mk'_surjective kernel)]
      exact hquotientHall.2
    by_cases hovergroupNe : overgroup ≠ ⊤
    · have hovergroupSmall : Nat.card overgroup < size := by
        rw [← hsize]
        have hstrict := subgroup_card_lt_of_lt overgroup ⊤ (lt_top_iff_ne_top.mpr hovergroupNe)
        rw [Subgroup.card_top] at hstrict
        exact hstrict
      obtain ⟨hall, hhall, hle⟩ := ih (Nat.card overgroup) hovergroupSmall (G := overgroup)
        (subgroup.subgroupOf overgroup)
        (PrimeSetOrder.subgroupOf primes subgroup overgroup hsubgroupLe horder) rfl
      refine ⟨hall.map overgroup.subtype, HallFor.map_subtype primes overgroup hall hhall hovergroupIndex, ?_⟩
      calc
        subgroup = (subgroup.subgroupOf overgroup).map overgroup.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hsubgroupLe).symm
        _ ≤ hall.map overgroup.subtype := Subgroup.map_mono hle
    have hovergroupTop : overgroup = ⊤ := not_ne_iff.mp hovergroupNe
    have hquotientTop : quotientHall = ⊤ := by
      have hmapped := Subgroup.map_comap_eq_self_of_surjective
        (QuotientGroup.mk'_surjective kernel) quotientHall
      change overgroup.map quotient = quotientHall at hmapped
      rw [hovergroupTop, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective kernel)] at hmapped
      exact hmapped.symm
    have hquotientOrder : PrimeSetOrder primes (Nat.card (G ⧸ kernel)) := by
      have hquotientOrder := hquotientHall.1
      rw [hquotientTop, Subgroup.card_top] at hquotientOrder
      exact hquotientOrder
    by_cases hkernelMem : kernelPrime ∈ primes
    · refine ⟨⊤, HallFor.top_of_primeSetOrder primes ?_, le_top⟩
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup kernel, hkernelCard]
      exact PrimeSetOrder.mul primes _ _ hquotientOrder
        (PrimeSetOrder.prime_pow primes kernelPrime hkernelPrime hkernelMem dimension)
    have hkernelOrder : PrimeSetOrder primesᶜ (Nat.card kernel) := by
      rw [hkernelCard]
      exact PrimeSetOrder.prime_pow primesᶜ kernelPrime hkernelPrime hkernelMem dimension
    have hkernelCoprime : (Nat.card kernel).Coprime kernel.index := by
      rw [Subgroup.index_eq_card]
      exact (PrimeSetOrder.coprime_compl primes _ _ hquotientOrder hkernelOrder).symm
    obtain ⟨hall, hcomplement⟩ := Subgroup.exists_right_complement'_of_coprime hkernelCoprime
    have hhall : HallFor primes hall := by
      constructor
      · rw [← hcomplement.symm.index_eq_card, Subgroup.index_eq_card]
        exact hquotientOrder
      · rw [hcomplement.index_eq_card]
        exact hkernelOrder
    let envelope := kernel ⊔ subgroup
    have hkernelLe : kernel ≤ envelope := le_sup_left
    have hsubgroupEnvelope : subgroup ≤ envelope := le_sup_right
    let localKernel := kernel.subgroupOf envelope
    let localSubgroup := subgroup.subgroupOf envelope
    let localHall := hall.subgroupOf envelope
    have hlocalKernelOrder : PrimeSetOrder primesᶜ (Nat.card localKernel) :=
      PrimeSetOrder.subgroupOf primesᶜ kernel envelope hkernelLe hkernelOrder
    have hlocalOrder : PrimeSetOrder primes (Nat.card localSubgroup) :=
      PrimeSetOrder.subgroupOf primes subgroup envelope hsubgroupEnvelope horder
    have hlocalComplement : localKernel.IsComplement' localSubgroup :=
      normal_complement_of_sup_eq_top_and_coprime localKernel localSubgroup
        (by rw [← Subgroup.subgroupOf_sup hkernelLe hsubgroupEnvelope];
            exact Subgroup.subgroupOf_self envelope)
        (PrimeSetOrder.coprime_compl primes _ _ hlocalOrder hlocalKernelOrder).symm
    have hlocalHallComplement : localKernel.IsComplement' localHall :=
      normal_complement_subgroupOf kernel hall envelope hcomplement hkernelLe
    have hcommKernel : IsMulCommutative kernel :=
      minimal_normal_solvable_commutative kernel hminimal inferInstance
    have hcommLocal : IsMulCommutative localKernel := by
      apply isMulCommutative_iff.mpr
      intro first second
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun element : kernel => (element : G))
        (isMulCommutative_iff.mp hcommKernel
          ⟨(first : envelope), first.property⟩ ⟨(second : envelope), second.property⟩)
    have hlocalCoprime : (Nat.card localKernel).Coprime localKernel.index := by
      rw [hlocalHallComplement.symm.index_eq_card]
      exact (PrimeSetOrder.coprime_compl primes _ _
        (PrimeSetOrder.subgroupOf_any primes hall envelope hhall.1) hlocalKernelOrder).symm
    obtain ⟨conjugator, _, hconjugacy⟩ := abelian_normal_complements_conjugate
      localKernel localSubgroup localHall hcommLocal hlocalComplement hlocalHallComplement hlocalCoprime
    have hmapped := congrArg (fun candidate : Subgroup envelope => candidate.map envelope.subtype) hconjugacy
    rw [map_conjugate_subgroup_eq, Subgroup.map_subgroupOf_eq_of_le hsubgroupEnvelope] at hmapped
    change subgroup.map (MulAut.conj (conjugator : G)).toMonoidHom =
      localHall.map envelope.subtype at hmapped
    have hconjugateLe : subgroup.map (MulAut.conj (conjugator : G)).toMonoidHom ≤ hall := by
      rw [hmapped]
      exact Subgroup.map_le_iff_le_comap.mpr le_rfl
    refine ⟨hall.map (MulAut.conj (conjugator : G)⁻¹).toMonoidHom,
      HallFor.map primes hall (MulAut.conj (conjugator : G)⁻¹).toMonoidHom
        (MulAut.conj (conjugator : G)⁻¹).surjective hhall, ?_⟩
    have hle := Subgroup.map_mono (f := (MulAut.conj (conjugator : G)⁻¹).toMonoidHom) hconjugateLe
    rw [subgroup_map_conj_inv_cancel] at hle
    exact hle

end CFSG.RankThreeEvenClassification.Helpers
