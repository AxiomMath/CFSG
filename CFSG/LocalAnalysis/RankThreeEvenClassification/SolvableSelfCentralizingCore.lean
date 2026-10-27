module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeComplementQuotient

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem normal_nilpotent_isPGroup_of_trivial_primeComplementCore {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (hcore : primeComplementCore G prime = ⊥)
    (subgroup : Subgroup G) [subgroup.Normal] (hnilpotent : Group.IsNilpotent subgroup) :
    IsPGroup prime subgroup := by
  have : Group.IsNilpotent subgroup := hnilpotent
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro divisor hdivisor hdiv
  by_contra hne
  have : Fact divisor.Prime := ⟨hdivisor⟩
  let sylow : Sylow divisor subgroup := Classical.choice inferInstance
  have hsylowNormal : (sylow : Subgroup subgroup).Normal := inferInstance
  have : (sylow : Subgroup subgroup).Characteristic := sylow.characteristic_of_normal hsylowNormal
  let ambient := (sylow : Subgroup subgroup).map subgroup.subtype
  have hambientNormal : ambient.Normal := ConjAct.normal_of_characteristic_of_normal
  have hambientPGroup : IsPGroup divisor ambient := sylow.isPGroup'.map subgroup.subtype
  obtain ⟨dimension, hcard⟩ := hambientPGroup.exists_card_eq
  have hcomplement : ¬prime ∣ Nat.card ambient := by
    rw [hcard]
    intro hprimeDiv
    exact hne (Nat.prime_eq_prime_of_dvd_pow hprime hdivisor hprimeDiv).symm
  have hambientBot : ambient = ⊥ := by
    apply bot_unique
    rw [← hcore]
    exact le_primeComplementCore prime ambient hambientNormal hcomplement
  have hsylowBot : (sylow : Subgroup subgroup) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (sylow : Subgroup subgroup) subgroup.subtype_injective).mp hambientBot
  have hdivSylow := sylow.dvd_card_of_dvd_card hdiv
  rw [hsylowBot, Subgroup.card_bot] at hdivSylow
  exact hdivisor.not_dvd_one hdivSylow

theorem exists_minimal_nontrivial_normal_le {G : Type u} [Group G] [Finite G]
    (subgroup : Subgroup G) [subgroup.Normal] (hne : subgroup ≠ ⊥) :
    ∃ minimal : Subgroup G, minimal ≤ subgroup ∧ MinimalNontrivialNormal minimal := by
  obtain ⟨minimal, hle, hminimal⟩ := Finite.exists_le_minimal
    (p := fun candidate : Subgroup G => candidate.Normal ∧ candidate ≠ ⊥) ⟨inferInstance, hne⟩
  exact ⟨minimal, hle, hminimal⟩

theorem solvable_trivial_primeComplementCore_self_centralizing {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G] (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore G prime = ⊥) :
    Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G := by
  classical
  let centralizer := Subgroup.centralizer (pCore prime G : Set G)
  have hcentralizerNormal : centralizer.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    apply normalizes_centralizer_of_normalizes
    have : (pCore prime G).Normal := pCore_normal G prime
    rw [Subgroup.normalizer_eq_top]
  have : centralizer.Normal := hcentralizerNormal
  let kernel := pCore prime G ⊓ centralizer
  have : (pCore prime G).Normal := pCore_normal G prime
  have : kernel.Normal := inferInstance
  let quotient := QuotientGroup.mk' kernel
  have hkernelCentralizer : kernel ≤ centralizer := inf_le_right
  have hkernelCentral : kernel ≤ Subgroup.centralizer (centralizer : Set G) := by
    apply (Subgroup.le_centralizer_iff).mpr
    exact Subgroup.centralizer_le (show (kernel : Set G) ⊆ (pCore prime G : Set G) from inf_le_left)
  have hquotientCentralizerNormal : (centralizer.map quotient).Normal :=
    hcentralizerNormal.map quotient (QuotientGroup.mk'_surjective kernel)
  have : (centralizer.map quotient).Normal := hquotientCentralizerNormal
  by_contra hnotLe
  have hquotientCentralizerNe : centralizer.map quotient ≠ ⊥ := by
    intro heq
    apply hnotLe
    intro element helement
    have hzero : quotient element = 1 := by
      have hmem := Subgroup.mem_map_of_mem quotient helement
      rw [heq, Subgroup.mem_bot] at hmem
      exact hmem
    have hkernelMem := MonoidHom.mem_ker.mpr hzero
    change element ∈ (QuotientGroup.mk' kernel).ker at hkernelMem
    rw [QuotientGroup.ker_mk'] at hkernelMem
    exact hkernelMem.1
  obtain ⟨minimal, hminimalLe, hminimal⟩ := exists_minimal_nontrivial_normal_le
    (centralizer.map quotient) hquotientCentralizerNe
  have : minimal.Normal := hminimal.1.1
  let preimage := minimal.comap quotient
  have : preimage.Normal := inferInstance
  have hpreimageCentralizer : preimage ≤ centralizer := by
    have hle := Subgroup.comap_mono (f := quotient) hminimalLe
    rw [Subgroup.comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']; exact hkernelCentralizer)] at hle
    exact hle
  let restriction : preimage →* minimal :=
    { toFun := fun element => ⟨quotient element, element.property⟩
      map_one' := Subtype.ext (map_one quotient)
      map_mul' := fun first second => Subtype.ext (map_mul quotient (first : G) (second : G)) }
  have hsurjective : Function.Surjective restriction := by
    intro element
    obtain ⟨representative, heq⟩ := QuotientGroup.mk'_surjective kernel element
    refine ⟨⟨representative, ?_⟩, Subtype.ext heq⟩
    change quotient representative ∈ minimal
    exact heq.symm ▸ element.property
  have hcentral : restriction.ker ≤ Subgroup.center preimage := by
    intro element helement
    have hzero := congrArg Subtype.val (MonoidHom.mem_ker.mp helement)
    have hkernelMem : (element : G) ∈ kernel := by
      rw [← QuotientGroup.ker_mk' kernel]
      exact MonoidHom.mem_ker.mpr hzero
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hkernelCentral hkernelMem) other
      (hpreimageCentralizer other.property)
  have hcomm : IsMulCommutative minimal := minimal_normal_solvable_commutative minimal hminimal inferInstance
  have : IsMulCommutative minimal := hcomm
  let : CommGroup minimal := IsMulCommutative.instCommGroup
  have hnilpotent : Group.IsNilpotent preimage := nilpotent_of_central_kernel restriction hsurjective hcentral inferInstance
  have hpgroup := normal_nilpotent_isPGroup_of_trivial_primeComplementCore prime hprime hcore preimage hnilpotent
  have hpreimageCore : preimage ≤ pCore prime G := le_pCore_of_normal prime preimage inferInstance hpgroup
  have hpreimageKernel : preimage ≤ kernel := le_inf hpreimageCore hpreimageCentralizer
  have hminimalBot : minimal = ⊥ := by
    apply bot_unique
    intro element helement
    obtain ⟨preimageElement, hpreimageElement⟩ := QuotientGroup.mk'_surjective kernel element
    have hmem : preimageElement ∈ preimage := by
      change quotient preimageElement ∈ minimal
      exact hpreimageElement.symm ▸ helement
    have hzero : quotient preimageElement = 1 := by
      apply MonoidHom.mem_ker.mp
      change preimageElement ∈ (QuotientGroup.mk' kernel).ker
      rw [QuotientGroup.ker_mk']
      exact hpreimageKernel hmem
    exact Subgroup.mem_bot.mpr (hpreimageElement.symm.trans hzero)
  exact hminimal.1.2 hminimalBot

end CFSG.RankThreeEvenClassification.Helpers
