module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem faithful_pGroup_frattini_action_kernel_isPGroup
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
    IsPGroup prime (MulDistribMulAction.toMulAut acting (source ⧸ frattini source)).ker := by
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
  let hom := MulDistribMulAction.toMulAut acting (source ⧸ frattini source)
  apply (isPGroup_iff_primeFactors_card_subset (Fact.out : prime.Prime).ne_zero).mpr
  intro otherPrime hfactor
  obtain ⟨hotherPrime, hdivides, _⟩ := Nat.mem_primeFactors.mp hfactor
  by_cases hequal : otherPrime = prime
  · rw [hequal]
    exact (Fact.out : prime.Prime).mem_primeFactors_self
  let : Fact otherPrime.Prime := ⟨hotherPrime⟩
  let sylow : Sylow otherPrime hom.ker := Classical.choice inferInstance
  have hcoprime : ¬ otherPrime ∣ Nat.card (frattini source) := by
    intro hdividesFrattini
    obtain ⟨exponent, hcard⟩ := (hsource.to_subgroup (frattini source)).exists_card_eq
    exact hequal ((Nat.prime_dvd_prime_iff_eq hotherPrime Fact.out).mp
      (hotherPrime.dvd_of_dvd_pow (hcard ▸ hdividesFrattini)))
  have hfaithfulSylow : Function.Injective
      (MulDistribMulAction.toMulAut (sylow : Subgroup hom.ker) source) := by
    intro first second hequalAction
    apply Subtype.ext
    apply Subtype.ext
    apply hfaithful
    ext member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequalAction
  have hquotientFaithful := faithful_coprime_pGroup_action_on_frattini_quotient
    otherPrime sylow.isPGroup' hcoprime hfaithfulSylow
  have hscalarTrivial : ∀ scalar : (sylow : Subgroup hom.ker), scalar = 1 := by
    intro scalar
    apply hquotientFaithful
    ext member
    have hequalAction : hom ((scalar : hom.ker) : acting) = 1 := (scalar : hom.ker).property
    have hfixed := congrArg
      (fun equivalence : MulAut (source ⧸ frattini source) => equivalence member) hequalAction
    change scalar • member = (1 : (sylow : Subgroup hom.ker)) • member
    rw [one_smul]
    exact hfixed
  have hcard : Nat.card (sylow : Subgroup hom.ker) = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, hscalarTrivial⟩
  have hprimeDivides := sylow.dvd_card_of_dvd_card hdivides
  rw [hcard] at hprimeDivides
  exact (hotherPrime.ne_one (Nat.dvd_one.mp hprimeDivides)).elim

theorem pGroup_frattini_action_kernel_isPGroup_of_source_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [Finite acting] [Group source] [Finite source]
    [MulDistribMulAction acting source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (hkernel : IsPGroup prime (MulDistribMulAction.toMulAut acting source).ker) :
    letI := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
    IsPGroup prime (MulDistribMulAction.toMulAut acting (source ⧸ frattini source)).ker := by
  let sourceHom := MulDistribMulAction.toMulAut acting source
  let : MulDistribMulAction sourceHom.range source := inferInstance
  have hfaithfulRange : Function.Injective (MulDistribMulAction.toMulAut sourceHom.range source) := by
    intro first second hequal
    apply Subtype.ext
    apply MulEquiv.ext
    intro member
    exact congrArg (fun equivalence : MulAut source => equivalence member) hequal
  let := characteristic_quotient_mulDistribMulAction (acting := sourceHom.range) (frattini source)
  let rangeHom := MulDistribMulAction.toMulAut sourceHom.range (source ⧸ frattini source)
  have hrangeKernel : IsPGroup prime rangeHom.ker :=
    faithful_pGroup_frattini_action_kernel_isPGroup prime hsource hfaithfulRange
  let := characteristic_quotient_mulDistribMulAction (acting := acting) (frattini source)
  have hcompose : rangeHom.comp sourceHom.rangeRestrict =
      MulDistribMulAction.toMulAut acting (source ⧸ frattini source) := by
    apply MonoidHom.ext
    intro scalar
    apply MulEquiv.ext
    intro member
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (frattini source) member
    rfl
  rw [← hcompose]
  apply pGroup_composite_hom_kernel prime sourceHom.rangeRestrict rangeHom
  · rw [MonoidHom.ker_rangeRestrict]
    exact hkernel
  · exact hrangeKernel

theorem normal_pGroup_le_frattini_conjugation_action_kernel
    {ambient : Type u} [Group ambient]
    (prime : ℕ) [Fact prime.Prime] [Finite ambient]
    (normal : Subgroup ambient) [normal.Normal] (hnormal : IsPGroup prime normal) :
    letI : MulDistribMulAction ambient normal :=
      MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
    letI := characteristic_quotient_mulDistribMulAction (acting := ambient) (frattini normal)
    normal ≤ (MulDistribMulAction.toMulAut ambient (normal ⧸ frattini normal)).ker := by
  let : MulDistribMulAction ambient normal :=
    MulDistribMulAction.compHom normal (MulAut.conjNormal (H := normal))
  let := characteristic_quotient_mulDistribMulAction (acting := ambient) (frattini normal)
  let : IsMulCommutative (normal ⧸ frattini normal) :=
    pGroup_frattini_quotient_isMulCommutative prime hnormal
  let : CommGroup (normal ⧸ frattini normal) := IsMulCommutative.instCommGroup
  intro scalar hscalar
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro member
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (frattini normal) member
  change (QuotientGroup.mk' (frattini normal)) (scalar • lift) =
    (QuotientGroup.mk' (frattini normal)) lift
  have hconjugation : scalar • lift =
      (⟨scalar, hscalar⟩ : normal) * lift * (⟨scalar, hscalar⟩ : normal)⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hconjugation, map_mul, map_mul, map_inv]
  rw [mul_comm ((QuotientGroup.mk' (frattini normal)) (⟨scalar, hscalar⟩ : normal)),
    mul_assoc, mul_inv_cancel, mul_one]

theorem selfcentralizing_pCore_frattini_conjugation_kernel_eq
    {ambient : Type u} [Group ambient] [Finite ambient]
    (prime : ℕ) [Fact prime.Prime]
    (hcentralizer : Subgroup.centralizer (pCore prime ambient : Set ambient) ≤ pCore prime ambient) :
    letI : (pCore prime ambient).Normal := pCore_normal prime
    letI : MulDistribMulAction ambient (pCore prime ambient) :=
      MulDistribMulAction.compHom (pCore prime ambient) (MulAut.conjNormal (H := pCore prime ambient))
    letI := characteristic_quotient_mulDistribMulAction (acting := ambient) (frattini (pCore prime ambient))
    (MulDistribMulAction.toMulAut ambient
      (pCore prime ambient ⧸ frattini (pCore prime ambient))).ker = pCore prime ambient := by
  let : (pCore prime ambient).Normal := pCore_normal prime
  let : MulDistribMulAction ambient (pCore prime ambient) :=
    MulDistribMulAction.compHom (pCore prime ambient) (MulAut.conjNormal (H := pCore prime ambient))
  have hsourceKernel : IsPGroup prime (MulDistribMulAction.toMulAut ambient (pCore prime ambient)).ker :=
    selfcentralizing_normal_conjugation_action_kernel_isPGroup prime (pCore prime ambient)
      (pCore_isPGroup prime) hcentralizer
  let := characteristic_quotient_mulDistribMulAction (acting := ambient) (frattini (pCore prime ambient))
  let hom := MulDistribMulAction.toMulAut ambient (pCore prime ambient ⧸ frattini (pCore prime ambient))
  have hkernel : IsPGroup prime hom.ker :=
    pGroup_frattini_action_kernel_isPGroup_of_source_kernel prime (pCore_isPGroup prime) hsourceKernel
  apply le_antisymm
  · exact le_sSup ⟨(inferInstance : hom.ker.Normal), hkernel⟩
  · exact normal_pGroup_le_frattini_conjugation_action_kernel prime (pCore prime ambient)
      (pCore_isPGroup prime)

end CFSG.PreuniquenessRankFour.Helpers
