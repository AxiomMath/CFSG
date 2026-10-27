module

public import CFSG.CharacterTheory.Semidihedral.Principal.ResidueCentralIdempotents
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NormalComplementPrincipal

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u

variable {E : Type u} [Group E] [Fintype E]

theorem centralCharacterScalar_eq_sum (basis : FiniteIrreducibleCharacterBasis E)
    (z : MonoidAlgebra ℂ E) (label : basis.index) :
    centralCharacterScalar basis z label =
      (∑ g, z.coeff g * (basis.representation label).character g) /
        (basis.representation label).character 1 := by
  unfold centralCharacterScalar characterPairing
  congr 1
  have hcard : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  exact Fintype.sum_equiv (Equiv.inv E) _ _ (fun g => by simp)

variable {Q : Type u} [Group Q] [Fintype Q] (π : E →* Q) (hπ : Function.Surjective π)

@[expose] noncomputable def inflationCentralHom (R : Subring ℂ) :
    centralCoefficientSubring (G := E) R →+* centralCoefficientSubring (G := Q) R where
  toFun z := ⟨MonoidAlgebra.mapDomainRingHom ℂ π z.val, by
    refine ⟨fun q => ?_, ?_⟩
    · rw [groupAlgebra_quotient_coeff_sum]
      refine R.sum_mem fun h _ => ?_
      split_ifs
      · exact centralCoefficientSubring_coefficients R z h
      · exact R.zero_mem
    · refine Subring.mem_center_iff.mpr fun w => ?_
      obtain ⟨y, rfl⟩ := groupAlgebra_mapDomain_surjective (ring := ℂ) π hπ w
      rw [← map_mul, ← map_mul, (centralCoefficientSubring_commutes R z y).eq]⟩
  map_one' := Subtype.ext (map_one _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_mul' x y := Subtype.ext (map_mul _ x.val y.val)

omit [Fintype Q] in
theorem inflationCentralHom_coeff (R : Subring ℂ) (z : centralCoefficientSubring (G := E) R)
    (q : Q) :
    (inflationCentralHom π hπ R z).val.coeff q =
      ∑ h : E, if π h = q then z.val.coeff h else 0 := by
  rw [show (inflationCentralHom π hπ R z).val = MonoidAlgebra.mapDomainRingHom ℂ π z.val from rfl,
    groupAlgebra_quotient_coeff_sum]

theorem localCentralCharacterHom_inflation (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (χ : basis.index)
    (θ : quotientBasis.index)
    (hχθ : (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π)
    (z : centralCoefficientSubring (G := E) (localizedComplexIntegerRing ideal)) :
    localCentralCharacterHom basis ideal χ z =
      localCentralCharacterHom quotientBasis ideal θ
        (inflationCentralHom π hπ (localizedComplexIntegerRing ideal) z) := by
  apply Subtype.ext
  change centralCharacterScalar basis z.val χ =
    centralCharacterScalar quotientBasis (inflationCentralHom π hπ _ z).val θ
  rw [centralCharacterScalar_eq_sum, centralCharacterScalar_eq_sum, hχθ]
  simp only [Function.comp_apply, map_one]
  congr 1
  simp only [inflationCentralHom_coeff, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_ite_eq]
  simp

omit [Fintype Q] in
include hπ in
theorem card_fiber_eq_card_ker (q : Q) :
    (Finset.univ.filter fun h : E => π h = q).card = Nat.card π.ker := by
  obtain ⟨g₀, rfl⟩ := hπ q
  have h1 : (Finset.univ.filter fun h : E => π h = π g₀) =
      Finset.univ.image (fun n : π.ker => g₀ * n) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hh
      have hmem : g₀⁻¹ * h ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hh, inv_mul_cancel]
      exact ⟨⟨g₀⁻¹ * h, hmem⟩, by simp⟩
    · rintro ⟨n, rfl⟩
      rw [map_mul, MonoidHom.mem_ker.mp n.2, mul_one]
  rw [h1, Finset.card_image_of_injective _ (fun a b hab => Subtype.ext (mul_left_cancel hab)),
    Finset.card_univ, Nat.card_eq_fintype_card]

omit [Fintype Q] in
include hπ in
theorem inflationCentralHom_surjective (R : Subring ℂ) (hN : ((Nat.card π.ker : ℂ))⁻¹ ∈ R) :
    Function.Surjective (inflationCentralHom π hπ R) := by
  intro w
  set c : ℂ := ((Nat.card π.ker : ℂ))⁻¹ with hc
  let lift : MonoidAlgebra ℂ E := ∑ h : E, MonoidAlgebra.single h (c * w.val.coeff (π h))
  have hliftcoeff : ∀ g : E, lift.coeff g = c * w.val.coeff (π g) := by
    intro g
    simp [lift, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.coeff_single,
      Finsupp.single_apply]
  have hwconj := (mem_center_iff_coeff_conj w.val).mp w.property.2
  have hcentral : lift ∈ Subring.center (MonoidAlgebra ℂ E) := by
    rw [mem_center_iff_coeff_conj]
    intro g k
    have hk : π (k * g * k⁻¹) = π k * π g * (π k)⁻¹ := by simp
    rw [hliftcoeff, hliftcoeff, hk, hwconj]
  refine ⟨⟨lift, ⟨fun g => ?_, hcentral⟩⟩, ?_⟩
  · rw [hliftcoeff]
    exact R.mul_mem hN (centralCoefficientSubring_coefficients R w _)
  · apply Subtype.ext
    ext q
    change (inflationCentralHom π hπ R ⟨lift, _⟩).val.coeff q = w.val.coeff q
    rw [inflationCentralHom_coeff]
    have hterm : ∀ h : E, (if π h = q then lift.coeff h else 0) =
        if π h = q then c * w.val.coeff q else 0 := by
      intro h
      split_ifs with hh
      · rw [hliftcoeff, hh]
      · rfl
    simp only [hterm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      card_fiber_eq_card_ker π hπ q, hc]
    have hN0 : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp

include hπ in
theorem exists_inflation_of_ker_le (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q) (χ : basis.index)
    (hker : π.ker ≤ MonoidHom.ker (basis.representation χ).representation) :
    ∃ θ : quotientBasis.index,
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π := by
  let ρ := (basis.representation χ).representation
  let ρ' : Representation ℂ Q (basis.representation χ).vector :=
    (QuotientGroup.lift π.ker ρ hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom
  have hcomp : ρ'.comp π = ρ := by
    ext g v
    have h : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
        (QuotientGroup.mk g : E ⧸ π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [ρ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  let factored : FiniteComplexRepresentation Q :=
    { vector := (basis.representation χ).vector, representation := ρ' }
  have hirr : factored.IsIrreducible := by
    apply CFSG.LyonsUnitaryFour.isIrreducible_of_comp_surjective π hπ
    rw [hcomp]
    exact basis.irreducible χ
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible quotientBasis factored hirr
  refine ⟨θ, ?_⟩
  rw [hθ]
  funext g
  change LinearMap.trace ℂ _ (ρ g) = LinearMap.trace ℂ _ (ρ' (π g))
  rw [← MonoidHom.comp_apply, hcomp]

theorem ker_le_of_inflation (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q) (χ : basis.index)
    (θ : quotientBasis.index)
    (hχθ : (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π) :
    π.ker ≤ MonoidHom.ker (basis.representation χ).representation := by
  apply CFSG.LyonsUnitaryFour.le_ker_of_character_eq_degree
  intro n hn
  change (basis.representation χ).character n = (basis.representation χ).character 1
  rw [hχθ]
  simp only [Function.comp_apply, map_one]
  rw [MonoidHom.mem_ker.mp hn]

include hπ in
theorem exists_inflated_label (basis : FiniteIrreducibleCharacterBasis E)
    (quotientBasis : FiniteIrreducibleCharacterBasis Q) (θ : quotientBasis.index) :
    ∃ χ : basis.index,
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π := by
  obtain ⟨χ, hχ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (inflatedFiniteComplexRepresentation π (quotientBasis.representation θ))
    (CFSG.LyonsUnitaryFour.isIrreducible_comp_surjective π hπ _ (quotientBasis.irreducible θ))
  exact ⟨χ, hχ⟩

include hπ in
theorem normal_prime_kernel_principal_block_inflation_of_surjective
    (basis : FiniteIrreducibleCharacterBasis E) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (hN : ¬ p ∣ Nat.card π.ker) (quotientBasis : FiniteIrreducibleCharacterBasis Q)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (quotientPrincipal : quotientBasis.index)
    (hquotientPrincipal : (quotientBasis.representation quotientPrincipal).character = 1) :
    (∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ θ ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) quotientPrincipal,
        (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π) ∧
    (∀ (χ χ' : basis.index) (θ θ' : quotientBasis.index),
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π →
      (basis.representation χ').character = (quotientBasis.representation θ').character ∘ π →
      (χ' ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ ↔
        θ' ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) θ)) ∧
    (∀ χ, π.ker ≤ MonoidHom.ker (basis.representation χ).representation →
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ,
        π.ker ≤ MonoidHom.ker (basis.representation ψ).representation) ∧
    (∀ χ, π.ker ≤ MonoidHom.ker (basis.representation χ).representation ↔
      ∃ θ : quotientBasis.index,
        (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π) := by
  set R := localizedComplexIntegerRing ideal with hR
  have hunit : IsUnit ((Nat.card π.ker : ℤ) : R) := by
    rw [localizedComplexInteger_integer_unit_iff ideal p]
    intro hdvd
    exact hN (Int.natCast_dvd_natCast.mp hdvd)
  have hinvmem : ((Nat.card π.ker : ℂ))⁻¹ ∈ R := by
    obtain ⟨u, hu⟩ := hunit
    have h : ((u⁻¹ : Rˣ) : R).val * (Nat.card π.ker : ℂ) = 1 := by
      have e : (((u⁻¹ : Rˣ) : R) * (u : R) : R) = 1 := by rw [Units.inv_mul]
      rw [hu] at e
      have e' := congrArg Subtype.val e
      simpa using e'
    rw [show ((Nat.card π.ker : ℂ))⁻¹ = ((u⁻¹ : Rˣ) : R).val from
      (eq_inv_of_mul_eq_one_left h).symm]
    exact ((u⁻¹ : Rˣ) : R).property
  have hsurj := inflationCentralHom_surjective π hπ R hinvmem
  have hsame : ∀ (χ χ' : basis.index) (θ θ' : quotientBasis.index),
      (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π →
      (basis.representation χ').character = (quotientBasis.representation θ').character ∘ π →
      (χ' ∈ coefficientBlock basis R χ ↔ θ' ∈ coefficientBlock quotientBasis R θ) := by
    intro χ χ' θ θ' hχ hχ'
    rw [coefficientBlock_mem_iff, coefficientBlock_mem_iff,
      sameCoefficientBlock_iff_centralCharacterResidueHom_eq,
      sameCoefficientBlock_iff_centralCharacterResidueHom_eq]
    have hcomp : ∀ (c : basis.index) (d : quotientBasis.index),
        (basis.representation c).character = (quotientBasis.representation d).character ∘ π →
        centralCharacterResidueHom basis ideal c =
          (centralCharacterResidueHom quotientBasis ideal d).comp
            (inflationCentralHom π hπ R) := by
      intro c d hcd
      apply RingHom.ext
      intro z
      change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal c z) =
        localizedComplexIntegerResidue ideal
          (localCentralCharacterHom quotientBasis ideal d (inflationCentralHom π hπ R z))
      rw [localCentralCharacterHom_inflation π hπ basis quotientBasis ideal c d hcd]
    rw [hcomp χ θ hχ, hcomp χ' θ' hχ']
    constructor
    · intro h
      apply RingHom.ext
      intro w
      obtain ⟨z, rfl⟩ := hsurj w
      exact congrArg (fun f => f z) h
    · intro h
      rw [h]
  obtain ⟨cardUnit, hcardUnit⟩ : ∃ cardUnit : Rˣ, (cardUnit : R) = Nat.card π.ker :=
    ⟨hunit.unit, by rw [IsUnit.unit_spec, Int.cast_natCast]⟩
  have hAadm := normalSubgroupCharacterSupport_admissible basis R π.ker cardUnit hcardUnit
  have hAmem : ∀ χ, χ ∈ normalSubgroupCharacterSupport basis π.ker ↔
      π.ker ≤ MonoidHom.ker (basis.representation χ).representation := by
    intro χ
    simp only [normalSubgroupCharacterSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h n => h n.property⟩
  have hclosed : ∀ χ, π.ker ≤ MonoidHom.ker (basis.representation χ).representation →
      ∀ ψ ∈ coefficientBlock basis R χ,
        π.ker ≤ MonoidHom.ker (basis.representation ψ).representation := by
    intro χ hχ ψ hψ
    rw [← hAmem]
    exact coefficientBlock_subset_admissible basis R _ hAadm χ ((hAmem χ).mpr hχ) hψ
  have hinfl : ∀ χ, π.ker ≤ MonoidHom.ker (basis.representation χ).representation ↔
      ∃ θ : quotientBasis.index,
        (basis.representation χ).character = (quotientBasis.representation θ).character ∘ π := by
    intro χ
    refine ⟨exists_inflation_of_ker_le π hπ basis quotientBasis χ, fun ⟨θ, hθ⟩ => ?_⟩
    exact ker_le_of_inflation π basis quotientBasis χ θ hθ
  have hprinInfl : (basis.representation principal).character =
      (quotientBasis.representation quotientPrincipal).character ∘ π := by
    rw [hprincipal, hquotientPrincipal]
    rfl
  refine ⟨fun χ => ?_, hsame, hclosed, hinfl⟩
  constructor
  · intro hχ
    have hker := hclosed principal ((hinfl principal).mpr ⟨_, hprinInfl⟩) χ hχ
    obtain ⟨θ, hθ⟩ := (hinfl χ).mp hker
    exact ⟨θ, (hsame principal χ quotientPrincipal θ hprinInfl hθ).mp hχ, hθ⟩
  · rintro ⟨θ, hθB, hθ⟩
    exact (hsame principal χ quotientPrincipal θ hprinInfl hθ).mpr hθB

theorem normal_prime_kernel_principal_block_inflation (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (N : Subgroup E) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) [Fintype (E ⧸ N)]
    (quotientBasis : FiniteIrreducibleCharacterBasis (E ⧸ N))
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (quotientPrincipal : quotientBasis.index)
    (hquotientPrincipal : (quotientBasis.representation quotientPrincipal).character = 1) :
    (∀ χ, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ↔
      ∃ θ ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) quotientPrincipal,
        (basis.representation χ).character =
          (quotientBasis.representation θ).character ∘ QuotientGroup.mk' N) ∧
    (∀ (χ χ' : basis.index) (θ θ' : quotientBasis.index),
      (basis.representation χ).character =
        (quotientBasis.representation θ).character ∘ QuotientGroup.mk' N →
      (basis.representation χ').character =
        (quotientBasis.representation θ').character ∘ QuotientGroup.mk' N →
      (χ' ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ ↔
        θ' ∈ coefficientBlock quotientBasis (localizedComplexIntegerRing ideal) θ)) ∧
    (∀ χ, N ≤ MonoidHom.ker (basis.representation χ).representation →
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) χ,
        N ≤ MonoidHom.ker (basis.representation ψ).representation) ∧
    (∀ χ, N ≤ MonoidHom.ker (basis.representation χ).representation ↔
      ∃ θ : quotientBasis.index, (basis.representation χ).character =
        (quotientBasis.representation θ).character ∘ QuotientGroup.mk' N) := by
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have h := normal_prime_kernel_principal_block_inflation_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) basis ideal p (by rw [hker]; exact hN) quotientBasis
    principal hprincipal quotientPrincipal hquotientPrincipal
  rw [hker] at h
  exact h

end CFSG.Semidihedral.Principal
