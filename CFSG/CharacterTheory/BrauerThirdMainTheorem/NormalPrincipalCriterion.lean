module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalCentralizerProjection

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem commonCentral_principal_iff (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (small large : Type) [Group small] [Group large] [Finite small] [Finite large]
    (subgroup : Subgroup large) [subgroup.Normal] (hpGroup : IsPGroup prime subgroup)
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (hrange : Set.range inclusion = (Subgroup.centralizer (subgroup : Set large) : Set large))
    (hconjugation : ∀ conjugator : large, ∃ equivalence : small ≃* small,
      ∀ element : small, inclusion (equivalence element) = conjugator * inclusion element * conjugator⁻¹)
    (smallCharacter : BlocksIrr small) (character : BlocksIrr large)
    (hrestriction : ∀ value : commonCentralAlgebra m hm small large inclusion,
      centralResidue m hm large character (commonCentralInclusion m hm small large inclusion value) =
        centralResidue m hm small smallCharacter value.val) :
    character.val ∈ BlocksPrincipalBlock m large ↔ smallCharacter.val ∈ BlocksPrincipalBlock m small := by
  classical
  constructor
  · intro hprincipal
    let : Fintype small := Fintype.ofFinite _
    have hadmissible := block_admissible m hm small (principal_isBlock m small)
    let coefficients := BlocksIdempotentCoeff small (BlocksPrincipalBlock m small)
    let value := centralLocalElement m hm small coefficients (idempotentCoeff_central m small hadmissible)
    have hcommon := principalLocalElement_invariant m hm small large inclusion hinjective hconjugation
    have hequal := hrestriction ⟨value, hcommon⟩
    have hcongr := (localResidue_eq_iff m hm _ _).mp hequal
    change BlocksCentralChar character.val (centralLocalCoefficients m hm large
      (commonCentralInclusion m hm small large inclusion ⟨value, hcommon⟩)) -
        BlocksCentralChar smallCharacter.val (centralLocalCoefficients m hm small value) ∈
          BlocksLocalMaxIdeal m at hcongr
    have hprincipalScalar := principal_centralChar_congr m hm large hprincipal
      (centralLocalCoefficients_central m hm large
        (commonCentralInclusion m hm small large inclusion ⟨value, hcommon⟩))
    rw [commonCentralInclusion_augmentation m hm small large inclusion hinjective ⟨value, hcommon⟩,
      centralLocalElement_coefficients,
      centralChar_idempotentCoeff hadmissible.1 (trivial_mem_irr small),
      ite_eq_left (trivial_mem_principal m small)] at hprincipalScalar
    rw [centralLocalElement_coefficients,
      centralChar_idempotentCoeff hadmissible.1 smallCharacter.property] at hcongr
    by_contra hnotPrincipal
    rw [ite_eq_right hnotPrincipal, sub_zero] at hcongr
    have hnegative : -BlocksCentralChar character.val (centralLocalCoefficients m hm large
      (commonCentralInclusion m hm small large inclusion ⟨value, hcommon⟩)) ∈ BlocksLocalMaxIdeal m :=
      localMaxIdeal_neg m hcongr
    have hminusOne : (-1 : ℂ) ∈ BlocksLocalMaxIdeal m := by
      convert localMaxIdeal_add m hm hprincipalScalar hnegative using 1
      ring
    exact localMaxIdeal_one_not m (by simpa only [neg_neg] using localMaxIdeal_neg m hminusOne)
  · intro hprincipal
    apply centralResidue_common_principal prime hprime m hm hprimeMem small large subgroup hpGroup
      inclusion hinjective hrange character
    intro value
    rw [hrestriction]
    exact congrArg (fun residue => residue value.val)
      (centralResidue_sameBlock m hm small smallCharacter ⟨fun _ => 1, trivial_mem_irr small⟩
        (mem_blockOf_symm m (trivial_mem_irr small) hprincipal))

end CFSG.BrauerThirdMainTheorem.Helpers
