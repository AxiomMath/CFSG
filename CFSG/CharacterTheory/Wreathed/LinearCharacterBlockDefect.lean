module

public import CFSG.CharacterTheory.Wreathed.CoprimeClassUnitRatio
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBlockDefect
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionOrthogonality

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

variable {H : Type*} [Group H] [Fintype H]

theorem linear_character_class_residue_ne_zero_iff (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (ν : H →* ℂˣ) (label : basis.index)
    (hlabel : ∀ h, (basis.representation label).character h = ν h) (X : ConjClasses H) :
    centralCharacterResidueHom basis ideal label
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) X) ≠ 0 ↔
      ¬ p ∣ Nat.card X.carrier := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective X
  set k := (Subgroup.centralizer ({g} : Set H)).index with hk
  have hcard : Nat.card (ConjClasses.mk g).carrier = k :=
    CFSG.LyonsUnitaryFour.card_conjClass_eq_index g
  have hval : (localCentralCharacterHom basis ideal label
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)) : ℂ) =
        (k : ℂ) * ν g := by
    have h := centralCharacterScalar_conjugacyClassSum_mk basis g label
    rw [hlabel, hlabel, map_one, Units.val_one, div_one] at h
    exact h
  have hpow : (ν g : ℂ) ^ orderOf g = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have hmem : (ν g : ℂ) ∈ localizedComplexIntegerRing ideal :=
    rootOfUnity_mem_localizedComplexIntegerRing ideal (orderOf g) (orderOf_pos g) _ hpow
  set w : localizedComplexIntegerRing ideal := ⟨ν g, hmem⟩ with hw
  have hwunit : IsUnit w := by
    have hpow' : w ^ orderOf g = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow]
      exact hpow)
    exact IsUnit.of_pow_eq_one hpow' (orderOf_pos g).ne'
  have hwres : localizedComplexIntegerResidue ideal w ≠ 0 :=
    (localizedComplexIntegerResidue_isUnit_iff ideal w).mp hwunit
  have hloc : localCentralCharacterHom basis ideal label
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk g)) =
        (k : localizedComplexIntegerRing ideal) * w := by
    apply Subtype.ext
    rw [hval, Subring.coe_mul, Subring.coe_natCast]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal label _) ≠ 0 ↔ _
  rw [hloc, map_mul, map_natCast, hcard, mul_ne_zero_iff, ne_eq, CharP.cast_eq_zero_iff _ p]
  exact ⟨fun h => h.1, fun h => ⟨h, hwres⟩⟩

theorem linear_character_block_has_sylow_defect (basis : FiniteIrreducibleCharacterBasis H)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (ν : H →* ℂˣ) (label : basis.index)
    (hlabel : ∀ h, (basis.representation label).character h = ν h) (S : Sylow p H) :
    coefficientBlockDefect basis ideal p label (S : Subgroup H) ∧
      ∀ X : ConjClasses H, centralCharacterResidueHom basis ideal label
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) X) ≠ 0 ↔
        ¬ p ∣ Nat.card X.carrier := by
  have hp : p.Prime := Fact.out
  have hiff := linear_character_class_residue_ne_zero_iff basis ideal p ν label hlabel
  have hsylow : subgroupIsSylow p (S : Subgroup H) := ⟨S, rfl⟩
  have hidentity : (S : Subgroup H) ≤ Subgroup.centralizer ({(1 : H)} : Set H) := by
    intro element _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  refine ⟨⟨⟨ConjClasses.mk (1 : H), classDefect_of_sylow_centralizes p hsylow 1 hidentity, ?_⟩,
    fun X Q hclass hvalue => ?_⟩, hiff⟩
  · rw [hiff]
    have h1 : Nat.card (ConjClasses.mk (1 : H)).carrier = 1 := by
      rw [CFSG.LyonsUnitaryFour.card_conjClass_eq_index]
      rw [show Subgroup.centralizer ({(1 : H)} : Set H) = ⊤ from by
        ext x
        simp [Subgroup.mem_centralizer_singleton_iff], Subgroup.index_top]
    rw [h1]
    exact hp.not_dvd_one
  · have hsize : conjugacyClassSize X = Nat.card X.carrier := by
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective X
      rw [conjugacyClassSize_centralizer_index, CFSG.LyonsUnitaryFour.card_conjClass_eq_index]
    have hQ : subgroupIsSylow p Q :=
      (classDefect_sylow_iff_class_size p hclass).mpr (hsize ▸ (hiff X).mp hvalue)
    exact subgroupIsSylow_subconjugate p hsylow hQ

end CFSG.Wreathed
