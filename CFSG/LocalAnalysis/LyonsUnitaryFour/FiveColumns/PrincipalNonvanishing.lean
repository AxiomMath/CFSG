module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralClassCoordinates
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCharacterResidueCriterion

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem card_conjClass_mul_card_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier * Nat.card (Subgroup.centralizer ({g} : Set G)) =
      Nat.card G := by
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have hst' : Fintype.card (ConjClasses.mk g).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) g) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact hst'

theorem card_conjClass_eq_index (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer ({g} : Set G)).index := by
  have h1 := card_conjClass_mul_card_centralizer g
  have h2 := (Subgroup.centralizer ({g} : Set G)).card_mul_index
  have hpos : 0 < Nat.card (Subgroup.centralizer ({g} : Set G)) := Nat.card_pos
  rw [← h2, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left hpos h1

theorem centralCharacterScalar_conjugacyClassSum (basis : FiniteIrreducibleCharacterBasis G)
    (c : ConjClasses G) (label : basis.index) :
    centralCharacterScalar basis (conjugacyClassSum c) label =
      (∑ g : G, if ConjClasses.mk g = c then (basis.representation label).character g else 0) /
        (basis.representation label).character 1 := by
  unfold centralCharacterScalar characterPairing
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
  simp only [Equiv.inv_apply, conjugacyClassSum_coeff]
  split_ifs <;> ring

theorem principal_block_character_ne_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) (x : G)
    (hx : ¬ p ∣ (Subgroup.centralizer ({x} : Set G)).index) :
    centralCharacterResidueHom basis ideal χ
        (centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk x)) ≠ 0 ∧
      (basis.representation χ).character x ≠ 0 := by
  set v := centralConjugacyClassSum (localizedComplexIntegerRing ideal) (ConjClasses.mk x) with hv
  have hsame : centralCharacterResidueHom basis ideal χ =
      centralCharacterResidueHom basis ideal principal :=
    (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal χ principal).mp
      (sameCoefficientBlock_symm basis _ ((coefficientBlock_mem_iff _ _ _ _).mp hχ))
  have hclass : (∑ g : G, if ConjClasses.mk g = ConjClasses.mk x then (1 : ℂ) else 0) =
      ((Subgroup.centralizer ({x} : Set G)).index : ℂ) := by
    rw [← card_conjClass_eq_index, Finset.sum_boole]
    congr 1
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq]
  have hprincipalValue : (localCentralCharacterHom basis ideal principal v : ℂ) =
      ((Subgroup.centralizer ({x} : Set G)).index : ℂ) := by
    rw [localCentralCharacterHom_coe, hv]
    change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk x)) principal = _
    rw [centralCharacterScalar_conjugacyClassSum, hprincipal]
    simp only [Pi.one_apply, div_one]
    exact hclass
  have hprincipalResidue : centralCharacterResidueHom basis ideal principal v ≠ 0 := by
    change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal principal v)
      ≠ 0
    have heq : localCentralCharacterHom basis ideal principal v =
        ((Subgroup.centralizer ({x} : Set G)).index : localizedComplexIntegerRing ideal) := by
      apply Subtype.ext
      rw [hprincipalValue]
      simp
    rw [heq, map_natCast]
    intro hzero
    exact hx ((CharP.cast_eq_zero_iff (ComplexAlgebraicIntegers ⧸ ideal) p _).mp hzero)
  refine ⟨by rw [hsame]; exact hprincipalResidue, ?_⟩
  intro hzero
  apply hprincipalResidue
  rw [← hsame]
  change localizedComplexIntegerResidue ideal (localCentralCharacterHom basis ideal χ v) = 0
  have hval : localCentralCharacterHom basis ideal χ v = 0 := by
    apply Subtype.ext
    rw [localCentralCharacterHom_coe, hv]
    change centralCharacterScalar basis (conjugacyClassSum (ConjClasses.mk x)) χ = 0
    rw [centralCharacterScalar_conjugacyClassSum]
    have hsum : (∑ g : G, if ConjClasses.mk g = ConjClasses.mk x then
        (basis.representation χ).character g else 0) = 0 := by
      refine Finset.sum_eq_zero fun g _ => ?_
      split_ifs with hg
      · obtain ⟨c, hc⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hg).symm
        rw [← hc]
        exact (Representation.char_conj _ x c).trans hzero
      · rfl
    rw [hsum, zero_div]
  rw [hval, map_zero]

theorem principal_block_character_ne_zero_of_centralizes_sylow
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (χ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (P : Sylow p G) (x : G) (hx : x ∈ Subgroup.centralizer ((P : Subgroup G) : Set G)) :
    (basis.representation χ).character x ≠ 0 := by
  refine (principal_block_character_ne_zero basis ideal p principal hprincipal χ hχ x ?_).2
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hx) s hs)
  intro hdvd
  exact P.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le hle))

end CFSG.LyonsUnitaryFour
