module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassProducts
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem localMaxIdeal_mul_not_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {left right : ℂ} (hleftRing : left ∈ BlocksLocalRing m)
    (hrightRing : right ∈ BlocksLocalRing m)
    (hleft : left ∉ BlocksLocalMaxIdeal m) (hright : right ∉ BlocksLocalMaxIdeal m) :
    left * right ∉ BlocksLocalMaxIdeal m := by
  have hleftResidue : localResidue m hm ⟨left, hleftRing⟩ ≠ 0 :=
    fun hequal => hleft ((localResidue_eq_zero_iff m hm _).mp hequal)
  have hrightResidue : localResidue m hm ⟨right, hrightRing⟩ ≠ 0 :=
    fun hequal => hright ((localResidue_eq_zero_iff m hm _).mp hequal)
  intro hproduct
  have hzero := (localResidue_eq_zero_iff m hm
    (⟨left, hleftRing⟩ * ⟨right, hrightRing⟩)).mpr hproduct
  rw [map_mul] at hzero
  exact mul_ne_zero hleftResidue hrightResidue hzero

theorem localRing_natCast (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (number : ℕ) :
    (number : ℂ) ∈ BlocksLocalRing m := by
  simpa only [SubringClass.coe_natCast] using localRing_of_algInt m hm (number : BlocksAlgInt)

theorem localMaxIdeal_natCast_of_dvd (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (prime : ℕ) (hprimeMem : (prime : BlocksAlgInt) ∈ m) {number : ℕ}
    (hdivides : prime ∣ number) : (number : ℂ) ∈ BlocksLocalMaxIdeal m := by
  obtain ⟨multiple, rfl⟩ := hdivides
  rw [Nat.cast_mul]
  exact localMaxIdeal_mul_localRing m hm (localMaxIdeal_of_mem m hm hprimeMem)
    (localRing_natCast m hm multiple)

theorem classCoefficients_one {G : Type*} [Group G] :
    classCoefficients (ConjClasses.mk (1 : G)) = (identityCoefficients : G → ℂ) := by
  ext element
  have hclass : ConjClasses.mk element = ConjClasses.mk (1 : G) ↔ element = 1 := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    constructor
    · rintro ⟨conjugator, hequal⟩
      have hcancel := congrArg (fun value => conjugator⁻¹ * value * conjugator) hequal
      have hnormal : conjugator⁻¹ * (conjugator * element * conjugator⁻¹) *
          conjugator = element := by group
      simpa only [hnormal, mul_one, inv_mul_cancel] using hcancel
    · rintro rfl
      exact ⟨1, by simp⟩
  simp only [classCoefficients, identityCoefficients, hclass]
  by_cases hequal : element = 1
  · simp only [hequal, ↓reduceIte]
  · simp only [hclass.not.mpr hequal, hequal, ↓reduceIte]

theorem centralChar_classProduct_nonzero_term
    (prime : ℕ) (_hprime : prime.Prime) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type*) [Group G] [Finite G]
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G)
    (left right : ConjClasses G)
    (hleft : BlocksCentralChar character (classCoefficients left) ∉ BlocksLocalMaxIdeal m)
    (hright : BlocksCentralChar character (classCoefficients right) ∉ BlocksLocalMaxIdeal m) :
    ∃ element : G,
      BlocksCentralChar character (classCoefficients (ConjClasses.mk element)) ∉
        BlocksLocalMaxIdeal m ∧ ¬ prime ∣ classProductCount left right element := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  choose representatives hrepresentatives using (fun conjugacyClass : ConjClasses G =>
    ConjClasses.exists_rep conjugacyClass)
  have hleftCentral := classCoefficients_central m hm left
  have hrightCentral := classCoefficients_central m hm right
  have hproduct := localMaxIdeal_mul_not_mem m hm
    (centralChar_localRing m hm hcharacter hleftCentral)
    (centralChar_localRing m hm hcharacter hrightCentral) hleft hright
  rw [← centralChar_convolution hcharacter _ _ hleftCentral.2 hrightCentral.2,
    central_class_expansion _
      (coefficientConvolution_central m hm hleftCentral hrightCentral).2
      representatives hrepresentatives, finsum_eq_sum_of_fintype,
    centralChar_sum] at hproduct
  have hterm : ∃ conjugacyClass : ConjClasses G,
      BlocksCentralChar character
        (coefficientConvolution (classCoefficients left) (classCoefficients right)
          (representatives conjugacyClass) • classCoefficients conjugacyClass) ∉
          BlocksLocalMaxIdeal m := by
    by_contra hnotExists
    push Not at hnotExists
    exact hproduct (localMaxIdeal_sum m hm Finset.univ _
      (fun conjugacyClass _ => hnotExists conjugacyClass))
  obtain ⟨conjugacyClass, hterm⟩ := hterm
  rw [centralChar_smul, classProductCount_convolution] at hterm
  refine ⟨representatives conjugacyClass, ?_, ?_⟩
  · rw [hrepresentatives]
    intro hzero
    exact hterm (by
      rw [mul_comm]
      exact localMaxIdeal_mul_localRing m hm hzero (localRing_natCast m hm _))
  · intro hdivides
    exact hterm (localMaxIdeal_mul_localRing m hm
      (localMaxIdeal_natCast_of_dvd m hm prime hprimeMem hdivides)
      (centralChar_localRing m hm hcharacter (classCoefficients_central m hm conjugacyClass)))

theorem blockDefect_exists (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type*) [Group G] [Finite G] {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) :
    ∃ defect : Subgroup G, blockDefect prime m character defect := by
  classical
  let candidates : ℕ → Prop := fun size => ∃ conjugacyClass : ConjClasses G,
    ∃ defect : Subgroup G, Nat.card defect = size ∧
      classDefect prime conjugacyClass defect ∧
      BlocksCentralChar character (classCoefficients conjugacyClass) ∉ BlocksLocalMaxIdeal m
  have hexists : ∃ size, candidates size := by
    obtain ⟨defect, hdefect⟩ := classDefect_exists prime (ConjClasses.mk (1 : G))
    refine ⟨Nat.card defect, ConjClasses.mk 1, defect, rfl, hdefect, ?_⟩
    rw [classCoefficients_one, centralChar_identityCoefficients hcharacter]
    exact localMaxIdeal_one_not m
  obtain ⟨conjugacyClass, defect, hsize, hdefect, hnonzero⟩ := Nat.find_spec hexists
  refine ⟨defect, ⟨conjugacyClass, hdefect, hnonzero⟩, ?_⟩
  intro otherClass hotherNonzero otherDefect hotherDefect
  obtain ⟨element, hproductNonzero, hcount⟩ := centralChar_classProduct_nonzero_term
    prime hprime m hm hprimeMem G hcharacter conjugacyClass otherClass hnonzero hotherNonzero
  obtain ⟨productDefect, hproductDefect⟩ := classDefect_exists prime (ConjClasses.mk element)
  obtain ⟨hproductLeft, hproductRight⟩ := classProduct_defect_containment prime hprime
    conjugacyClass otherClass element hcount hproductDefect hdefect hotherDefect
  have hminimal : Nat.card defect ≤ Nat.card productDefect := by
    rw [hsize]
    exact Nat.find_min' hexists
      ⟨ConjClasses.mk element, productDefect, rfl, hproductDefect, hproductNonzero⟩
  exact subgroupSubconjugate_trans
    (subgroupSubconjugate_symm_of_card_le hproductLeft hminimal) hproductRight

end CFSG.BrauerThirdMainTheorem.Helpers
