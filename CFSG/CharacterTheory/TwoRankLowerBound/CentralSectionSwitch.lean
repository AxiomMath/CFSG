module

public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualCharacters

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def centralInvolutionSections {G : Type*} [Group G] (involution : G) : Set G :=
  {element | Odd (orderOf element) ∨ Odd (orderOf (element * involution))}

@[expose] noncomputable def centralSectionSwitch {G : Type*} [Group G] (involution : G)
    (function : G → ℂ) : G → ℂ :=
  fun element => if Odd (orderOf element) then function element
    else if Odd (orderOf (element * involution)) then -function element else 0

theorem central_involution_translate_twice {G : Type*} [Group G]
    (involution : G) (hsquare : involution ^ 2 = 1) (element : G) :
    element * involution * involution = element := by
  rw [mul_assoc, ← pow_two, hsquare, mul_one]

theorem central_involution_odd_translate_not_odd {G : Type*} [Group G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (horder : orderOf involution = 2) (element : G) (hodd : Odd (orderOf element)) :
    ¬Odd (orderOf (element * involution)) := by
  have hcommute : Commute element involution := Subgroup.mem_center_iff.mp hcentral element
  rw [hcommute.orderOf_mul_eq_mul_orderOf_of_coprime (horder ▸ hodd.coprime_two_right), horder]
  exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_mul_left 2 (orderOf element)))

theorem centralInvolutionSections_translate_iff {G : Type*} [Group G]
    (involution : G) (hsquare : involution ^ 2 = 1) (element : G) :
    element * involution ∈ centralInvolutionSections involution ↔
      element ∈ centralInvolutionSections involution := by
  simp only [centralInvolutionSections, Set.mem_ofPred_eq,
    central_involution_translate_twice involution hsquare element, or_comm]

theorem centralInvolutionSections_inverse_iff {G : Type*} [Group G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) (element : G) :
    element⁻¹ ∈ centralInvolutionSections involution ↔ element ∈ centralInvolutionSections involution := by
  have hinverse : involution⁻¹ = involution := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using hsquare)
  have hequal : element⁻¹ * involution = (element * involution)⁻¹ := by
    rw [mul_inv_rev, hinverse, Subgroup.mem_center_iff.mp hcentral element⁻¹]
  simp only [centralInvolutionSections, Set.mem_ofPred_eq, hequal, orderOf_inv]

theorem centralSectionSwitch_supported {G : Type*} [Group G] (involution : G)
    (function : G → ℂ) (element : G) (hnot : element ∉ centralInvolutionSections involution) :
    centralSectionSwitch involution function element = 0 := by
  have hnotOdd : ¬Odd (orderOf element) := fun hodd => hnot (Or.inl hodd)
  have hnotTranslate : ¬Odd (orderOf (element * involution)) := fun hodd => hnot (Or.inr hodd)
  simp only [centralSectionSwitch, ite_eq_right hnotOdd, ite_eq_right hnotTranslate]

theorem centralSectionSwitch_squared {G : Type*} [Group G] (involution : G)
    (function : G → ℂ)
    (hsupport : ∀ element, element ∉ centralInvolutionSections involution → function element = 0) :
    centralSectionSwitch involution (centralSectionSwitch involution function) = function := by
  ext element
  by_cases hodd : Odd (orderOf element)
  · simp only [centralSectionSwitch, ite_eq_left hodd]
  · by_cases htranslate : Odd (orderOf (element * involution))
    · simp only [centralSectionSwitch, ite_eq_right hodd, ite_eq_left htranslate, neg_neg]
    · have hzero := hsupport element (by
        rintro (hoddElement | hoddTranslate)
        · exact hodd hoddElement
        · exact htranslate hoddTranslate)
      simp only [centralSectionSwitch, ite_eq_right hodd, ite_eq_right htranslate, hzero]

theorem centralSectionSwitch_reverses_parity {G : Type*} [Group G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G) (horder : orderOf involution = 2)
    (function : G → ℂ) (parity : ℂ)
    (hparity : ∀ element, function (element * involution) = parity * function element) (element : G) :
    centralSectionSwitch involution function (element * involution) =
      -parity * centralSectionSwitch involution function element := by
  have hsquare := (orderOf_eq_prime_iff.mp horder).1
  have htwice := central_involution_translate_twice involution hsquare element
  by_cases hodd : Odd (orderOf element)
  · have hnot := central_involution_odd_translate_not_odd involution hcentral horder element hodd
    simp only [centralSectionSwitch, ite_eq_right hnot, htwice, ite_eq_left hodd, hparity, neg_mul]
  · by_cases htranslate : Odd (orderOf (element * involution))
    · simp only [centralSectionSwitch, ite_eq_left htranslate, ite_eq_right hodd, hparity, neg_mul_neg]
    · simp only [centralSectionSwitch, ite_eq_right htranslate, htwice, ite_eq_right hodd, mul_zero]

theorem centralSectionSwitch_pairing {G : Type*} [Group G] [Fintype G]
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) (left right : G → ℂ)
    (hsupport : ∀ element, element ∉ centralInvolutionSections involution → left element = 0) :
    characterPairing (centralSectionSwitch involution left) (centralSectionSwitch involution right) =
      characterPairing left right := by
  have hinverse : involution⁻¹ = involution := inv_eq_of_mul_eq_one_left (by
    simpa only [pow_two] using hsquare)
  have hequal : ∀ element : G, element⁻¹ * involution = (element * involution)⁻¹ := by
    intro element
    rw [mul_inv_rev, hinverse, Subgroup.mem_center_iff.mp hcentral element⁻¹]
  unfold characterPairing
  congr 1
  apply Finset.sum_congr rfl
  intro element _
  by_cases hodd : Odd (orderOf element)
  · simp only [centralSectionSwitch, orderOf_inv, ite_eq_left hodd]
  · by_cases htranslate : Odd (orderOf (element * involution))
    · simp only [centralSectionSwitch, hequal, orderOf_inv, ite_eq_right hodd, ite_eq_left htranslate, neg_mul_neg]
    · have hzero := hsupport element (by
        rintro (hoddElement | hoddTranslate)
        · exact hodd hoddElement
        · exact htranslate hoddTranslate)
      simp only [centralSectionSwitch, hequal, orderOf_inv, ite_eq_right hodd, ite_eq_right htranslate, hzero, zero_mul]

noncomputable def centralSectionSwitchLinearMap {G : Type*} [Group G] (involution : G) :
    (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := centralSectionSwitch involution
  map_add' := by
    intro left right
    ext element
    simp only [centralSectionSwitch, Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro scalar function
    ext element
    simp only [centralSectionSwitch, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem centralSectionSwitch_zsmul {G : Type*} [Group G] (involution : G)
    (integer : ℤ) (function : G → ℂ) :
    centralSectionSwitch involution (integer • function) =
      integer • centralSectionSwitch involution function := by
  ext element
  simp only [centralSectionSwitch, Pi.smul_apply, zsmul_eq_mul]
  split_ifs <;> ring

theorem centralSectionSwitch_equiv {source target : Type*} [Group source] [Group target]
    (isomorphism : source ≃* target) (involution : source) (function : target → ℂ) :
    centralSectionSwitch involution (function ∘ isomorphism) =
      centralSectionSwitch (isomorphism involution) function ∘ isomorphism := by
  ext element
  simp only [centralSectionSwitch, Function.comp_apply, ← map_mul, isomorphism.orderOf_eq]

@[expose] def centralSectionParityLattice {G : Type*} [Group G] (involution : G) (parity : ℂ) :
    Submodule ℤ (G → ℂ) where
  carrier := {function | function ∈ virtualCharacters G ∧
    (∀ element, element ∉ centralInvolutionSections involution → function element = 0) ∧
    ∀ element, function (element * involution) = parity * function element}
  zero_mem' := by simp
  add_mem' := by
    rintro left right ⟨hleft, hleftSupport, hleftParity⟩ ⟨hright, hrightSupport, hrightParity⟩
    refine ⟨Submodule.add_mem _ hleft hright, ?_, ?_⟩
    · intro element hnot
      simp only [Pi.add_apply, hleftSupport element hnot, hrightSupport element hnot, add_zero]
    · intro element
      simp only [Pi.add_apply, hleftParity, hrightParity, mul_add]
  smul_mem' := by
    rintro scalar function ⟨hvirtual, hsupport, hparity⟩
    refine ⟨Submodule.smul_mem _ scalar hvirtual, ?_, ?_⟩
    · intro element hnot
      simp only [Pi.smul_apply, hsupport element hnot, smul_zero]
    · intro element
      simp only [Pi.smul_apply, zsmul_eq_mul, hparity]
      ring

end CFSG.TwoRankLowerBound.Helpers
