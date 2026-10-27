module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralIntegrality
public import Mathlib.Algebra.Group.ConjFinite

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def classCoefficients {G : Type*} [Group G] (conjugacyClass : ConjClasses G) : G → ℂ :=
  fun element => if ConjClasses.mk element = conjugacyClass then 1 else 0

theorem classCoefficients_central {G : Type*} [Group G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (conjugacyClass : ConjClasses G) :
    BlocksIsCentralR m (classCoefficients conjugacyClass) := by
  classical
  constructor
  · intro element
    unfold classCoefficients
    split_ifs
    · exact localRing_one m hm
    · exact localRing_zero m hm
  · intro element conjugator
    have hequal : ConjClasses.mk (conjugator * element * conjugator⁻¹) = ConjClasses.mk element :=
      ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨conjugator, rfl⟩).symm
    simp only [classCoefficients, hequal]

theorem central_class_expansion {G : Type*} [Group G] [Finite G]
    (coefficients : G → ℂ) (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element)
    (representatives : ConjClasses G → G)
    (hrepresentatives : ∀ conjugacyClass, ConjClasses.mk (representatives conjugacyClass) = conjugacyClass) :
    coefficients = ∑ᶠ conjugacyClass : ConjClasses G,
      coefficients (representatives conjugacyClass) • classCoefficients conjugacyClass := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  ext element
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, classCoefficients, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (ConjClasses.mk element)]
  · have hconjugate : IsConj (representatives (ConjClasses.mk element)) element :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hrepresentatives _)
    obtain ⟨conjugator, hconjugator⟩ := isConj_iff.mp hconjugate
    rw [ite_eq_left rfl]
    exact (congrArg coefficients hconjugator).symm.trans
      (hcentral (representatives (ConjClasses.mk element)) conjugator)
  · intro other _ hother
    exact ite_eq_right (Ne.symm hother)
  · intro hnotMember
    exact (hnotMember (Finset.mem_univ _)).elim

theorem centralChar_maxIdeal_coefficients {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {character coefficients : G → ℂ} (hcharacter : character ∈ BlocksIrr G)
    (hcoefficients : ∀ element, coefficients element ∈ BlocksLocalMaxIdeal m)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element) :
    BlocksCentralChar character coefficients ∈ BlocksLocalMaxIdeal m := by
  classical
  let : Fintype (ConjClasses G) := Fintype.ofFinite _
  choose representatives hrepresentatives using (fun conjugacyClass : ConjClasses G =>
    ConjClasses.exists_rep conjugacyClass)
  rw [central_class_expansion coefficients hcentral representatives hrepresentatives,
    finsum_eq_sum_of_fintype, centralChar_sum]
  apply localMaxIdeal_sum m hm
  intro conjugacyClass _
  rw [centralChar_smul]
  exact localMaxIdeal_mul_localRing m hm (hcoefficients _)
    (centralChar_localRing m hm hcharacter (classCoefficients_central m hm conjugacyClass))

end CFSG.BrauerThirdMainTheorem.Helpers
