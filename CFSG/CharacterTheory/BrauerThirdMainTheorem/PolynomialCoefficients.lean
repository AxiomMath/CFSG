module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Characters
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Convolution
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalCoefficientRing

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def identityCoefficients {G : Type*} [Group G] : G → ℂ :=
  fun element => if element = 1 then 1 else 0

theorem identityCoefficients_central {G : Type*} [Group G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) :
    BlocksIsCentralR m (identityCoefficients : G → ℂ) := by
  classical
  constructor
  · intro element
    unfold identityCoefficients
    split_ifs
    · exact localRing_one m hm
    · exact localRing_zero m hm
  · intro element conjugator
    have hone : conjugator * element * conjugator⁻¹ = 1 ↔ element = 1 := by
      constructor
      · intro hequal
        have hconjugated := congrArg (fun value : G => conjugator⁻¹ * value * conjugator) hequal
        convert hconjugated using 1 <;> group
      · rintro rfl
        group
    simp only [identityCoefficients, hone]

theorem centralChar_identityCoefficients {G : Type*} [Group G] [Finite G]
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G) :
    BlocksCentralChar character identityCoefficients = 1 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  unfold BlocksCentralChar
  rw [finsum_eq_sum_of_fintype]
  simp only [identityCoefficients, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ 1)]
  exact div_self (irr_degree_ne_zero hcharacter)

theorem centralR_smul {G : Type*} [Group G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {coefficients : G → ℂ}
    (hcoefficients : BlocksIsCentralR m coefficients) {scalar : ℂ}
    (hscalar : scalar ∈ BlocksLocalRing m) :
    BlocksIsCentralR m (scalar • coefficients) := by
  constructor
  · intro element
    exact localRing_mul m hm hscalar (hcoefficients.1 element)
  · intro element conjugator
    change scalar * coefficients (conjugator * element * conjugator⁻¹) =
      scalar * coefficients element
    rw [hcoefficients.2]

theorem centralR_sum {G : Type*} [Group G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {index : Type*}
    (indices : Finset index) (coefficients : index → G → ℂ)
    (hcoefficients : ∀ entry ∈ indices, BlocksIsCentralR m (coefficients entry)) :
    BlocksIsCentralR m (∑ entry ∈ indices, coefficients entry) := by
  constructor
  · intro element
    simp only [Finset.sum_apply]
    exact localRing_sum m hm indices _ (fun entry hentry => (hcoefficients entry hentry).1 element)
  · intro element conjugator
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun entry hentry => (hcoefficients entry hentry).2 element conjugator)

@[expose] noncomputable def coefficientPower {G : Type*} [Group G] [Finite G]
    (coefficients : G → ℂ) : ℕ → G → ℂ
  | 0 => identityCoefficients
  | exponent + 1 => coefficientConvolution coefficients (coefficientPower coefficients exponent)

theorem coefficientPower_central {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {coefficients : G → ℂ}
    (hcoefficients : BlocksIsCentralR m coefficients) (exponent : ℕ) :
    BlocksIsCentralR m (coefficientPower coefficients exponent) := by
  induction exponent with
  | zero => exact identityCoefficients_central m hm
  | succ exponent hinduction =>
      exact coefficientConvolution_central m hm hcoefficients hinduction

theorem centralChar_coefficientPower {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (hcoefficients : BlocksIsCentralR m coefficients)
    (exponent : ℕ) :
    BlocksCentralChar character (coefficientPower coefficients exponent) =
      BlocksCentralChar character coefficients ^ exponent := by
  induction exponent with
  | zero => simpa only [coefficientPower, pow_zero] using centralChar_identityCoefficients hcharacter
  | succ exponent hinduction =>
      rw [coefficientPower, centralChar_convolution hcharacter _ _ hcoefficients.2
        (coefficientPower_central m hm hcoefficients exponent).2, hinduction, pow_succ']

noncomputable def polynomialCoefficients {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (coefficients : G → ℂ)
    (polynomial : Polynomial (localCoefficientSubring m hm)) : G → ℂ :=
  ∑ exponent ∈ Finset.range (polynomial.natDegree + 1),
    (polynomial.coeff exponent : ℂ) • coefficientPower coefficients exponent

theorem polynomialCoefficients_central {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {coefficients : G → ℂ}
    (hcoefficients : BlocksIsCentralR m coefficients)
    (polynomial : Polynomial (localCoefficientSubring m hm)) :
    BlocksIsCentralR m (polynomialCoefficients m hm coefficients polynomial) := by
  apply centralR_sum m hm
  intro exponent _
  exact centralR_smul m hm (coefficientPower_central m hm hcoefficients exponent)
    (polynomial.coeff exponent).property

theorem centralChar_polynomialCoefficients {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (hcoefficients : BlocksIsCentralR m coefficients)
    (polynomial : Polynomial (localCoefficientSubring m hm)) :
    BlocksCentralChar character (polynomialCoefficients m hm coefficients polynomial) =
      Polynomial.eval₂ (localCoefficientSubring m hm).subtype
        (BlocksCentralChar character coefficients) polynomial := by
  unfold polynomialCoefficients
  rw [centralChar_sum, Polynomial.eval₂_eq_sum_range]
  apply Finset.sum_congr rfl
  intro exponent _
  rw [centralChar_smul, centralChar_coefficientPower m hm hcharacter hcoefficients]
  rfl

end CFSG.BrauerThirdMainTheorem.Helpers
