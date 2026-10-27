module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PolynomialCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassCoefficients
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Spectral

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem coefficientAlgebra_convolution {G : Type*} [Group G] [Fintype G]
    (left right : G → ℂ) :
    coefficientAlgebra (coefficientConvolution left right) =
      coefficientAlgebra left * coefficientAlgebra right := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro element
  rw [coefficientAlgebra_coeff, MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · simp only [coefficientAlgebra_coeff, coefficientConvolution_apply]
  · intro _
    exact zero_mul _

theorem coefficientAlgebra_identity {G : Type*} [Group G] [Fintype G] :
    coefficientAlgebra (identityCoefficients : G → ℂ) = 1 := by
  classical
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro element
  rw [coefficientAlgebra_coeff]
  change (if element = 1 then (1 : ℂ) else 0) = (MonoidAlgebra.single 1 1).coeff element
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hequal : element = 1 <;> simp [hequal, Ne.symm]

theorem coefficientAlgebra_power {G : Type*} [Group G] [Fintype G]
    (coefficients : G → ℂ) (exponent : ℕ) :
    coefficientAlgebra (coefficientPower coefficients exponent) =
      coefficientAlgebra coefficients ^ exponent := by
  induction exponent with
  | zero => exact coefficientAlgebra_identity
  | succ exponent hinduction =>
      rw [coefficientPower, coefficientAlgebra_convolution, hinduction, pow_succ']

@[expose] noncomputable def localCoefficientAlgebra {G : Type*} [Group G] [Fintype G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (coefficients : G → ℂ)
    (hcoefficients : ∀ element, coefficients element ∈ BlocksLocalRing m) :
    MonoidAlgebra (localCoefficientSubring m hm) G :=
  ∑ element : G, MonoidAlgebra.single element ⟨coefficients element, hcoefficients element⟩

theorem localCoefficientAlgebra_coeff {G : Type*} [Group G] [Fintype G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (coefficients : G → ℂ)
    (hcoefficients : ∀ element, coefficients element ∈ BlocksLocalRing m) (element : G) :
    (localCoefficientAlgebra m hm coefficients hcoefficients).coeff element =
      ⟨coefficients element, hcoefficients element⟩ := by
  classical
  simp only [localCoefficientAlgebra, MonoidAlgebra.coeff_sum, Finset.sum_apply',
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Fintype.sum_ite_eq']

theorem localCoefficientAlgebra_complex {G : Type*} [Group G] [Fintype G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (coefficients : G → ℂ)
    (hcoefficients : ∀ element, coefficients element ∈ BlocksLocalRing m) :
    MonoidAlgebra.mapRingHom G (localCoefficientSubring m hm).subtype
      (localCoefficientAlgebra m hm coefficients hcoefficients) = coefficientAlgebra coefficients := by
  classical
  simp only [localCoefficientAlgebra, map_sum, MonoidAlgebra.mapRingHom_single,
    Subring.coe_subtype, coefficientAlgebra]

theorem centralChar_residue_nilpotent (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Fintype G] {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (hcoefficients : BlocksIsCentralR m coefficients)
    (hnilpotent : IsNilpotent (MonoidAlgebra.mapRingHom G (localResidue m hm)
      (localCoefficientAlgebra m hm coefficients hcoefficients.1))) :
    BlocksCentralChar character coefficients ∈ BlocksLocalMaxIdeal m := by
  classical
  obtain ⟨exponent, hexponent⟩ := hnilpotent
  let localElement := localCoefficientAlgebra m hm coefficients hcoefficients.1
  have hcomplex : MonoidAlgebra.mapRingHom G (localCoefficientSubring m hm).subtype
      (localElement ^ exponent) = coefficientAlgebra (coefficientPower coefficients exponent) := by
    rw [map_pow, localCoefficientAlgebra_complex, coefficientAlgebra_power]
  have hcoeffMax : ∀ element,
      coefficientPower coefficients exponent element ∈ BlocksLocalMaxIdeal m := by
    intro element
    have hcast := congrArg (fun value : MonoidAlgebra ℂ G => value.coeff element) hcomplex
    rw [MonoidAlgebra.coeff_mapRingHom, coefficientAlgebra_coeff] at hcast
    rw [← hcast]
    apply (localResidue_eq_zero_iff m hm ((localElement ^ exponent).coeff element)).mp
    have hresidue := congrArg (fun value : MonoidAlgebra (localResidueField m hm) G =>
      value.coeff element) hexponent
    rw [← map_pow, MonoidAlgebra.coeff_mapRingHom, MonoidAlgebra.coeff_zero] at hresidue
    exact hresidue
  have hscalar := centralChar_maxIdeal_coefficients m hm hcharacter hcoeffMax
    (coefficientPower_central m hm hcoefficients exponent).2
  rw [centralChar_coefficientPower m hm hcharacter hcoefficients] at hscalar
  have hresidue := (localResidue_eq_zero_iff m hm
    (⟨BlocksCentralChar character coefficients ^ exponent,
      (localCoefficientSubring m hm).pow_mem (centralChar_localRing m hm hcharacter hcoefficients) exponent⟩)).mpr
      hscalar
  rw [show (⟨BlocksCentralChar character coefficients ^ exponent, _⟩ : localCoefficientSubring m hm) =
    (⟨BlocksCentralChar character coefficients, centralChar_localRing m hm hcharacter hcoefficients⟩ ^ exponent)
      from rfl, map_pow] at hresidue
  apply (localResidue_eq_zero_iff m hm
    ⟨BlocksCentralChar character coefficients, centralChar_localRing m hm hcharacter hcoefficients⟩).mp
  exact (isNilpotent_iff_eq_zero).mp ⟨exponent, hresidue⟩

end CFSG.BrauerThirdMainTheorem.Helpers
