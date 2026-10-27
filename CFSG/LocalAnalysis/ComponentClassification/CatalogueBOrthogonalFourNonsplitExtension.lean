module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

abbrev extension (delta : K) := QuadraticAlgebra K delta 0

@[instance_reducible] def extensionField (delta : K) (hns : ¬ IsSquare delta) :
    Field (extension delta) := by
  letI : Fact (¬ IsSquare delta) := ⟨hns⟩
  infer_instance

theorem generator_square (delta : K) :
    (QuadraticAlgebra.omega : extension delta) ^ 2 =
      algebraMap K (extension delta) delta := by
  rw [QuadraticAlgebra.omega_pow_two_eq_add]
  simp [Algebra.algebraMap_eq_smul_one]

@[expose] def conjugation (delta : K) : extension delta ≃ₐ[K] extension delta where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' x y := by rw [star_mul, mul_comm]
  map_add' := star_add
  commutes' x := by
    apply QuadraticAlgebra.ext <;> simp

theorem conjugation_mk (delta s r : K) :
    conjugation delta (⟨s, r⟩ : extension delta) = ⟨s, -r⟩ := by
  apply QuadraticAlgebra.ext <;> simp [conjugation]

theorem conjugation_square (delta : K) : (conjugation delta).toRingEquiv ^ 2 = 1 := by
  apply RingEquiv.ext
  intro z
  exact star_star z

theorem conjugation_ne_one (delta : K) (h2 : (2 : K) ≠ 0) :
    (conjugation delta).toRingEquiv ≠ 1 := by
  intro h
  have ht := congrArg QuadraticAlgebra.im
    (DFunLike.congr_fun h (QuadraticAlgebra.omega : extension delta))
  have hneg : -(1 : K) = 1 := by simpa [conjugation] using ht
  apply h2
  linear_combination -hneg

theorem conjugation_fixed_iff (delta : K) (h2 : (2 : K) ≠ 0) (z : extension delta) :
    conjugation delta z = z ↔ z = algebraMap K (extension delta) z.re := by
  constructor
  · intro h
    have him := congrArg QuadraticAlgebra.im h
    have hz : z.im = 0 := by
      have heq : -z.im = z.im := by simpa [conjugation] using him
      have hmul : (2 : K) * z.im = 0 := by linear_combination -heq
      exact (mul_eq_zero.mp hmul).resolve_left h2
    apply QuadraticAlgebra.ext <;> simp [hz]
  · intro h
    rw [h]
    exact (conjugation delta).commutes z.re

theorem conjugation_fixed_range (delta : K) (h2 : (2 : K) ≠ 0) (z : extension delta) :
    conjugation delta z = z ↔ z ∈ Set.range (algebraMap K (extension delta)) := by
  constructor
  · intro hz
    exact ⟨z.re, ((conjugation_fixed_iff delta h2 z).mp hz).symm⟩
  · rintro ⟨s, rfl⟩
    exact (conjugation delta).commutes s

theorem extension_finrank (delta : K) : Module.finrank K (extension delta) = 2 :=
  QuadraticAlgebra.finrank_eq_two delta 0

theorem extension_card (delta : K) : Nat.card (extension delta) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd delta 0), Nat.card_prod, pow_two]

theorem extension_norm (delta : K) (z : extension delta) :
    QuadraticAlgebra.norm z = z.re ^ 2 - delta * z.im ^ 2 := by
  simp [QuadraticAlgebra.norm_def, pow_two, mul_assoc]

theorem extension_norm_product (delta : K) (z : extension delta) :
    z * conjugation delta z =
      algebraMap K (extension delta) (QuadraticAlgebra.norm z) :=
  (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm

theorem extension_norm_surjective [Finite K] (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (a : Kˣ) :
    ∃ c : (extension delta)ˣ, QuadraticAlgebra.norm (c : extension delta) = (a : K) := by
  let : Finite (extension delta) :=
    Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm
  let aE : (extension delta)ˣ := Units.map (algebraMap K (extension delta)) a
  obtain ⟨c, hc⟩ := CatalogueBLinearTwoDescent.exists_norm_unit (extension delta)
    (conjugation delta).toRingEquiv (conjugation_square delta)
    (conjugation_ne_one delta h2) aE ((conjugation delta).commutes (a : K))
  refine ⟨c, ?_⟩
  apply QuadraticAlgebra.algebraMap_injective (a := delta) (b := 0)
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  exact hc

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
