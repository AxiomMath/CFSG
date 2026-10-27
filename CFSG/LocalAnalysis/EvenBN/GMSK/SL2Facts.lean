module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.FieldTheory.Finite.Basic
import CFSG.Walter.PSL2Facts.Even
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

section SL2

variable {K : Type*} [Field K]

theorem two_eq_zero_of_card [Fintype K] {n : ℕ} (hn : n ≠ 0) (hK : Fintype.card K = 2 ^ n) :
    (2 : K) = 0 := by
  have h := FiniteField.cast_card_eq_zero K
  rw [hK, Nat.cast_pow, Nat.cast_ofNat] at h
  exact (pow_eq_zero_iff hn).1 h

variable (K) in
@[expose] def sl2Upper : Multiplicative K →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun x := ⟨!![1, x.toAdd; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := by
    apply Subtype.ext
    change !![1, (x * y).toAdd; 0, 1] = !![1, x.toAdd; 0, 1] * !![(1 : K), y.toAdd; 0, 1]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]

theorem sl2Upper_coe (x : Multiplicative K) :
    (sl2Upper K x : Matrix (Fin 2) (Fin 2) K) = !![1, x.toAdd; 0, 1] := rfl

theorem sl2Upper_injective : Function.Injective (sl2Upper K) := by
  intro x y h
  have h01 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h
  simp only [sl2Upper_coe] at h01
  simpa using h01

theorem sl2_exists_mul_ne : ∃ x y : Matrix.SpecialLinearGroup (Fin 2) K, x * y ≠ y * x := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩,
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩, fun h => ?_⟩
  have h00 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change (!![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1]) 0 0 =
    (!![(1 : K), 0; 1, 1] * !![(1 : K), 1; 0, 1]) 0 0 at h00
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h00
  simp at h00

theorem sl2_isSimpleGroup [Fintype K] (h2 : (2 : K) = 0) (h4 : 4 ≤ Fintype.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rwa [Nat.card_eq_fintype_card])
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)).symm.isSimpleGroup

theorem exists_elementaryAbelian_four [Fintype K] (h2 : (2 : K) = 0)
    (h4 : 4 ∣ Fintype.card K) :
    ∃ E : Subgroup (Multiplicative K), CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := Multiplicative K) 2 (n := 2)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]; simpa using h4)
  refine ⟨E, ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_⟩, by
    rw [hE]; norm_num⟩
  change (x : Multiplicative K) ^ 2 = 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul, ← two_mul, h2, zero_mul]

end SL2

end CFSG.LocalAnalysis.EvenBN.GMSK
