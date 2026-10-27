module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import CFSG.CharacterTheory.FrobeniusDeterminant.AW
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed

public section

namespace CFSG

open CFSG.FrobeniusDeterminant
open MvPolynomial Matrix

namespace FrobeniusDeterminant

theorem frobenius_group_determinant (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    ∃ (r : ℕ) (p : Fin r → MvPolynomial G ℂ),
      r = Nat.card (ConjClasses G) ∧
      (∀ j, Irreducible (p j)) ∧
      (∀ i j, i ≠ j → ¬ Associated (p i) (p j)) ∧
      groupDeterminant G = ∏ j, (p j) ^ (p j).totalDegree := by
  classical
  obtain ⟨r, d, hd, hφ⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
      ℂ (MonoidAlgebra ℂ G)
  let : ∀ i, NeZero (d i) := hd
  let φ := Classical.choice hφ
  have hr : r = Nat.card (ConjClasses G) := FrobeniusDeterminant.AW.wedderburn_count φ
  have hrpos : 0 < r := by
    rw [hr]
    exact Nat.card_pos
  let : NeZero r := ⟨Nat.ne_of_gt hrpos⟩
  have hd0 : 0 < d (0 : Fin r) := NeZero.pos _
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq
    (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) hd0
  have hsign : (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) ≠ 0 := by
    exact Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hcne : c ≠ 0 := by
    intro h
    subst c
    rw [zero_pow (Nat.ne_of_gt hd0)] at hc
    exact hsign hc.symm
  let u : Fin r → ℂ := fun i => if i = 0 then c else 1
  have hune : ∀ i, u i ≠ 0 := by
    intro i
    by_cases hi : i = 0
    · simp [u, hi, hcne]
    · simp [u, hi]
  have huUnit : ∀ i, IsUnit (MvPolynomial.C (u i) : MvPolynomial G ℂ) := by
    intro i
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
    exact ⟨u i, isUnit_iff_ne_zero.mpr (hune i), rfl⟩
  let p : Fin r → MvPolynomial G ℂ := fun i =>
    MvPolynomial.C (u i) * FrobeniusDeterminant.AW.factor φ i
  have hpirreducible : ∀ i, Irreducible (p i) := by
    intro i
    dsimp [p]
    exact (irreducible_isUnit_mul (huUnit i)).2
      (FrobeniusDeterminant.AW.factor_irreducible φ i)
  have hpdeg : ∀ i, (p i).totalDegree = d i := by
    intro i
    dsimp [p]
    rw [MvPolynomial.totalDegree_mul_of_isDomain
      (MvPolynomial.C_ne_zero.mpr (hune i))
      (FrobeniusDeterminant.AW.factor_irreducible φ i).ne_zero]
    simp [FrobeniusDeterminant.AW.factor_totalDegree]
  have hpAssoc : ∀ i, Associated (p i) (FrobeniusDeterminant.AW.factor φ i) := by
    intro i
    dsimp [p]
    simpa [mul_comm] using associated_mul_unit_left
      (FrobeniusDeterminant.AW.factor φ i) (MvPolynomial.C (u i)) (huUnit i)
  have hpnonassoc : ∀ i j, i ≠ j → ¬Associated (p i) (p j) := by
    intro i j hij h
    apply FrobeniusDeterminant.AW.factor_not_associated φ hij
    exact (hpAssoc i).symm.trans (h.trans (hpAssoc j))
  have huprod : ∏ i, u i ^ d i =
      (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) := by
    simp [u, hc]
  have hpprod : ∏ i, p i ^ (p i).totalDegree =
      MvPolynomial.C (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) *
        ∏ i, FrobeniusDeterminant.AW.factor φ i ^ d i := by
    calc
      ∏ i, p i ^ (p i).totalDegree =
          (∏ i, MvPolynomial.C (u i) ^ d i) *
            ∏ i, FrobeniusDeterminant.AW.factor φ i ^ d i := by
        simp_rw [hpdeg, p, mul_pow]
        exact Finset.prod_mul_distrib
      _ = MvPolynomial.C
            (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) *
            ∏ i, FrobeniusDeterminant.AW.factor φ i ^ d i := by
        congr 1
        simp_rw [← map_pow]
        rw [← map_prod]
        rw [huprod]
  refine ⟨r, p, hr, hpirreducible, hpnonassoc, ?_⟩
  calc
    groupDeterminant G =
        MvPolynomial.C (Equiv.Perm.sign (FrobeniusDeterminant.Core.invPerm G) : ℂ) *
          ∏ i, FrobeniusDeterminant.AW.factor φ i ^ d i :=
      FrobeniusDeterminant.AW.groupDeterminant_factorization φ
    _ = ∏ i, p i ^ (p i).totalDegree := hpprod.symm

end FrobeniusDeterminant

end CFSG
