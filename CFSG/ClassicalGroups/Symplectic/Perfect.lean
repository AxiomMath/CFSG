module

public import Mathlib.GroupTheory.IsPerfect
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
import CFSG.Adapters.SpecialLinearPerfect
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.SumRootGeneration
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

public section

namespace CFSG.ClassicalGroups.Symplectic

open TauCeti.GLSymplecticFin
open scoped commutatorElement

private theorem commutatorElement_mem_commutator {G : Type*} [Group G] (g h : G) :
    ⁅g, h⁆ ∈ commutator G :=
  Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)

private theorem rootHom_mem_commutator_of_character_ne_one {K : Type*} [Field K] {m : ℕ}
    (root : RootSubgroupIndex m) (t : Fin m → Kˣ) (ht : ((root.character t : Kˣ) : K) ≠ 1)
    (c : Multiplicative K) :
    root.hom c ∈ commutator ↥(TauCeti.GLSymplecticFin m K) := by
  have hχ : ((root.character t : Kˣ) : K) - 1 ≠ 0 := sub_ne_zero.mpr ht
  have hword : ⁅diagonal t, root.hom (Multiplicative.ofAdd
      (c.toAdd / (((root.character t : Kˣ) : K) - 1)))⁆ = root.hom c := by
    rw [commutatorElement_def, diagonal_mul_rootSubgroup_mul_inv, ← map_inv (root.hom (R := K)),
      ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    field_simp
    ring
  rw [← hword]
  exact commutatorElement_mem_commutator _ _

theorem commutator_GLSymplecticFin_eq_top_of_exists_sq_ne_one
    (K : Type*) [Field K] (m : ℕ) (hK : ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ := by
  obtain ⟨a, ha0, ha2⟩ := hK
  have ha1 : a ≠ 1 := (sq_ne_one_iff.mp ha2).1
  have haa : a * a ≠ 1 := by rwa [← sq]
  have haa' : a⁻¹ * a⁻¹ ≠ 1 := by rwa [← mul_inv, Ne, inv_eq_one]
  apply eq_top_of_root_subgroups
  intro root c
  cases root with
  | positiveLong i =>
      refine rootHom_mem_commutator_of_character_ne_one _ (Pi.mulSingle i (Units.mk0 a ha0)) ?_ c
      simpa using haa
  | negativeLong i =>
      refine rootHom_mem_commutator_of_character_ne_one _ (Pi.mulSingle i (Units.mk0 a ha0)) ?_ c
      simpa using haa'
  | difference i j hij =>
      refine rootHom_mem_commutator_of_character_ne_one _ (Pi.mulSingle i (Units.mk0 a ha0)) ?_ c
      simpa [Pi.mulSingle_eq_of_ne hij.symm] using ha1
  | positiveSum i j hij =>
      refine rootHom_mem_commutator_of_character_ne_one _ (Pi.mulSingle i (Units.mk0 a ha0)) ?_ c
      simpa [Pi.mulSingle_eq_of_ne hij.ne'] using ha1
  | negativeSum i j hij =>
      refine rootHom_mem_commutator_of_character_ne_one _ (Pi.mulSingle i (Units.mk0 a ha0)) ?_ c
      simpa [Pi.mulSingle_eq_of_ne hij.ne'] using ha1

private theorem longRoot_mem_commutator {K : Type*} [Field K] {m : ℕ}
    (hdiff : ∀ {i j : Fin m} (hij : i ≠ j) (c : K),
      differenceShortRootUnit hij c ∈ commutator ↥(TauCeti.GLSymplecticFin m K))
    {i j : Fin m} (hij : i ≠ j) (c : K) :
    positiveLongRootTransvectionUnit i c ∈ commutator ↥(TauCeti.GLSymplecticFin m K) ∧
      negativeLongRootTransvectionUnit i c ∈ commutator ↥(TauCeti.GLSymplecticFin m K) := by
  constructor
  · have h := commutatorElement_mem_commutator (positiveSumShortRootUnit hij (1 : K))
      (negativeLongRootTransvectionUnit j (-c))
    rw [commutatorElement_positiveSumShortRootUnit_negativeLongRootTransvectionUnit] at h
    simp only [one_mul, one_pow, neg_neg] at h
    exact ((commutator _).mul_mem_cancel_left (hdiff hij _)).mp h
  · have h := commutatorElement_mem_commutator (negativeSumShortRootUnit hij (1 : K))
      (positiveLongRootTransvectionUnit j (-c))
    rw [commutatorElement_negativeSumShortRootUnit_positiveLongRootTransvectionUnit] at h
    simp only [one_mul, one_pow, neg_neg] at h
    exact ((commutator _).mul_mem_cancel_left (hdiff hij.symm _)).mp h

private theorem commutator_eq_top_of_differenceShortRootUnit_mem {K : Type*} [Field K] {m : ℕ}
    (hm : 2 ≤ m)
    (hdiff : ∀ {i j : Fin m} (hij : i ≠ j) (c : K),
      differenceShortRootUnit hij c ∈ commutator ↥(TauCeti.GLSymplecticFin m K)) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  apply eq_top_of_root_subgroups
  apply rootSubgroupHom_mem_of_difference_long _ hdiff
  · intro i c
    obtain ⟨j, hji⟩ := exists_ne i
    exact (longRoot_mem_commutator hdiff hji.symm c).1
  · intro i c
    obtain ⟨j, hji⟩ := exists_ne i
    exact (longRoot_mem_commutator hdiff hji.symm c).2

theorem commutator_GLSymplecticFin_eq_top_of_three_le
    (K : Type*) [Field K] (m : ℕ) (hm : 3 ≤ m) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ := by
  apply commutator_eq_top_of_differenceShortRootUnit_mem (by omega)
  intro i k hik c
  obtain ⟨j, hji, hjk⟩ := Fin.exists_ne_and_ne_of_two_lt i k (by omega)
  have h := commutatorElement_mem_commutator (differenceShortRootUnit hji.symm c)
    (differenceShortRootUnit hjk (1 : K))
  rwa [commutatorElement_differenceShortRootUnit_differenceShortRootUnit hji.symm hjk hik,
    mul_one] at h

theorem commutator_GLSymplecticFin_eq_top_of_exists_ne_zero_ne_one
    (K : Type*) [Field K] (m : ℕ) (hK : ∃ a : K, a ≠ 0 ∧ a ≠ 1) (hm : 2 ≤ m) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ := by
  obtain ⟨a, ha0, ha1⟩ := hK
  apply commutator_eq_top_of_differenceShortRootUnit_mem hm
  intro i j hij c
  have h := rootHom_mem_commutator_of_character_ne_one (.difference i j hij)
    (Pi.mulSingle i (Units.mk0 a ha0)) (by simpa [Pi.mulSingle_eq_of_ne hij.symm] using ha1)
    (Multiplicative.ofAdd c)
  simpa only [RootSubgroupIndex.hom_difference, differenceShortRootHom_apply,
    toAdd_ofAdd] using h

theorem commutator_GLSymplecticFin_eq_top_of_card_eq_three
    (K : Type*) [Field K] [Finite K] (hK : Nat.card K = 3) (m : ℕ) (hm : 2 ≤ m) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ := by
  have h3 : (3 : K) = 0 := by
    let _ := Fintype.ofFinite K
    have h := Nat.cast_card_eq_zero K
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact_mod_cast h
  refine commutator_GLSymplecticFin_eq_top_of_exists_ne_zero_ne_one K m
    ⟨-1, neg_ne_zero.mpr one_ne_zero, fun h => ?_⟩ hm
  exact one_ne_zero (by linear_combination h3 + h : (1 : K) = 0)

theorem commutator_GLSymplecticFin_eq_top_of_card_eq_two
    (K : Type*) [Field K] [Finite K] (_hK : Nat.card K = 2) (m : ℕ) (hm : 3 ≤ m) :
    commutator ↥(TauCeti.GLSymplecticFin m K) = ⊤ :=
  commutator_GLSymplecticFin_eq_top_of_three_le K m hm

private theorem exists_ne_zero_sq_ne_one_of_infinite (K : Type*) [Field K] [Infinite K] :
    ∃ a : K, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact ⟨a, ha.1, sq_ne_one_iff.mpr ha.2⟩

theorem isPerfect_GLSymplecticFin (K : Type*) [Field K] (m : ℕ)
    (h : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ m) ∨
      (Nat.card K = 2 ∧ 3 ≤ m)) :
    Group.IsPerfect ↥(TauCeti.GLSymplecticFin m K) := by
  refine ⟨?_⟩
  rcases h with (hinf | h4) | ⟨h3, hm⟩ | ⟨h2, hm⟩
  · exact commutator_GLSymplecticFin_eq_top_of_exists_sq_ne_one K m
      (exists_ne_zero_sq_ne_one_of_infinite K)
  · have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    exact commutator_GLSymplecticFin_eq_top_of_exists_sq_ne_one K m
      (CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K h4)
  · have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    exact commutator_GLSymplecticFin_eq_top_of_card_eq_three K h3 m hm
  · have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    exact commutator_GLSymplecticFin_eq_top_of_card_eq_two K h2 m hm

end CFSG.ClassicalGroups.Symplectic
