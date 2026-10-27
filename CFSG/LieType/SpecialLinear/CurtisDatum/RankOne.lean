module

public import CFSG.LieType.Universal.SpecialLinearExtras
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.Bruhat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SL CFSG.LieType.RootSystem
  CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
open scoped MatrixGroups

open _root_.Classical

variable (m : ℕ) (F : Type) [Field F]

abbrev SLG := SpecialLinearGroup (Fin (m + 1)) F

@[expose] noncomputable def hdiag (k : Fin m) (u : Fˣ) : SLG m F :=
  SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) u

private theorem isDiag_of_mem_torus {k : Fin m} {h : SLG m F} (hh : h ∈ torus m F k) :
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag := by
  have hle : torus m F k ≤ SpecialLinearGroup.diagonalTorus F (m + 1) := by
    rw [torus, Subgroup.closure_le]
    rintro h ⟨t, ht⟩
    exact SpecialLinearGroup.mem_diagonalTorus_iff.mpr (by rw [ht]; exact isDiag_diagonal _)
  exact SpecialLinearGroup.mem_diagonalTorus_iff.mp (hle hh)

theorem hdiag_mem_torus (k : Fin m) (u : Fˣ) : hdiag m F k u ∈ torus m F k := by
  refine Subgroup.subset_closure ⟨u, ?_⟩
  change (SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) u).1 = _
  rw [SpecialLinearGroup.diag2nUnit_coe]
  congr 1
  funext r
  simp only [Function.update_apply, Pi.one_apply]
  have hne := (Fin.castSucc_lt_succ (i := k)).ne
  split_ifs <;> simp_all

theorem hdiag_mem_H (k : Fin m) (u : Fˣ) : hdiag m F k u ∈ ⨆ k, torus m F k :=
  Subgroup.mem_iSup_of_mem k (hdiag_mem_torus m F k u)

theorem hdiag_mul (k : Fin m) (u v : Fˣ) :
    hdiag m F k (u * v) = hdiag m F k u * hdiag m F k v := by
  apply Subtype.ext
  change (SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) (u * v)).1 =
    (SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) u).1 *
      (SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) v).1
  rw [SpecialLinearGroup.diag2nUnit_coe, SpecialLinearGroup.diag2nUnit_coe,
    SpecialLinearGroup.diag2nUnit_coe, diagonal_mul_diagonal]
  congr 1
  funext r
  split_ifs <;> simp [mul_comm]

theorem hdiag_one (k : Fin m) : hdiag m F k 1 = 1 := by
  show SpecialLinearGroup.diag2nUnit ((Fin.castSucc_lt_succ (i := k)).ne) (1 : Fˣ) = 1
  exact SpecialLinearGroup.diag2nUnit_one (R := F) (i := k.castSucc) (j := k.succ)
    (hij := (Fin.castSucc_lt_succ (i := k)).ne)

@[expose] noncomputable def phiVal (k : Fin m) (x : SLG m F) : SLG m F :=
  if h : (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k.castSucc k.succ ≠ 0 then
    hdiag m F k (Units.mk0 (-(x : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k.castSucc k.succ)
      (neg_ne_zero.mpr h))
  else 1

theorem phiVal_mem (k : Fin m) {x : SLG m F} (_hx : x ∈ rootGroup m F (Pi.single k 1))
    (_hx1 : x ≠ 1) : phiVal m F k x ∈ ⨆ k, torus m F k := by
  unfold phiVal
  split_ifs with h
  · exact Subgroup.mem_iSup_of_mem k (hdiag_mem_torus m F k _)
  · exact Subgroup.mem_iSup_of_mem k (one_mem _)

theorem phiVal_eq (k : Fin m) {c : F} (hc : c ≠ 0) :
    phiVal m F k (SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c) =
      hdiag m F k (Units.mk0 (-c) (neg_ne_zero.mpr hc)) := by
  unfold phiVal
  have hval : ((SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c :
      SLG m F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k.castSucc k.succ = c := by
    rw [SpecialLinearGroup.transvection_coe]
    simp [(Fin.castSucc_lt_succ (i := k)).ne]
  rw [dif_pos (by rw [hval]; exact hc)]
  congr 1
  apply Units.ext
  simpa using congrArg Neg.neg hval

private noncomputable def h2 (u : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  SpecialLinearGroup.diag2nUnit (zero_ne_one : (0 : Fin 2) ≠ 1) u

private theorem h2_eq_diag2 (a : F) (ha : a ≠ 0) :
    h2 F (Units.mk0 a ha) = SpecialLinearGroup.diag2 a ha := by
  rw [h2, SpecialLinearGroup.diag2nUnit_mk0, ← SpecialLinearGroup.diag2_def]

private theorem blockHom_transvection_zero_one (k : Fin m) (c : F) :
    blockHom F k (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) =
      SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c := by
  apply Subtype.ext
  have hx : (↑(SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) :
      Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := by
    rw [SpecialLinearGroup.transvection_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp []
  change blockMat k (↑(SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c) :
    Matrix (Fin 2) (Fin 2) F) = ↑(SpecialLinearGroup.transvection
      ((Fin.castSucc_lt_succ (i := k)).ne) c)
  rw [hx, blockMat_transvection_upper, SpecialLinearGroup.transvection_coe]
  simp [Matrix.transvection]

private theorem blockHom_transvection_one_zero (k : Fin m) (c : F) :
    blockHom F k (SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) =
      SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne).symm c := by
  apply Subtype.ext
  have hx : (↑(SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) :
      Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := by
    rw [SpecialLinearGroup.transvection_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp []
  change blockMat k (↑(SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c) :
    Matrix (Fin 2) (Fin 2) F) = ↑(SpecialLinearGroup.transvection
      ((Fin.castSucc_lt_succ (i := k)).ne).symm c)
  rw [hx, blockMat_transvection_lower, SpecialLinearGroup.transvection_coe]
  simp [Matrix.transvection]

private theorem blockHom_h2 (k : Fin m) (u : Fˣ) :
    blockHom F k (h2 F u) = hdiag m F k u := by
  have hpq : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  rw [h2, SpecialLinearGroup.diag2nUnit_decompose (zero_ne_one : (0 : Fin 2) ≠ 1) u]
  rw [show hdiag m F k u = SpecialLinearGroup.diag2nUnit hpq u from rfl,
    SpecialLinearGroup.diag2nUnit_decompose hpq u]
  simp only [map_mul, blockHom_transvection_zero_one, blockHom_transvection_one_zero]

private theorem sl2_upper_identity (c : F) (hc : c ≠ 0) :
    SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c *
        (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1 *
          SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1) *
          SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1) =
      SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) c⁻¹ *
        h2 F (Units.mk0 (-c) (neg_ne_zero.mpr hc)) *
        SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-c⁻¹) := by
  rw [h2_eq_diag2 F (-c) (neg_ne_zero.mpr hc)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  all_goals field_simp
  all_goals ring

private theorem sl2_conj_identity (c : F) (hc : c ≠ 0) :
    (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1 *
          SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1) *
          SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1) *
        SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) c *
        (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1 *
          SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1) *
          SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1) =
      SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-c⁻¹) *
        (SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1 *
          SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) (-1) *
          SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) 1) *
        h2 F (Units.mk0 (-c) (neg_ne_zero.mpr hc)) *
        SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-c⁻¹) := by
  rw [h2_eq_diag2 F (-c) (neg_ne_zero.mpr hc)]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection_coe, SpecialLinearGroup.diag2_coe',
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  all_goals field_simp
  all_goals ring

theorem rankOne_upper (k : Fin m) (c : F) (hc : c ≠ 0) :
    SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c * weylRep m F k =
      SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne).symm c⁻¹ *
        hdiag m F k (Units.mk0 (-c) (neg_ne_zero.mpr hc)) *
        SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (-c⁻¹) := by
  have h := congrArg (blockHom F k) (sl2_upper_identity (F := F) c hc)
  simpa [map_mul, blockHom_transvection_zero_one, blockHom_transvection_one_zero,
    blockHom_h2, weylRep, hdiag] using h

theorem rankOne_conj (k : Fin m) (c : F) (hc : c ≠ 0) :
    weylRep m F k * SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c *
        weylRep m F k =
      SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (-c⁻¹) *
        weylRep m F k * hdiag m F k (Units.mk0 (-c) (neg_ne_zero.mpr hc)) *
        SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (-c⁻¹) := by
  have h := congrArg (blockHom F k) (sl2_conj_identity (F := F) c hc)
  simpa [map_mul, blockHom_transvection_zero_one, blockHom_transvection_one_zero,
    blockHom_h2, weylRep, hdiag] using h

theorem phiVal_spec (k : Fin m) {x : SLG m F} (hx : x ∈ rootGroup m F (Pi.single k 1))
    (hx1 : x ≠ 1) :
    ∃ l ∈ negUnipotent (rootDatum m F), ∃ u ∈ posUnipotent (rootDatum m F),
      x * weylRep m F k = l * phiVal m F k x * u := by
  have hpq : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  have hst : toStd m (-Pi.single k 1) = Pi.single k.succ 1 - Pi.single k.castSucc 1 := by
    rw [toStd_neg, toStd_single, neg_sub]
  rw [rootGroup_eq m F hpq (toStd_single m k), mem_rootSubgroup] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : c ≠ 0 := by
    intro h0
    apply hx1
    rw [h0]
    show SpecialLinearGroup.transvection hpq (0 : F) = 1
    exact SpecialLinearGroup.transvection_coeff_zero hpq
  rw [phiVal_eq m F k hc]
  refine ⟨SpecialLinearGroup.transvection hpq.symm c⁻¹, ?_,
    SpecialLinearGroup.transvection hpq (-c⁻¹), ?_, rankOne_upper m F k c hc⟩
  · have hγ : -Pi.single k 1 ∈ (rootDatum m F).roots := by
      change -Pi.single k 1 ∈ roots (isFiniteType_A m) ∅
      rw [roots_eq]
      exact ⟨k.succ, k.castSucc, hpq.symm, by rw [toStd_neg, toStd_single, neg_sub]⟩
    have hneg : ht (-Pi.single k 1) < 0 := by
      rw [ht_neg, ht_single]
      norm_num
    exact rootGroup_le_negUnipotent (D := rootDatum m F) hγ hneg
      ((rootGroup_eq m F hpq.symm hst).symm.le (transvection_mem_rootSubgroup hpq.symm c⁻¹))
  · have hγ : Pi.single k 1 ∈ (rootDatum m F).roots := by
      change Pi.single k 1 ∈ roots (isFiniteType_A m) ∅
      rw [roots_eq]
      exact ⟨k.castSucc, k.succ, hpq, toStd_single m k⟩
    exact rootGroup_le_posUnipotent (D := rootDatum m F) hγ (ht_single_pos (D := rootDatum m F) k)
      ((rootGroup_eq m F hpq (toStd_single m k)).symm.le (transvection_mem_rootSubgroup hpq (-c⁻¹)))

theorem psiVal_spec (k : Fin m) {x : SLG m F} (hx : x ∈ rootGroup m F (Pi.single k 1))
    (hx1 : x ≠ 1) :
    ∃ a ∈ rootGroup m F (Pi.single k 1), ∃ u ∈ posUnipotent (rootDatum m F),
      weylRep m F k * x * weylRep m F k = a * weylRep m F k * phiVal m F k x * u := by
  have hpq : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  rw [rootGroup_eq m F hpq (toStd_single m k), mem_rootSubgroup] at hx
  obtain ⟨c, rfl⟩ := hx
  have hc : c ≠ 0 := by
    intro h0
    apply hx1
    rw [h0]
    show SpecialLinearGroup.transvection hpq (0 : F) = 1
    exact SpecialLinearGroup.transvection_coeff_zero hpq
  rw [phiVal_eq m F k hc]
  refine ⟨SpecialLinearGroup.transvection hpq (-c⁻¹), ?_,
    SpecialLinearGroup.transvection hpq (-c⁻¹), ?_, rankOne_conj m F k c hc⟩
  · exact (rootGroup_eq m F hpq (toStd_single m k)).symm.le
      (transvection_mem_rootSubgroup hpq (-c⁻¹))
  · have hγ : Pi.single k 1 ∈ (rootDatum m F).roots := by
      change Pi.single k 1 ∈ roots (isFiniteType_A m) ∅
      rw [roots_eq]
      exact ⟨k.castSucc, k.succ, hpq, toStd_single m k⟩
    exact rootGroup_le_posUnipotent (D := rootDatum m F) hγ (ht_single_pos (D := rootDatum m F) k)
      ((rootGroup_eq m F hpq (toStd_single m k)).symm.le (transvection_mem_rootSubgroup hpq (-c⁻¹)))

theorem bruhatY_spec (k : Fin m) {y : SLG m F} (hy : y ∈ rootGroup m F (-Pi.single k 1))
    (hy1 : y ≠ 1) :
    ∃ h ∈ ⨆ k, torus m F k, ∃ a ∈ rootGroup m F (Pi.single k 1),
      ∃ c ∈ rootGroup m F (Pi.single k 1), y = a * (h * weylRep m F k) * c := by
  have hpq : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  have hst : toStd m (-Pi.single k 1) = Pi.single k.succ 1 - Pi.single k.castSucc 1 := by
    rw [toStd_neg, toStd_single, neg_sub]
  have hyR : y ∈ CurtisTits.rankOne (rootGroup m F) k := by
    rw [rankOne_rootGroup m F k]
    exact Subgroup.mem_sup_right ((rootGroup_eq m F hpq.symm hst).le hy)
  have hmem := (rootGroup_eq m F hpq.symm hst).le hy
  rw [mem_rootSubgroup] at hmem
  obtain ⟨c, hc_eq⟩ := hmem
  have hc : c ≠ 0 := by
    intro h0
    apply hy1
    rw [← hc_eq, h0]
    show SpecialLinearGroup.transvection hpq.symm (0 : F) = 1
    exact SpecialLinearGroup.transvection_coeff_zero hpq.symm
  rcases (steinbergExtras m F).rankOne_bruhat k y hyR with
    ⟨h, hh, u, hu, he⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · exfalso
    have hhdiag : (h : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag :=
      isDiag_of_mem_torus m F hh
    have hu_mem := (rootGroup_eq m F hpq (toStd_single m k)).le hu
    rw [mem_rootSubgroup] at hu_mem
    obtain ⟨d, hd_eq⟩ := hu_mem
    have hu0 : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k.succ k.castSucc = 0 := by
      rw [← hd_eq, SpecialLinearGroup.transvection_coe]
      simp [hpq, hpq.symm]
    have hprod0 : ((h * u : SLG m F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
        k.succ k.castSucc = 0 := by
      change ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) F) *
        (u : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) k.succ k.castSucc = 0
      rw [← hhdiag.diagonal_diag, Matrix.diagonal_mul, hu0, mul_zero]
    have hy0 : (y : Matrix (Fin (m + 1)) (Fin (m + 1)) F) k.succ k.castSucc = c := by
      rw [← hc_eq, SpecialLinearGroup.transvection_coe]
      simp [hpq.symm]
    rw [he] at hy0
    rw [hprod0] at hy0
    exact hc hy0.symm
  · let h' : SLG m F := weylRep m F k * h * (weylRep m F k)⁻¹
    have hh' : h' ∈ torus m F k := by
      have hh0 := (isCTGroupDatum m F).conj_H_mem k k h hh
      rw [sup_idem] at hh0
      simpa [h'] using hh0
    refine ⟨h', Subgroup.mem_iSup_of_mem k hh', u, hu, v, hv, ?_⟩
    rw [he]
    change u * weylRep m F k * h * v = u * (h' * weylRep m F k) * v
    have hW : h' * weylRep m F k = weylRep m F k * h := by
      change weylRep m F k * h * (weylRep m F k)⁻¹ * weylRep m F k = weylRep m F k * h
      group
    rw [hW]
    group

end CFSG.LieType.SpecialLinear
