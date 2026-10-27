module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23Levi
public import Certificates.Certificate3183
import all CFSG.Fischer.F4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open Subgroup CFSG.Fischer CFSG.LinearGroups CFSG.LieType.Universal.Unitary Matrix
open CFSG.Monster.B.Classical.UnitarySix


theorem Ymat_det : Ymat.det = 1 :=
  Certificates.certificate3183.1

theorem Ymat_iso : (Ymat.map bar)ᵀ * antidiag 6 * Ymat = antidiag 6 :=
  Certificates.certificate3183.2.1

theorem Ymat_comm : Ymat * (1 + Matrix.single 2 3 1) = (1 + Matrix.single 2 3 1) * Ymat :=
  Certificates.certificate3183.2.2.1

theorem Ymat_trace : (Ymat * Ymat * Ymat).trace ≠ bar (Ymat * Ymat * Ymat).trace :=
  Certificates.certificate3183.2.2.2

@[expose] noncomputable def YSU : SU frobeniusF4 6 :=
  mkSU Ymat Ymat_det ((isIsometry_iff_map_bar _).2 Ymat_iso)

theorem YSU_comm : YSU * rep₁ = rep₁ * YSU :=
  SU_ext (by rw [coe_SU_mul, coe_SU_mul, YSU, coe_mkSU, coe_rep₁]; exact Ymat_comm)

theorem pow_three_F4 : ∀ b : F4, b ≠ 0 → b ^ 3 = 1 := by decide

theorem trace_betaM (M : Matrix (Fin 6) (Fin 6) F4) : (betaM M).trace = bar M.trace := by
  rw [Matrix.trace, Matrix.trace, bar_sum]
  rfl

theorem trace_eq_bar_of_conj {Y A Ai : Matrix (Fin 6) (Fin 6) F4} {a : F4} (ha : a ^ 3 = 1)
    (hAi : Ai * A = 1) (h : Y = a • (A * betaM Y * Ai)) :
    (Y * Y * Y).trace = bar (Y * Y * Y).trace := by
  have hZ : (A * betaM Y * Ai) * (A * betaM Y * Ai) * (A * betaM Y * Ai) =
      A * betaM (Y * Y * Y) * Ai := by
    rw [betaM_mul, betaM_mul]
    calc (A * betaM Y * Ai) * (A * betaM Y * Ai) * (A * betaM Y * Ai) =
        A * betaM Y * (Ai * A) * betaM Y * (Ai * A) * betaM Y * Ai := by
          simp only [Matrix.mul_assoc]
      _ = A * (betaM Y * betaM Y * betaM Y) * Ai := by
          simp only [hAi, Matrix.mul_one, Matrix.mul_assoc]
  have h3 : Y * Y * Y = a ^ 3 • (A * betaM (Y * Y * Y) * Ai) := by
    conv_lhs => rw [h]
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hZ, pow_three, mul_assoc]
  calc (Y * Y * Y).trace = (A * betaM (Y * Y * Y) * Ai).trace := by
        conv_lhs => rw [h3, ha, one_smul]
    _ = (betaM (Y * Y * Y)).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hAi, Matrix.one_mul]
    _ = bar (Y * Y * Y).trace := trace_betaM _

theorem not_conj_Y (A : SU frobeniusF4 6) :
    (A : ProjSU) * betaL (YSU : ProjSU) ≠ (YSU : ProjSU) * (A : ProjSU) := by
  intro h
  rw [betaL_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    mem_scalars] at h
  obtain ⟨a, ha⟩ := h
  have e : YSU = A * betaSU YSU * ((A * betaSU YSU)⁻¹ * (YSU * A)) * A⁻¹ := by group
  have hm := congrArg
    (fun x : SU frobeniusF4 6 => ((x : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) e
  simp only [coe_SU_mul, coe_betaSU, ha] at hm
  have hY : ((YSU : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = Ymat := coe_mkSU _ _ _
  rw [hY] at hm
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hd := det_of_mem ((A * betaSU YSU)⁻¹ * (YSU * A))
    rw [ha, Matrix.scalar_apply, Matrix.det_diagonal] at hd
    simp at hd
  apply Ymat_trace
  refine trace_eq_bar_of_conj (pow_three_F4 a ha0) (coe_SU_inv_mul A) ?_
  conv_lhs => rw [hm]
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul]

open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.LieType.Chevalley.C2E6Std CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap (K)

@[expose] noncomputable def leviY : stdGroup := leviG (leviOf YSU)

theorem leviOf_YSU_comm : leviOf YSU * leviOf rep₁ = leviOf rep₁ * leviOf YSU := by
  apply leviPSU.injective
  rw [map_mul, map_mul, leviPSU_leviOf, leviPSU_leviOf, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, YSU_comm]

theorem leviY_comm : leviY * repPoint 2 = repPoint 2 * leviY := by
  rw [leviY, ← leviG_leviOf_rep₁]
  have h := congrArg leviG leviOf_YSU_comm
  rwa [map_mul, map_mul] at h

theorem not_commute_leviY {x : GStar} (hx : x ∈ parStar firstJ) (hr : x.right ≠ 1) :
    ¬ Commute x (SemidirectProduct.inl leviY) := by
  intro hc
  have hb : ((x.right : betaGroup) : MulAut stdGroup) = betaG := by
    rcases mem_betaGroup_iff.mp x.right.2 with h | h
    · exact absurd (Subtype.ext h) hr
    · exact h
  have e1 : x.left * betaG leviY = leviY * x.left := by
    have := congrArg SemidirectProduct.left hc.eq
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply] at this
    have h0 : (betaGroup.subtype x.right : MulAut stdGroup) = betaG := hb
    rwa [h0] at this
  have e2 : (x.left : ModGL Tag.E6 K) * betaGL (leviOf YSU) =
      (leviOf YSU : ModGL Tag.E6 K) * x.left := by
    have := congrArg (fun g : stdGroup => (g : ModGL Tag.E6 K)) e1
    simp only [Subgroup.coe_mul, coe_betaG_apply] at this
    exact this
  have hYP : ((leviOf YSU : stdLevi firstJ) : ModGL Tag.E6 K) ∈ nativeParabolic firstJ :=
    stdLevi_le_nativeParabolic two_mem_firstJ (leviOf YSU).2
  have hbYP : betaGL (leviOf YSU : ModGL Tag.E6 K) ∈ nativeParabolic firstJ :=
    stdLevi_le_nativeParabolic two_mem_firstJ (betaLevi (leviOf YSU)).2
  have hxP : (x.left : ModGL Tag.E6 K) ∈ nativeParabolic firstJ := mem_parStar.mp hx
  have e3 : (⟨x.left, hxP⟩ : nativeParabolic firstJ) * ⟨_, hbYP⟩ = ⟨_, hYP⟩ * ⟨x.left, hxP⟩ :=
    Subtype.ext e2
  have e4 := congrArg (leviProj two_mem_firstJ) e3
  have h1 : leviProj two_mem_firstJ ⟨_, hbYP⟩ = betaLevi (leviOf YSU) :=
    leviProj_of_mem two_mem_firstJ (betaLevi (leviOf YSU)).2 hbYP
  have h2 : leviProj two_mem_firstJ ⟨_, hYP⟩ = leviOf YSU :=
    leviProj_of_mem two_mem_firstJ (leviOf YSU).2 hYP
  rw [map_mul, map_mul, h1, h2] at e4
  have e5 := congrArg leviPSU e4
  rw [map_mul, map_mul, leviPSU_betaLevi, leviPSU_leviOf] at e5
  obtain ⟨A, hA⟩ := QuotientGroup.mk_surjective
    (leviPSU (leviProj two_mem_firstJ ⟨x.left, hxP⟩))
  rw [← hA] at e5
  exact not_conj_Y A e5

theorem exists_inner_not_commute_outer {r : stdGroup} (hr : r ∈ levPoints (repLevel 2)) :
    ∃ y : stdGroup, Commute y rootInv ∧ Commute y r ∧
      ∀ x ∈ parStar firstJ, x.right ≠ 1 → ¬ Commute x (SemidirectProduct.inl y) := by
  rw [← lev_repPoint, ← conjOrbit_PJ_rootMap] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hcomm : ∀ g : stdGroup, g ∈ PJ → Commute g rootInv := fun g hg =>
    mul_inv_eq_iff_eq_mul.1 ((mem_centralizer_rootInv_iff g).2 (Subgroup.mem_subgroupOf.1 hg))
  refine ⟨p * leviY * p⁻¹, hcomm _ (mul_mem (mul_mem hp (leviG_mem_PJ _)) (inv_mem hp)),
    conj_commute leviY_comm p, fun x hx hxr hc => ?_⟩
  have hpS : SemidirectProduct.inl p ∈ parStar firstJ :=
    mem_parStar.2 (by rw [SemidirectProduct.left_inl]; exact Subgroup.mem_subgroupOf.1 hp)
  refine not_commute_leviY (x := (SemidirectProduct.inl p)⁻¹ * x * SemidirectProduct.inl p)
    (mul_mem (mul_mem (inv_mem hpS) hx) hpS) ?_ ?_
  · simpa only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inl, inv_one, one_mul, mul_one] using hxr
  · have h := conj_commute hc (SemidirectProduct.inl p)⁻¹
    rw [inv_inv] at h
    have e : (SemidirectProduct.inl p)⁻¹ * SemidirectProduct.inl (p * leviY * p⁻¹) *
        SemidirectProduct.inl p = (SemidirectProduct.inl leviY : GStar) := by
      rw [map_mul, map_mul, map_inv]
      group
    rwa [e] at h

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner
