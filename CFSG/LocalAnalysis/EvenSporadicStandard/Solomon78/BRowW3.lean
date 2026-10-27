module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowW3Cbar
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowComponent
public import CFSG.Monster.B.CTIB.CoreCensus
public import CFSG.Monster.B.CTIB.Census
public import CFSG.Monster.B.CTIB.SylowCenter
public import CFSG.Monster.B.CTIB.UniqueComponent
public import CFSG.Monster.B.CTIB.Fusion
public import CFSG.Monster.Existence.BabyTableIIIOf
public import CFSG.Monster.Existence.BabyW3Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup MulOpposite CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.GMS
  CFSG.Monster.Existence CFSG.Blueprint.NativeSporadic

theorem op_mul_comm_iff {G : Type*} [Group G] {a b : Gᵐᵒᵖ} :
    a * b = b * a ↔ a.unop * b.unop = b.unop * a.unop := by
  constructor
  · intro h
    have := congrArg MulOpposite.unop h
    simpa using this.symm
  · intro h
    apply MulOpposite.unop_injective
    simpa using h.symm


theorem mem_Jbar_op_iff {y : Sbp} : y ∈ Jbar.op ↔ y * xs = xs * y := by
  rw [Subgroup.mem_op, ← centralizer_xbar, Subgroup.mem_centralizer_singleton_iff, op_mul_comm_iff]
  exact Iff.rfl

theorem Jbar_op_eq_centralizer : Jbar.op = Subgroup.centralizer ({xs} : Set Sbp) := by
  ext y
  rw [mem_Jbar_op_iff, Subgroup.mem_centralizer_singleton_iff]

theorem eq_of_centralizes_qS_seven {z : Sbp}
    (hzc : ∀ y : Sbp, y * qS 7 = qS 7 * y → z * y = y * z) :
    z = 1 ∨ z = xs ∨ z = qS 7 ∨ z = qS 7 * xs := by
  have hwQ : (qS 7).unop ∈ Ebar := Subgroup.mem_op.1 (qS_mem 7)
  have hw2 : (qS 7).unop * (qS 7).unop = 1 := by
    have h : qS 7 * qS 7 = 1 := by
      rw [← rs3_eq]
      exact rs_mul_self (by norm_num)
    have := congrArg MulOpposite.unop h
    simpa using this
  have hgx : z.unop * xbar = xbar * z.unop := by
    have h := hzc xs (op_mul_comm_iff.2 (ebar_comm_xbar hwQ).symm)
    exact (op_mul_comm_iff.1 h)
  have hgT : ∀ t ∈ Ebar, (qS 7).unop * t = t * (qS 7).unop → z.unop * t = t * z.unop := by
    intro t ht hwt
    have h := hzc (op t) (op_mul_comm_iff.2 hwt.symm)
    exact (op_mul_comm_iff.1 h)
  rcases eq_of_commute_ebar_centralizer hwQ hw2 hgx hgT with h | h | h | h
  · left
    exact MulOpposite.unop_injective (by simpa using h)
  · right; left
    exact MulOpposite.unop_injective h
  · right; right; left
    exact MulOpposite.unop_injective h
  · right; right; right
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_mul]
    exact h

theorem natCard_jClass_qS_seven : (jClass (qS 7)).ncard = 4098600 := by
  have h0 : psiS (qS 7) ≠ 0 := psiS_qS_ne_zero (by decide)
  rw [jClass_eq_fiber (qS_mem 7) h0, ncard_fiber, ncard_jOrbit_seven]

theorem natCard_centralizer_qS_seven :
    Nat.card (Subgroup.centralizer ({qS 7} : Set Sbp)) = babyCentOrder 2 := by
  have h := natCard_centralizer_rep_three
  have e1 := Nat.card_congr (@CTIB.centralizerEquiv CFSG.Blueprint.NativeSporadic.B Sbp
    Units.instGroup _ CTIB.iotaEquiv (CTIB.iotaEquiv.symm (CTIB.rs 3))).toEquiv
  rw [MulEquiv.apply_symm_apply] at e1
  rw [← rs3_eq, ← e1]
  exact h

theorem natCard_Jbar_op : Nat.card (Jbar.op) = babyCentOrder 1 := by
  have h := natCard_centralizer_rep_zero
  have e1 := Nat.card_congr (@CTIB.centralizerEquiv CFSG.Blueprint.NativeSporadic.B Sbp
    Units.instGroup _ CTIB.iotaEquiv (babyRep 0)).toEquiv
  rw [babyRep, MulEquiv.apply_symm_apply] at e1
  rw [babyRep] at h
  rw [Jbar_op_eq_centralizer, ← rs0_eq, ← e1]
  exact h

theorem not_centralizer_qS_seven_le_Jbar_op :
    ¬ ∀ y : Sbp, y * qS 7 = qS 7 * y → y ∈ Jbar.op := by
  intro h
  have hC : Jbar.op ⊓ Subgroup.centralizer ({qS 7} : Set Sbp) =
      Subgroup.centralizer ({qS 7} : Set Sbp) :=
    inf_eq_right.2 fun y hy => h y (Subgroup.mem_centralizer_singleton_iff.1 hy)
  have hm := card_inf_centralizer_mul_ncard_conj Jbar.op (qS 7)
  have hset : ({y | ∃ h ∈ Jbar.op, h * qS 7 * h⁻¹ = y} : Set Sbp) = jClass (qS 7) := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨h⁻¹, Jbar.op.inv_mem hh, by group⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, Jbar.op.inv_mem hg, by group⟩
  rw [hC, hset, natCard_jClass_qS_seven, natCard_centralizer_qS_seven, natCard_Jbar_op] at hm
  norm_num [babyCentOrder] at hm

theorem centerInvAt_qS_seven : CenterInvAt (qS 7) := by
  intro z hzz hzc
  have hw2 : qS 7 * qS 7 = 1 := by
    rw [← rs3_eq]
    exact rs_mul_self (by norm_num)
  have hcentral : ∀ y : Sbp, y * qS 7 = qS 7 * y → y * xs = xs * y → y ∈ Jbar.op :=
    fun _ _ h => mem_Jbar_op_iff.2 h
  rcases eq_of_centralizes_qS_seven hzc with h | h | h | h
  · exact Or.inl h
  · exfalso
    refine not_centralizer_qS_seven_le_Jbar_op fun y hy => mem_Jbar_op_iff.2 ?_
    have := hzc y hy
    rw [h] at this
    exact this.symm
  · exact Or.inr h
  · exfalso
    refine not_centralizer_qS_seven_le_Jbar_op fun y hy => mem_Jbar_op_iff.2 ?_
    have h1 := hzc y hy
    rw [h] at h1
    calc y * xs = y * (qS 7 * (qS 7 * xs)) := by rw [← mul_assoc (qS 7) (qS 7) xs, hw2, one_mul]
      _ = (y * qS 7) * (qS 7 * xs) := by rw [mul_assoc]
      _ = (qS 7 * y) * (qS 7 * xs) := by rw [hy]
      _ = qS 7 * (y * (qS 7 * xs)) := by rw [mul_assoc]
      _ = qS 7 * ((qS 7 * xs) * y) := by rw [h1]
      _ = xs * y := by rw [← mul_assoc, ← mul_assoc, hw2, one_mul]

end CFSG.EvenSporadicStandard.Solomon78
