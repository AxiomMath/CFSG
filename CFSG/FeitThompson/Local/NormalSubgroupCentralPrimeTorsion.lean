module

public import Mathlib.GroupTheory.GroupAction.ConjAct
import CFSG.FeitThompson.Foundations.PGroupFixedPointCongruence
import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite

open MulAction Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a : ℕ} {P : Type*} [Group P] (L : Subgroup P) [L.Normal]

theorem mem_fixedPoints_conjAct_iff {x : ↥L} :
    x ∈ fixedPoints (ConjAct P) ↥L ↔ (x : P) ∈ center P := by
  simp only [mem_fixedPoints, Subgroup.mem_center_iff]
  constructor
  · intro h g
    have hx := congrArg Subtype.val (h (ConjAct.toConjAct g))
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct,
      mul_inv_eq_iff_eq_mul] at hx
    exact hx
  · intro h g
    ext
    rw [ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def, h (ConjAct.ofConjAct g),
      mul_inv_cancel_right]

def fixedPointsConjActEquiv : fixedPoints (ConjAct P) ↥L ≃ ↥(L ⊓ center P) where
  toFun x := ⟨(x.1 : P), Subgroup.mem_inf.mpr ⟨x.1.2, (mem_fixedPoints_conjAct_iff L).mp x.2⟩⟩
  invFun y := ⟨⟨(y : P), (Subgroup.mem_inf.mp y.2).1⟩,
    (mem_fixedPoints_conjAct_iff L).mpr (Subgroup.mem_inf.mp y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem coe_fixedPointsConjActEquiv (x : fixedPoints (ConjAct P) ↥L) :
    ((fixedPointsConjActEquiv L x : ↥(L ⊓ center P)) : P) = (x : ↥L) := (rfl)

theorem natCard_fixedPoints_conjAct :
    Nat.card (fixedPoints (ConjAct P) ↥L) = Nat.card ↥(L ⊓ center P) :=
  Nat.card_congr (fixedPointsConjActEquiv L)

theorem dvd_natCard_inf_center (hp : p.Prime) (hP : Nat.card P = p ^ a) (hL : L ≠ ⊥) :
    p ∣ Nat.card ↥(L ⊓ center P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL
  obtain ⟨n, hn, hcardL⟩ :=
    (IsPGroup.nontrivial_iff_card ((IsPGroup.of_card hP).to_subgroup L)).mp inferInstance
  have hLp : p ∣ Nat.card ↥L := hcardL ▸ dvd_pow_self p hn.ne'
  have hcard : Nat.card (ConjAct P) = p ^ a := by
    rw [Nat.card_congr ConjAct.ofConjAct.toEquiv, hP]
  have hmod := natCard_modEq_natCard_fixedPoints (P := ConjAct P) (X := ↥L) hcard
  rw [natCard_fixedPoints_conjAct] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hLp.modEq_zero_nat)

theorem exists_le_inf_center_natCard_eq (hp : p.Prime) (hP : Nat.card P = p ^ a) (hL : L ≠ ⊥) :
    ∃ Q : Subgroup P, Q ≤ L ⊓ center P ∧ Nat.card Q = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(L ⊓ center P)) p (dvd_natCard_inf_center L hp hP hL)
  refine ⟨zpowers (x : P), Subgroup.zpowers_le.mpr x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

theorem inf_center_ne_bot (hp : p.Prime) (hP : Nat.card P = p ^ a) (hL : L ≠ ⊥) :
    L ⊓ center P ≠ ⊥ := by
  obtain ⟨Q, hQle, hQcard⟩ := exists_le_inf_center_natCard_eq L hp hP hL
  intro h
  rw [h, le_bot_iff] at hQle
  rw [hQle, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hQcard
  exact hp.one_lt.ne hQcard

end

end CFSG.FeitThompson
