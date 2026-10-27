module

public import CFSG.Certificates.Kernel.AS35QTS.LaneSound
public import CFSG.Certificates.Kernel.F4M3BSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd V3 M3 unitB hermC)

theorem beq_F4 (x y : F4) : (x == y) = decide (x.code = y.code) := by
  change decide (x = y) = _
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  simp only [F4.mk.injEq]

theorem isOne_e (x : F4) : isOne bOps (lb x) (hb x) = (x == 1) := by
  rw [beq_F4]
  obtain ⟨c⟩ := x
  fin_cases c <;> rfl

theorem isZero_e (x : F4) : isZero bOps (lb x) (hb x) = (x == 0) := by
  rw [beq_F4]
  obtain ⟨c⟩ := x
  fin_cases c <;> rfl

theorem isEq_e (x y : F4) : isEq bOps (lb x) (hb x) (lb y) (hb y) = (x == y) := by
  rw [beq_F4]
  obtain ⟨c⟩ := x
  obtain ⟨d⟩ := y
  fin_cases c <;> fin_cases d <;> rfl

theorem bOps_a (p q : Bool) : bOps.a p q = (p && q) := rfl

theorem unitT_ofCd (z : Cd) : unitT bOps (ofCd z) = unitB z.m := by
  have h0 : col0 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col0 z.m) := rfl
  have h1 : col1 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col1 z.m) := rfl
  have h2 : col2 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col2 z.m) := rfl
  simp only [unitT, h0, h1, h2, hL_e, hH_e, isOne_e, isZero_e, bOps_a, unitB, Bool.and_assoc]

theorem unitT_lane {t c : Nat} (ht : t.testBit c = true) (X : PL Nat) :
    (unitT (natOps t) X).testBit c = unitT bOps (laneOf c X) := by
  simp only [unitT, isOne, isZero, bnot, hL, hH, dl, dh, pl, ph, col0, col1, col2, laneOf, mapP,
    natOps, bOps, tb_land, tb_xor, ht]

theorem ind_testBit (c : Nat) : ∀ L : List Nat, (ind L).testBit c = decide (c ∈ L)
  | [] => by
    change Nat.testBit 0 c = _
    simp
  | d :: L => by
    change ((1 <<< d) ||| ind L).testBit c = _
    rw [Nat.testBit_or, ind_testBit c L, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : d = c
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem and'_eq (a b : Bool) : Bool.and' a b = (a && b) := by
  cases a <;> cases b <;> rfl

theorem allOnes_testBit (m c : Nat) : (Nat.sub (Nat.pow 2 m) 1).testBit c = decide (c < m) := by
  change (2 ^ m - 1).testBit c = _
  exact Nat.testBit_two_pow_sub_one m c

theorem lane_mat {c : Nat} (hc : c < 2 ^ 18) :
    laneOf c (⟨0, ⟨0, 0, 0, 0, 0, 0⟩, ⟨pln 16 18, pln 17 18, pln 14 18, pln 15 18, pln 12 18,
      pln 13 18⟩, ⟨pln 10 18, pln 11 18, pln 8 18, pln 9 18, pln 6 18, pln 7 18⟩,
      ⟨pln 4 18, pln 5 18, pln 2 18, pln 3 18, pln 0 18, pln 1 18⟩⟩ : PL Nat) =
      ofCd (decN c) := by
  have hz : ∀ b, 18 ≤ b → c.testBit b = false := fun b hb =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hb))
  rw [ofCd_decN]
  simp only [laneOf, mapP, ofIx, pln_bit, hc, decide_true, Bool.true_and, Nat.zero_testBit,
    hz 18 (by norm_num), hz 19 (by norm_num), hz 20 (by norm_num), hz 21 (by norm_num),
    hz 22 (by norm_num), hz 23 (by norm_num), hz 24 (by norm_num)]

theorem gOK_spec {G : List Nat} (h : gOK G = true) :
    incB 262144 G = true ∧ ∀ c < 2 ^ 18, (unitB (decN c).m = true ↔ c ∈ G) := by
  unfold gOK at h
  rw [and'_eq, Bool.and_eq_true, frc_eq] at h
  refine ⟨h.1, fun c hc => ?_⟩
  have h2 := h.2
  unfold matK at h2
  simp only [frc_eq] at h2
  generalize hm : (262144 : Nat) = m at h2
  have he := congrArg (fun p => Nat.testBit p c) (Nat.eq_of_beq_eq_true h2)
  have ht : (Nat.sub (Nat.pow 2 m) 1).testBit c = true :=
    (allOnes_testBit m c).trans (decide_eq_true (by omega))
  rw [unitT_lane ht, lane_mat hc, unitT_ofCd, ind_testBit] at he
  rw [he, decide_eq_true_iff]

end CFSG.KC.AS35QTS

end
