module

public import CFSG.Certificates.Kernel.AS35QTS.EnumSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd V3 M3 mulC e0 I3 powC)

theorem bindP_eq (Y : PL Nat) (k : PL Nat → Bool) : bindP Y k = k Y := by
  simp only [bindP, frc_eqL]

theorem mulK_frc (t : Nat) (X Y : PL Nat) (k : PL Nat → Bool) :
    mulK (natOps t) frc X Y k = k (mulD (natOps t) X Y) :=
  mulK_eq (natOps t) frc_eqL X Y k

theorem lane_cst {t c : Nat} (ht : t.testBit c = true) (n : Nat) :
    laneOf c (cst t n) = ofCd (decN n) := by
  rw [ofCd_decN]
  have h : ∀ b, (Nat.mul (bitN n b) t).testBit c = n.testBit b := by
    intro b
    have := bitN_lt n b
    rw [← bitN_testBit n b]
    interval_cases h : bitN n b
    · simp [Nat.mul_eq]
    · simp [Nat.mul_eq, ht]
  simp only [laneOf, mapP, cst, ofIx, h]

theorem isI3_e (x : Cd) : isI3 bOps (ofCd x) = true ↔ x.m = I3 := by
  obtain ⟨e, a, ⟨⟨a00, a01, a02⟩, ⟨a10, a11, a12⟩, ⟨a20, a21, a22⟩⟩⟩ := x
  simp only [isI3, ofCd, ofV, isOne_e, isZero_e, bOps_a, Bool.and_eq_true, beq_iff_eq, I3,
    M3.mk.injEq, V3.mk.injEq]

theorem bnot_xe : ∀ a b : ZMod 2, bnot bOps (bOps.x (eb a) (eb b)) = true ↔ a = b := by
  decide

theorem eqP_e (x y : Cd) : eqP bOps (ofCd x) (ofCd y) = true ↔ x = y := by
  obtain ⟨e, ⟨a0, a1, a2⟩, ⟨⟨b00, b01, b02⟩, ⟨b10, b11, b12⟩, ⟨b20, b21, b22⟩⟩⟩ := x
  obtain ⟨e', ⟨a0', a1', a2'⟩, ⟨⟨c00, c01, c02⟩, ⟨c10, c11, c12⟩, ⟨c20, c21, c22⟩⟩⟩ := y
  simp only [eqP, eqV, ofCd, ofV, isEq_e, bOps_a, Bool.and_eq_true, beq_iff_eq, bnot_xe,
    Cd.mk.injEq, V3.mk.injEq, M3.mk.injEq]

theorem tb_qpow {t c : Nat} (ht : t.testBit c = true) (X P E : PL Nat) :
    (Nat.land (isI3 (natOps t) X) (bnot (natOps t) (eqP (natOps t) P E))).testBit c =
      (isI3 bOps (laneOf c X) && bnot bOps (eqP bOps (laneOf c P) (laneOf c E))) := by
  simp only [isI3, eqP, eqV, isEq, isOne, isZero, bnot, laneOf, mapP, natOps, bOps, tb_land,
    tb_xor, ht]

theorem bnot_bOps (p : Bool) : bnot bOps p = !p := by cases p <;> rfl

theorem decN_ixE : decN ixE = e0 := rfl

theorem allT_testBit {c : Nat} (hc : c < 82944) : allT.testBit c = true := by
  unfold allT
  generalize hm : (82944 : Nat) = m at hc ⊢
  exact (allOnes_testBit m c).trans (decide_eq_true hc)

theorem incB_lt {N : Nat} {L : List Nat} (h : incB N L = true) : ∀ x ∈ L, x < N :=
  fun x hx => ((incB_go L 0 h).1 x hx).2

theorem qpowOK_spec {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
    (h : qpowOK G = true) :
    ∀ q ∈ CFSG.LargeExtraspecial.AS35QTS.codes, q.m = I3 → powC q 4 = e0 := by
  have hGb : ∀ g ∈ G, g < 2 ^ 18 := fun g hg' => by
    have := incB_lt (gOK_spec hg).1 g hg'
    omega
  intro q hq hm
  rw [codes_eq hG (gu3s_eq hg) hGb] at hq
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
  have hc' := List.mem_range.1 hc
  unfold qpowOK at h
  rw [frc_eqL, lanesK_eq, bindP_eq] at h
  simp only [mulK_frc] at h
  have ht : allT.testBit c = true := allT_testBit hc'
  have hb := congrArg (fun p => Nat.testBit p c) (Nat.eq_of_beq_eq_true h)
  simp only [Nat.zero_testBit] at hb
  rw [tb_qpow ht] at hb
  have hX := lane_lanes hG hGb hc'
  have hE := lane_cst ht ixE
  rw [decN_ixE] at hE
  rw [lane_mulP _ _ (lane_mulP _ _ (lane_mulP _ _ (lane_mulP _ _ hE hX) hX) hX) hX, hX, hE,
    bnot_bOps] at hb
  have hi := (isI3_e _).2 hm
  rw [hi, Bool.true_and, Bool.not_eq_false'] at hb
  exact (eqP_e _ _).1 hb

end CFSG.KC.AS35QTS

end
