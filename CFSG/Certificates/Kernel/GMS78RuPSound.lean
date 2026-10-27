module

public import Certificates.Data.Kernel.GMS78RuP117
public import CFSG.Certificates.Kernel.GMS78RuGenS
import CFSG.Certificates.Kernel.GMS78RuP.Checks

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuS CFSG.GMS78RuSP

@[expose] def sTabs (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8) (ε : Bool)
    (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat) : Prop :=
  (∀ i < 65536, (gA.getD i 0).val = fget (sGamRow GT (i / 256)) (i % 256) 3) ∧
    (∀ i < 2048, (dA.getD i (0, 0)).1 = Nat.land (fget (neGet 0 DPR (i / 256)) (i % 256) 11) 255 ∧
      (dA.getD i (0, 0)).2.val = Nat.shiftRight (fget (neGet 0 DPR (i / 256)) (i % 256) 11) 8) ∧
    (∀ d < 8, ∀ t < 8, (linApply (dct.getD d linId) (fin8Of t)).val = fget LIN (8 * d + t) 3) ∧
    (∀ d < 8, ∀ e < 8, (dMul (fin8Of d) (fin8Of e)).val = fget DM (8 * d + e) 3) ∧
    (∀ d < 8, ∀ e < 8, (ε && dOvf (fin8Of d) (fin8Of e)) = Nat.beq (fget DO (8 * d + e) 1) 1) ∧
    (∀ i < 2048, (dA.getD i (0, 0)).1 < 256)

private theorem mul_code {gA : Array (Fin 8)} {dA : Array (Nat × Fin 8)} {dct : List Lin8}
    {GT : List (List Nat)} {DPR : List Nat} {LIN DM DO : Nat}
    (hT : sTabs gA dA dct true GT DPR LIN DM DO) :
    P117.MulCode (sMulK GT DPR LIN DM DO) gA dA dct := by
  obtain ⟨hg, hd, hl, hm, ho, h256⟩ := hT
  have key : ∀ p q : Pt, p.1 < 256 → q.1 < 256 →
      sMulK GT DPR LIN DM DO (P117.pCode p) (P117.pCode q) =
        P117.pCode (Gen.pMulG gA dA dct p q) ∧ (Gen.pMulG gA dA dct p q).1 < 256 := by
    rintro ⟨pc, pt, pd⟩ ⟨qc, qt, qd⟩ hp hq
    dsimp only at hp hq
    have hpd := pd.isLt
    have hqd := qd.isLt
    have hqt := qt.isLt
    have hi : 256 * pd.val + qc < 2048 := by omega
    obtain ⟨hd1, hd2⟩ := hd _ hi
    have e1 : (256 * pd.val + qc) / 256 = pd.val := by omega
    have e2 : (256 * pd.val + qc) % 256 = qc := by omega
    rw [e1, e2] at hd1 hd2
    have hb := h256 _ hi
    set dp := dA.getD (256 * pd.val + qc) (0, 0) with hdp
    have hj : 256 * pc + dp.1 < 65536 := by omega
    have hgg := hg _ hj
    have e3 : (256 * pc + dp.1) / 256 = pc := by omega
    have e4 : (256 * pc + dp.1) % 256 = dp.1 := by omega
    rw [e3, e4] at hgg
    have hl' := hl pd.val pd.isLt qt.val qt.isLt
    have hm' := hm pd.val pd.isLt qd.val qd.isLt
    have ho' := ho pd.val pd.isLt qd.val qd.isLt
    have f8 : ∀ a : Fin 8, fin8Of a.val = a := fun a => Fin.ext (Nat.mod_eq_of_lt a.isLt)
    rw [f8] at hl' hm' ho'
    rw [f8] at hm' ho'
    have hov : fget DO (8 * pd.val + qd.val) 1 ≤ 1 := Nat.and_le_right
    have hdo : (if (true && dOvf pd qd) = true then (1 : Fin 8) else 0).val =
        fget DO (8 * pd.val + qd.val) 1 := by
      rw [ho']
      by_cases h : (fget DO (8 * pd.val + qd.val) 1).beq 1 = true
      · rw [if_pos h, Nat.eq_of_beq_eq_true h]
        rfl
      · rw [if_neg h]
        have h1 : fget DO (8 * pd.val + qd.val) 1 ≠ 1 := fun h' => h (by rw [h']; rfl)
        have h0 : fget DO (8 * pd.val + qd.val) 1 = 0 := by omega
        rw [h0]
        rfl
    have hR : P117.pCode (Gen.pMulG gA dA dct (pc, pt, pd) (qc, qt, qd)) =
        (pc ^^^ dp.1) |||
          ((pt.val ^^^ (linApply (dct.getD pd.val linId) qt).val ^^^ dp.2.val ^^^
            (gA.getD (256 * pc + dp.1) 0).val ^^^
            (if (true && dOvf pd qd) = true then (1 : Fin 8) else 0).val) <<< 8) |||
          ((dMul pd qd).val <<< 11) := by
      simp only [P117.pCode, Gen.pMulG, Gen.sMulFG, P117.fin8_xor_val]
      rfl
    refine ⟨?_, ?_⟩
    · unfold sMulK
      rw [P117.pCode_c hp, P117.pCode_t hp, P117.pCode_d hp, P117.pCode_c hq, P117.pCode_t hq,
        P117.pCode_d hq, hR]
      simp only [Nat.add_eq, Nat.mul_eq]
      rw [← hd1, ← hd2, ← hgg, ← hl', ← hm', ← hdo, Nat.or_assoc]
      rfl
    · change (pc ^^^ dp.1) < 256
      exact Nat.xor_lt_two_pow (n := 8) hp hb
  exact ⟨fun p q hp hq => (key p q hp hq).1, fun p q hp hq => (key p q hp hq).2⟩

theorem check15117_sound (gA : Array (Fin 8)) (dA : Array (Nat × Fin 8)) (dct : List Lin8)
    (xs : List Pt) (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO JM : Nat)
    (XS CXL F1L KL : List Nat)
    (hT : sTabs gA dA dct true GT DPR LIN DM DO)
    (hX : XS = xs.map fun x => x.1 ||| (x.2.1.val <<< 8) ||| (x.2.2.val <<< 11))
    (hXs : xs.all (fun x => decide (x.1 < 256)) = true)
    (hJ : ∀ i < 16384, kJM (sMulK GT DPR LIN DM DO) XS JM i = true)
    (hA : kA117 (sMulK GT DPR LIN DM DO) XS JM = true)
    (hL : kLists117 (sMulK GT DPR LIN DM DO) XS JM CXL F1L KL = true)
    (hCx : ∀ i < CXL.length, kCx (sMulK GT DPR LIN DM DO) JM (CXL.getD i 0) = true)
    (hF1 : ∀ i < F1L.length, kF1 (sMulK GT DPR LIN DM DO) JM (F1L.getD i 0) = true)
    (hF3 : ∀ i < KL.length, kF3 (sMulK GT DPR LIN DM DO) JM (KL.getD i 0) = true) :
    Gen.checkAG gA dA dct xs = true ∧ Gen.checkCaG gA dA dct = true ∧
      Gen.checkCxG gA dA dct xs = true ∧ Gen.checkF1G gA dA dct xs = true ∧
      Gen.checkF3G gA dA dct xs = true ∧ Gen.checkJdG gA dA dct xs = true := by
  have hxs' : ∀ x ∈ xs, x.1 < 256 := fun x hx => of_decide_eq_true (List.all_eq_true.1 hXs x hx)
  have hX' : XS = xs.map P117.pCode := hX
  subst hX'
  exact P117.checks_of (mul_code hT) hxs' hJ hA hL hCx hF1 hF3

end CFSG.KC.GMS

end
