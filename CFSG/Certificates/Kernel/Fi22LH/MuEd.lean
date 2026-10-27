module

public import CFSG.Certificates.Kernel.Fi22LH.Rows
public import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.Certificates.Kernel.Fi22LH.Card
import CFSG.Certificates.Kernel.Fi22LH.Pop
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.EdgeWit
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.MuTree
import CFSG.Certificates.Kernel.Fi22LH.RowPhi
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import Mathlib.Data.List.Find

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW

variable {D : LHData}

private theorem muw_bitAt_bitsOfNat {a y : Nat} (hy : y < 3520) :
    bitAt (bitsOfNat a) y = a.testBit y :=
  Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat a).2 y hy)

private theorem muw_two_pow_le {m n : Nat} (h : m ≤ n) : 2 ^ m ≤ 2 ^ n :=
  Nat.pow_le_pow_right (by decide) h

private theorem muw_andPop_bitsOfNat {a b N : Nat} (ha : a < 2 ^ N) (hN : N ≤ 3520) :
    andPop (bitsOfNat a) (bitsOfNat b) = popK masks (Nat.land a b) := by
  have hab : Nat.land a b < 2 ^ N := Nat.lt_of_le_of_lt Nat.and_le_left ha
  have hpop : Nat.land a b < 2 ^ 3584 :=
    lt_of_lt_of_le hab (muw_two_pow_le (by omega))
  rw [andPop_eq (by simp [bitsOfNat]) (by simp [bitsOfNat]), popK_eq hpop]
  have hbit : (List.range 3520).countP
      (fun y => bitAt (bitsOfNat a) y && bitAt (bitsOfNat b) y) =
      (List.range 3520).countP fun y => (Nat.land a b).testBit y := by
    refine List.countP_congr fun y hy => ?_
    rw [muw_bitAt_bitsOfNat (List.mem_range.1 hy),
      muw_bitAt_bitsOfNat (List.mem_range.1 hy), show Nat.land a b = a &&& b from rfl,
      Nat.testBit_and]
  rw [hbit]
  have hzero : ∀ i < 64, (Nat.land a b).testBit (3520 + i) = false := fun i hi =>
    Nat.testBit_lt_two_pow (x := Nat.land a b) (i := 3520 + i)
      (lt_of_lt_of_le hab (muw_two_pow_le (by omega)))
  have htail : ((List.range 64).map (3520 + ·)).countP
      (fun y => (Nat.land a b).testBit y) = 0 := by
    rw [List.countP_map]
    exact List.countP_eq_zero.2 fun i hi => Bool.eq_false_iff.mp (hzero i (List.mem_range.1 hi))
  rw [show 3584 = 3520 + 64 by decide, List.range_add, List.countP_append, htail,
    Nat.add_zero]

private theorem muw_muWD_get {f : Nat} (hf : f < 3510) :
    (muWD D)[f]! = fd (D.P f) 14 4095 := by
  unfold muWD
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem muw_mkMuW_get {f : Nat} (hf : f < 3510) :
    (mkMuW (tauAll orbL) (commBits (tauAll orbL)) (bitsOf (lhData ())[0]!)
      (orbDec D.QA) (rowRD D) (fd D.mt 0 16383))[f]! =
      (if bitAt (bitsOf (lhData ())[0]!) f then 3510 else
        if andPop ((orbDec D.QA).sets[(rowRD D)[f]!]!)
            ((orbDec D.QA).sets[fd D.mt 0 16383]!) == 63 then
          edgeWit (tauAll orbL) (commBits (tauAll orbL))
            ((orbDec D.QA).sets[(rowRD D)[f]!]!) ((orbDec D.QA).sets[fd D.mt 0 16383]!)
        else 3510) := by
  unfold mkMuW
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem muw_muK (h : LHChecks D) {f : Nat} (hf : f < 3510) :
    (if (memB (bs D.lb0) f) = true then Nat.beq (fd (D.P f) 14 4095) 3510 else
      if (Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
          (sb (D.QA (fd D.mt 0 16383))))) 63) = true then
        edgeK D.R D.Z (D.QA (fd (D.P f) 0 16383)) (sb (D.QA (fd (D.P f) 0 16383)))
          (sb (D.QA (fd D.mt 0 16383))) (fd (D.P f) 14 4095)
      else Nat.beq (fd (D.P f) 14 4095) 3510) = true := by
  have hs := h.mu (f / 880) (by omega)
  unfold muSlW at hs
  rw [strictB_eq, strictB_eq, strictB_eq] at hs
  have hm := allN_iff.1 hs (f % 880) (Nat.mod_lt _ (by decide))
  unfold muSl at hm
  have e : Nat.add (Nat.mul (nat_lit 880) (f / 880)) (f % 880) = f := by
    change 880 * (f / 880) + f % 880 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at hm
  unfold muK at hm
  simpa only [strictB_eq, bIf_eq] using hm

theorem muW_eq (hO : OrbOK) (h : LHChecks D) :
    mkMuW (tauAll orbL) (commBits (tauAll orbL)) (bitsOf (lhData ())[0]!) (orbDec D.QA) (rowRD D)
      (fd D.mt 0 16383) = muWD D := by
  have hv0 : fd D.mt 0 16383 < 14080 := (farK_spec h).1
  refine ext_get! (N := 3510) ?_ ?_ fun f hf => ?_
  · unfold mkMuW
    rw [Array.size_ofFn]
  · unfold muWD
    rw [Array.size_ofFn]
  · rw [muw_mkMuW_get hf, muw_muWD_get hf]
    have hbB := B0_at h hf
    by_cases hb : (bs D.lb0).testBit f = true
    · have hroot : bitAt (bitsOf (lhData ())[0]!) f = true := by rw [hbB, hb]
      have hmk := muw_muK h hf
      rw [memB_eq, hb, if_pos rfl] at hmk
      have hw : fd (D.P f) 14 4095 = 3510 := Nat.eq_of_beq_eq_true hmk
      rw [hroot, if_pos rfl, hw]
    · have hbf : (bs D.lb0).testBit f = false := Bool.eq_false_iff.2 hb
      have hout : bitAt (bitsOf (lhData ())[0]!) f = false := by rw [hbB, hbf]
      rw [hout, if_neg (by simp)]
      have hmk := muw_muK h hf
      rw [memB_eq, hbf, if_neg (by simp)] at hmk
      have hq : fd (D.P f) 0 16383 < 14080 := ((rowF_spec h hf).2 hbf).1
      have hA : (orbDec D.QA).sets[(rowRD D)[f]!]! =
          bitsOfNat (sb (D.QA (fd (D.P f) 0 16383))) := by
        rw [rowR_get hf, orbDec_sets _ hq]
      have hV : (orbDec D.QA).sets[fd D.mt 0 16383]! =
          bitsOfNat (sb (D.QA (fd D.mt 0 16383))) := orbDec_sets _ hv0
      have hand : andPop ((orbDec D.QA).sets[(rowRD D)[f]!]!)
          ((orbDec D.QA).sets[fd D.mt 0 16383]!) =
          popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
            (sb (D.QA (fd D.mt 0 16383)))) := by
        rw [hA, hV]
        exact muw_andPop_bitsOfNat (sb_lt _) (by decide)
      rw [hand]
      by_cases hc : (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
          (sb (D.QA (fd D.mt 0 16383)))) == 63) = true
      · have hc' : Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
            (sb (D.QA (fd D.mt 0 16383))))) 63 = true := hc
        rw [hc', if_pos rfl] at hmk
        rw [if_pos hc]
        rw [hA, hV]
        exact (edgeWit_eq_of_edgeK hO h hq hv0 hmk).2.2
      · have hc' : Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P f) 0 16383)))
            (sb (D.QA (fd D.mt 0 16383))))) 63 = false := Bool.eq_false_iff.2 hc
        rw [hc', if_neg (by simp)] at hmk
        have hw : fd (D.P f) 14 4095 = 3510 := Nat.eq_of_beq_eq_true hmk
        rw [if_neg hc, hw]

theorem muTree_eq (hO : OrbOK) (h : LHChecks D) :
    mkMuTree (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D) (muWD D) =
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 0 4095,
        Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 12 1023,
        Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 22 4095) :=
  muTree_eq_of hO h

private theorem edw_qa_mem_lt (h : LHChecks D) (hv0 : fd D.mt 0 16383 < 14080) :
    ∀ j < 351, ent (D.QA (fd D.mt 0 16383)) j < 3510 := by
  intro j hj
  have hb := (sb_mem h.setA hv0 (ent (D.QA (fd D.mt 0 16383)) j)).2 ⟨j, hj, rfl⟩
  rw [testBit_sb] at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.1

private theorem edw_edK (h : LHChecks D) {hN : Nat} (hh : hN < 3510) :
    (memB (sb (D.QA (fd D.mt 0 16383))) hN = true →
      fd (D.P hN) 26 16383 = 14080) ∧
    (memB (sb (D.QA (fd D.mt 0 16383))) hN = false →
      fd (D.P hN) 26 16383 < 14080 ∧
      ∀ j < 351, (sb (D.QA (fd (D.P hN) 26 16383))).testBit
        (ent (D.R hN) (ent (D.QA (fd D.mt 0 16383)) j)) = true) := by
  have hs := h.ed (hN / 440) (by omega)
  unfold edSlW edSl at hs
  rw [strictB_eq, strictB_eq, strictB_eq] at hs
  have hstep := allN_iff.1 hs (hN % 440) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 440) (hN / 440)) (hN % 440) = hN := by
    change 440 * (hN / 440) + hN % 440 = hN
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hh)] at hstep
  unfold edK at hstep
  simp only [strictB_eq] at hstep
  rw [bIf_eq] at hstep
  constructor
  · intro hmb
    rw [if_pos hmb, bAnd_eq, Bool.and_eq_true] at hstep
    exact Nat.eq_of_beq_eq_true hstep.1
  · intro hmb
    rw [if_neg (by rw [hmb]; simp), bAnd_eq, Bool.and_eq_true] at hstep
    obtain ⟨h1, h2⟩ := hstep
    rw [Nat.blt_eq] at h1
    rw [bAnd_eq, Bool.and_eq_true] at h2
    refine ⟨h1, fun j hj => ?_⟩
    simpa only [memB_eq] using allN_iff.1 h2.1 j hj

private theorem edw_sb_img (hO : OrbOK) (h : LHChecks D) {hN : Nat} (hh : hN < 3510)
    (hv0 : fd D.mt 0 16383 < 14080) (he : fd (D.P hN) 26 16383 < 14080)
    (hsub : ∀ j < 351, (sb (D.QA (fd (D.P hN) 26 16383))).testBit
      (ent (D.R hN) (ent (D.QA (fd D.mt 0 16383)) j)) = true) (y : Nat) :
    (sb (D.QA (fd (D.P hN) 26 16383))).testBit y = true ↔
      ∃ j < 351, ent (D.R hN) (ent (D.QA (fd D.mt 0 16383)) j) = y := by
  have hqv := edw_qa_mem_lt h hv0
  rw [sb_mem h.setA he]
  refine img_eq_of_sub (g := fun j => ent (D.R hN) (ent (D.QA (fd D.mt 0 16383)) j))
    (e := fun j => ent (D.QA (fd (D.P hN) 26 16383)) j) ?_ ?_ y
  · intro i hi j hj e
    exact ent_inj_of_setSl h.setA hv0 i hi j hj (row_inj hO h hh (hqv i hi) (hqv j hj) e)
  · intro j hj
    exact (sb_mem h.setA he _).1 (hsub j hj)

private theorem edw_imgBits (hO : OrbOK) (h : LHChecks D) {hN : Nat} (hh : hN < 3510)
    (hv0 : fd D.mt 0 16383 < 14080) (he : fd (D.P hN) 26 16383 < 14080)
    (hsub : ∀ j < 351, (sb (D.QA (fd (D.P hN) 26 16383))).testBit
      (ent (D.R hN) (ent (D.QA (fd D.mt 0 16383)) j)) = true) :
    imgBits (tauAll orbL)[hN]! (bitsOfNat (sb (D.QA (fd D.mt 0 16383)))) =
      bitsOfNat (sb (D.QA (fd (D.P hN) 26 16383))) := by
  have hT := tauAll_TR hO h hN hh
  have hqv := edw_qa_mem_lt h hv0
  refine BitsIs.eq_bitsOfNat (bitsIs_imgBits (bitsIs_bitsOfNat _) fun x hx _ => by
    rw [(hT.2 x hx).1]
    have := (hT.2 x hx).2
    omega) fun y _ => ?_
  constructor
  · rintro ⟨x, hx, hxS, rfl⟩
    rw [(hT.2 x hx).1]
    obtain ⟨j, hj, rfl⟩ := (sb_mem h.setA hv0 x).1 hxS
    exact hsub j hj
  · intro hb
    obtain ⟨j, hj, rfl⟩ := (edw_sb_img hO h hh hv0 he hsub y).1 hb
    exact ⟨ent (D.QA (fd D.mt 0 16383)) j, hqv j hj,
      (sb_mem h.setA hv0 _).2 ⟨j, hj, rfl⟩, (hT.2 _ (hqv j hj)).1⟩

theorem edW_eq (hO : OrbOK) (h : LHChecks D) :
    mkEdW (tauAll orbL) (orbDec D.QA) (fd D.mt 0 16383) = edWD D := by
  have hv0 := (farK_spec h).1
  unfold mkEdW edWD
  congr 1
  funext hf
  dsimp only
  rw [orbDec_sets D.QA hv0]
  have hh := hf.2
  have hK := edw_edK h hh
  by_cases hbit : bitAt (bitsOfNat (sb (D.QA (fd D.mt 0 16383)))) hf.val = true
  · have hmb : memB (sb (D.QA (fd D.mt 0 16383))) hf.val = true := by
      rw [memB_eq]
      exact ((bitsIs_bitsOfNat (sb (D.QA (fd D.mt 0 16383)))).2 hf.val
        (by omega)).1 hbit
    rw [if_pos hbit]
    exact (hK.1 hmb).symm
  · have hmb : memB (sb (D.QA (fd D.mt 0 16383))) hf.val = false := by
      rw [memB_eq]
      exact Bool.eq_false_iff.2 fun ht =>
        hbit (((bitsIs_bitsOfNat (sb (D.QA (fd D.mt 0 16383)))).2 hf.val
          (by omega)).2 ht)
    obtain ⟨he, hsub⟩ := hK.2 hmb
    rw [if_neg hbit, edw_imgBits hO h hh hv0 he hsub]
    exact find_orbDec_of (fun i hi j hj e => sb_inj h.walkA hi hj e) he rfl

private theorem ced_edWD_get {f : Nat} (hf : f < 3510) :
    (edWD D)[f]! = fd (D.P f) 26 16383 := by
  unfold edWD
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem ced_edK {f : Nat} (hf : f < 3510) (hchk : LHChecks D) :
    edK D.R D.Z D.P D.QA D.G masks D.mq D.ml (D.QA (fd D.mt 0 16383))
      (sb (D.QA (fd D.mt 0 16383))) f = true := by
  have hs := hchk.ed (f / 440) (by omega)
  unfold edSlW edSl at hs
  rw [strictB_eq, strictB_eq, strictB_eq] at hs
  have hi := allN_iff.1 hs (f % 440) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 440) (f / 440)) (f % 440) = f := by
    change 440 * (f / 440) + f % 440 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at hi
  exact hi

private theorem ced_root_muW (hchk : LHChecks D) {f : Nat} (hf : f < 3510)
    (hb : (bs D.lb0).testBit f = true) : fd (D.P f) 14 4095 = 3510 := by
  have hmk := muw_muK hchk hf
  rw [memB_eq, hb, if_pos rfl] at hmk
  exact Nat.eq_of_beq_eq_true hmk

private theorem ced_ml_facts (hchk : LHChecks D) :
    fd D.mt 70 1023 = 648 ∧
      (∀ i j, i < j → j < 648 → ent D.ml i < ent D.ml j) ∧
      (∀ i < 648, ent D.ml i < 3510) ∧
      (∀ i < 648, fld(D.mq, 10 * ent D.ml i, 1023) < 648) := by
  have hm := hchk.ml
  unfold mlK at hm
  simp only [bAnd_eq, Bool.and_eq_true] at hm
  obtain ⟨hnm, hinc, hlast, hpos⟩ := hm
  have hnm' : fd D.mt 70 1023 = 648 := Nat.eq_of_beq_eq_true hnm
  have hstep : ∀ i < 647, ent D.ml i < ent D.ml (i + 1) := by
    intro i hi
    have h := allN_iff.1 hinc i hi
    rwa [Nat.blt_eq] at h
  have hinc' : ∀ i j, i < j → j < 648 → ent D.ml i < ent D.ml j := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge i j with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hstep j (by omega))
      · have e : i = j := by omega
        subst e
        exact hstep i (by omega)
  have hlast' : ent D.ml 647 < 3510 := by
    have h := hlast
    rwa [Nat.blt_eq] at h
  refine ⟨hnm', hinc', fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_or_ge i 647 with h | h
    · exact Nat.lt_trans (hinc' i 647 h (by omega)) hlast'
    · have e : i = 647 := by omega
      subst e
      exact hlast'
  · have h := allN_iff.1 hpos i hi
    rw [hnm'] at h
    rwa [Nat.blt_eq] at h

private theorem ced_muTree_spec (h : LHChecks D) :
    (∀ k < 648, fd (D.P (fd (D.M k) 0 4095)) 14 4095 < 3510 ∧
      D.G k = sb (rowSet D.P D.QA (fd (D.M k) 0 4095))) ∧
    (∀ k < 648, fld(D.mq, 10 * fd (D.M k) 0 4095, 1023) = k) ∧
    (∀ x < 3510, fld(D.mq, 10 * x, 1023) = 1023 ∨
      (fld(D.mq, 10 * x, 1023) < 648 ∧
        fd (D.M (fld(D.mq, 10 * x, 1023))) 0 4095 = x)) ∧
    (∀ f < 3510, fd (D.P f) 14 4095 < 3510 → fld(D.mq, 10 * f, 1023) < 648) := by
  have hnm := (ced_ml_facts h).1
  have hs := h.muTree
  unfold muTreeW at hs
  rw [strictB_eq] at hs
  unfold muTreeK at hs
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hs
  obtain ⟨-, -, -, -, hk, hpos, hall, -⟩ := hs
  rw [hnm] at hk hpos hall
  unfold posK at hpos
  rw [bAnd_eq, Bool.and_eq_true] at hpos
  refine ⟨fun k hkk => ?_, fun k hkk => ?_, fun x hx => ?_, fun f hf hPf => ?_⟩
  · have := allN_iff.1 hk k hkk
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · have h := allN_iff.1 hpos.1 k hkk
    rwa [Nat.beq_eq] at h
  · have h := allN_iff.1 hpos.2 x hx
    rw [strictB_eq, bIf_eq] at h
    dsimp only at h
    split_ifs at h with hb
    · left
      rwa [Nat.beq_eq] at hb
    · right
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      exact h
  · have := allN_iff.1 hall f hf
    rw [bIf_eq] at this
    rw [if_pos (blt_true hPf)] at this
    rwa [Nat.blt_eq] at this

private noncomputable def edeS (D : LHData) : Finset Nat :=
  (Finset.range 3510).filter fun f => fd (D.P f) 14 4095 < 3510

private theorem ede_land_comm (a b : Nat) : Nat.land a b = Nat.land b a :=
  Nat.and_comm a b

private theorem ede_V_get (h : LHChecks D) :
    (orbDec D.QA).sets[fd D.mt 0 16383]! = bitsOfNat (sb (D.QA (fd D.mt 0 16383))) :=
  orbDec_sets _ (farK_spec h).1

private theorem ede_bitAt_V (h : LHChecks D) {m : Nat} (hm : m < 3510) :
    bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) m =
      (sb (D.QA (fd D.mt 0 16383))).testBit m := by
  rw [ede_V_get h]
  exact Bool.eq_iff_iff.2 ((bitsIs_bitsOfNat _).2 m (by omega))

private theorem ede_ml_mono (h : LHChecks D) {i j : Nat} (hij : i ≤ j) (hj : j < 648) :
    ent D.ml i ≤ ent D.ml j := by
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact le_of_lt ((ced_ml_facts h).2.1 i j hlt hj)

private theorem ede_ml_inj (h : LHChecks D) {i j : Nat} (hi : i < 648) (hj : j < 648)
    (e : ent D.ml i = ent D.ml j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (ced_ml_facts h).2.1 i j hlt hj
    omega
  · have := (ced_ml_facts h).2.1 j i hlt hi
    omega

private theorem ede_ml_inS (h : LHChecks D) {i : Nat} (hi : i < 648) :
    fd (D.P (ent D.ml i)) 14 4095 < 3510 := by
  obtain ⟨hPk, -, hP2, -⟩ := ced_muTree_spec h
  have hlt := (ced_ml_facts h).2.2.1 i hi
  have hp := (ced_ml_facts h).2.2.2 i hi
  rcases hP2 (ent D.ml i) hlt with e | ⟨-, hpts⟩
  · omega
  · rw [← hpts]
    exact (hPk _ hp).1

private theorem ede_S_eq (h : LHChecks D) :
    edeS D = (Finset.range 648).image (fun i => ent D.ml i) := by
  classical
  obtain ⟨-, -, hP2, hall⟩ := ced_muTree_spec h
  have hSsub : edeS D ⊆ (Finset.range 648).image (fun k => fd (D.M k) 0 4095) := by
    intro f hf
    simp only [edeS, Finset.mem_filter, Finset.mem_range] at hf
    obtain ⟨hf3510, hPf⟩ := hf
    have hp := hall f hf3510 hPf
    rcases hP2 f hf3510 with e | ⟨-, hpts⟩
    · omega
    · exact Finset.mem_image.2 ⟨fld(D.mq, 10 * f, 1023), Finset.mem_range.2 hp, hpts⟩
  have hScard : (edeS D).card ≤ 648 := by
    refine le_trans (Finset.card_le_card hSsub) ?_
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
  have hTS : (Finset.range 648).image (fun i => ent D.ml i) ⊆ edeS D := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hf
    simp only [edeS, Finset.mem_filter, Finset.mem_range]
    exact ⟨(ced_ml_facts h).2.2.1 i (Finset.mem_range.1 hi),
      ede_ml_inS h (Finset.mem_range.1 hi)⟩
  have hTcard : ((Finset.range 648).image (fun i => ent D.ml i)).card = 648 := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    exact ede_ml_inj h (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) e
  exact (Finset.eq_of_subset_of_card_le hTS (by rw [hTcard]; exact hScard)).symm

private theorem ede_ml_enum (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hP : fd (D.P f) 14 4095 < 3510) : ∃ t < 648, ent D.ml t = f := by
  have hfS : f ∈ edeS D := by
    simp only [edeS, Finset.mem_filter, Finset.mem_range]
    exact ⟨hf, hP⟩
  rw [ede_S_eq h] at hfS
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 hfS
  exact ⟨t, Finset.mem_range.1 ht, e⟩

private theorem ede_ml_lt_enum (h : LHChecks D) {i f : Nat} (hf : f < 3510)
    (hP : fd (D.P f) 14 4095 < 3510) (hlt : f < ent D.ml i) : ∃ s < i, ent D.ml s = f := by
  obtain ⟨s, hs, e⟩ := ede_ml_enum h hf hP
  refine ⟨s, ?_, e⟩
  by_contra hs'
  have hle : ent D.ml i ≤ ent D.ml s := ede_ml_mono h (by omega) hs
  omega

private theorem ede_find?_filter_range {P p : Nat → Bool} {N k : Nat} (hk : k < N)
    (hPk : P k = true) (hpk : p k = true) (hpre : ∀ t < k, P t = true → p t = false) :
    (List.filter P (List.range N)).find? p = some k := by
  obtain ⟨r, rfl⟩ : ∃ r, N = k + 1 + r := ⟨N - k - 1, by omega⟩
  rw [List.range_add, List.filter_append, List.range_succ, List.filter_append,
    List.filter_cons_of_pos hPk, List.filter_nil]
  rw [List.find?_append, List.find?_append]
  have h1 : (List.filter P (List.range k)).find? p = none :=
    List.find?_eq_none.2 fun t ht => by
      rw [List.mem_filter] at ht
      have := hpre t (List.mem_range.1 ht.1) ht.2
      rw [this]
      decide
  rw [h1, List.find?_singleton, if_pos hpk]
  rfl

private theorem ede_rowR_lt (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hP : fd (D.P f) 14 4095 < 3510) : (rowRD D)[f]! < 14080 := by
  have hb0 : (bs D.lb0).testBit f = false := Bool.eq_false_iff.2 fun hb => by
    have := ced_root_muW h hf hb
    omega
  rw [rowR_get hf]
  exact ((rowF_spec h hf).2 hb0).1

private theorem ede_mem_facts (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = true) :
    fd (D.P m) 26 16383 = 14080 ∧ fd (D.P m) 40 4095 = 3510 ∧
      fd (D.P m) 52 4095 = 3510 := by
  have hk := ced_edK hm h
  unfold edK at hk
  simp only [strictB_eq, bAnd_eq, memB_eq, Nat.blt_eq, Nat.beq_eq] at hk
  rw [bIf_eq] at hk
  rw [if_pos hb] at hk
  simp only [Bool.and_eq_true, Nat.beq_eq] at hk
  exact hk

private theorem ede_nonfar_facts (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = false) :
    fd (D.P m) 26 16383 < 14080 ∧
      (farB D.QA (fd (D.P m) 26 16383) = false →
        fd (D.P m) 40 4095 = 3510 ∧ fd (D.P m) 52 4095 = 3510) := by
  have hk := ced_edK hm h
  unfold edK at hk
  simp only [strictB_eq, bAnd_eq, memB_eq, Nat.blt_eq, Nat.beq_eq] at hk
  simp only [bIf_eq] at hk
  rw [if_neg (by rw [hb]; simp)] at hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hk
  obtain ⟨h1, -, h2⟩ := hk
  refine ⟨h1, fun hf => ?_⟩
  rw [if_neg (by rw [hf]; simp)] at h2
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  exact h2

private theorem ede_far_facts (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = false)
    (hf : farB D.QA (fd (D.P m) 26 16383) = true) :
    fd (D.P m) 26 16383 < 14080 ∧ fd (D.P m) 64 1023 < 648 ∧
      ent D.ml (fd (D.P m) 64 1023) = fd (D.P m) 40 4095 ∧
      (∀ t < fd (D.P m) 64 1023, popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
        (D.G (fld(D.mq, 10 * ent D.ml t, 1023)))) ≠ 63) ∧
      popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
        (D.G (fld(D.mq, 10 * fd (D.P m) 40 4095, 1023)))) = 63 ∧
      edgeK D.R D.Z (rowSet D.P D.QA (fd (D.P m) 40 4095))
        (D.G (fld(D.mq, 10 * fd (D.P m) 40 4095, 1023)))
        (sb (D.QA (fd (D.P m) 26 16383))) (fd (D.P m) 52 4095) = true := by
  have hk := ced_edK hm h
  unfold edK at hk
  simp only [strictB_eq, bAnd_eq, memB_eq, Nat.blt_eq, Nat.beq_eq] at hk
  simp only [bIf_eq] at hk
  rw [if_neg (by rw [hb]; simp)] at hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hk
  obtain ⟨h1, -, h2⟩ := hk
  rw [if_pos hf] at h2
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h2
  obtain ⟨hi, hg, hpre, hpos, hedge⟩ := h2
  refine ⟨h1, hi, hg, ?_, hpos, hedge⟩
  intro t ht
  have hz : Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
      (D.G (fld(D.mq, 10 * ent D.ml t, 1023))))) 63 = false := by
    have h := allN_iff.1 hpre t ht
    rwa [notB_eq, Bool.not_eq_true'] at h
  intro h
  rw [h, beq_true rfl] at hz
  simp at hz

private noncomputable def edeMM (D : LHData) : List Nat :=
  (List.range 3510).filter fun f => decide (fd (D.P f) 14 4095 < 3510)

private noncomputable def edePred (D : LHData) (e f : Nat) : Bool :=
  andPop (bitsOfNat (sb (D.QA (fd (D.P f) 0 16383)))) (bitsOfNat (sb (D.QA e))) == 63 &&
    decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
      (bitsOfNat (sb (D.QA (fd (D.P f) 0 16383)))) (bitsOfNat (sb (D.QA e))) < 3510)

private theorem ede_pred_eq (D : LHData) (e f : Nat) :
    edePred D e f = (andPop (bitsOfNat (sb (rowSet D.P D.QA f))) (bitsOfNat (sb (D.QA e))) == 63 &&
      decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
        (bitsOfNat (sb (rowSet D.P D.QA f))) (bitsOfNat (sb (D.QA e))) < 3510)) := rfl

private theorem ede_G_eq (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hP : fd (D.P f) 14 4095 < 3510) :
    D.G (fld(D.mq, 10 * f, 1023)) = sb (rowSet D.P D.QA f) := by
  obtain ⟨hPk, -, hP2, hall⟩ := ced_muTree_spec h
  have hp := hall f hf hP
  rcases hP2 f hf with e | ⟨-, hpts⟩
  · omega
  · have hk := (hPk (fld(D.mq, 10 * f, 1023)) hp).2
    rw [hpts] at hk
    exact hk

private theorem ede_set_get (h : LHChecks D) {f : Nat} (hf : f < 3510)
    (hP : fd (D.P f) 14 4095 < 3510) :
    (orbDec D.QA).sets[(rowRD D)[f]!]! = bitsOfNat (sb (rowSet D.P D.QA f)) := by
  have hk : fd (D.P f) 0 16383 < 14080 := by
    have h' := ede_rowR_lt h hf hP
    rw [rowR_get hf] at h'
    exact h'
  have h1 : (orbDec D.QA).sets[fd (D.P f) 0 16383]! =
      bitsOfNat (sb (D.QA (fd (D.P f) 0 16383))) :=
    orbDec_sets (Q := D.QA) hk
  rw [rowR_get hf]
  exact h1

private theorem ede_find_far (hO : OrbOK) (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = false)
    (hf : farB D.QA (fd (D.P m) 26 16383) = true) :
    (edeMM D).find? (edePred D (fd (D.P m) 26 16383)) = some (fd (D.P m) 40 4095) ∧
      edgeWit (tauAll orbL) (commBits (tauAll orbL))
        (bitsOfNat (sb (rowSet D.P D.QA (fd (D.P m) 40 4095))))
        (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) = fd (D.P m) 52 4095 := by
  obtain ⟨h1, hi, hg, hpre, hpos, hedge⟩ := ede_far_facts h hm hb hf
  have hglt : fd (D.P m) 40 4095 < 3510 := by rw [← hg]; exact (ced_ml_facts h).2.2.1 _ hi
  have hPg : fd (D.P (fd (D.P m) 40 4095)) 14 4095 < 3510 := by
    rw [← hg]; exact ede_ml_inS h hi
  have hGg := ede_G_eq h hglt hPg
  have hpos' : andPop (bitsOfNat (sb (D.QA (fd (D.P (fd (D.P m) 40 4095)) 0 16383))))
      (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) = 63 := by
    rw [muw_andPop_bitsOfNat (sb_lt _) (by decide), ede_land_comm]
    change popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
      (sb (rowSet D.P D.QA (fd (D.P m) 40 4095)))) = 63
    rw [← hGg]
    exact hpos
  have hmm : fd (D.P (fd (D.P m) 40 4095)) 0 16383 < 14080 := by
    have h' := ede_rowR_lt h hglt hPg
    rw [rowR_get hglt] at h'
    exact h'
  have hedge' := edgeWit_eq_of_edgeK hO h (m := fd (D.P (fd (D.P m) 40 4095)) 0 16383)
    (m' := fd (D.P m) 26 16383) (w := fd (D.P m) 52 4095) hmm h1
    (by
      change edgeK D.R D.Z (rowSet D.P D.QA (fd (D.P m) 40 4095))
        (sb (rowSet D.P D.QA (fd (D.P m) 40 4095)))
        (sb (D.QA (fd (D.P m) 26 16383))) (fd (D.P m) 52 4095) = true
      rw [← hGg]
      exact hedge)
  have hpk : edePred D (fd (D.P m) 26 16383) (fd (D.P m) 40 4095) = true := by
    change (andPop (bitsOfNat (sb (D.QA (fd (D.P (fd (D.P m) 40 4095)) 0 16383))))
      (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) == 63 &&
      decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
        (bitsOfNat (sb (D.QA (fd (D.P (fd (D.P m) 40 4095)) 0 16383))))
        (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) < 3510)) = true
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨hpos', ?_⟩
    rw [hedge'.2.2]
    exact hedge'.1
  have hpre' : ∀ t < fd (D.P m) 40 4095,
      decide (fd (D.P t) 14 4095 < 3510) = true →
      edePred D (fd (D.P m) 26 16383) t = false := by
    intro t ht hPt
    have ht3510 : t < 3510 := by omega
    have hPt' : fd (D.P t) 14 4095 < 3510 := of_decide_eq_true hPt
    obtain ⟨s', hs', hts⟩ := ede_ml_lt_enum h ht3510 hPt' (by rw [hg]; exact ht)
    have hz : Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
        (D.G (fld(D.mq, 10 * ent D.ml s', 1023))))) 63 = false :=
      beq_false (hpre s' hs')
    have hGt : D.G (fld(D.mq, 10 * ent D.ml s', 1023)) = sb (rowSet D.P D.QA t) := by
      rw [hts]
      exact ede_G_eq h ht3510 hPt'
    change (andPop (bitsOfNat (sb (D.QA (fd (D.P t) 0 16383))))
      (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) == 63 &&
      decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
        (bitsOfNat (sb (D.QA (fd (D.P t) 0 16383))))
        (bitsOfNat (sb (D.QA (fd (D.P m) 26 16383)))) < 3510)) = false
    rw [Bool.and_eq_false_iff]
    left
    rw [muw_andPop_bitsOfNat (sb_lt _) (by decide), ede_land_comm]
    change Nat.beq (popK masks (Nat.land (sb (D.QA (fd (D.P m) 26 16383)))
      (sb (rowSet D.P D.QA t)))) 63 = false
    rw [← hGt]
    exact hz
  have hfind := ede_find?_filter_range (P := fun f => decide (fd (D.P f) 14 4095 < 3510))
    (p := edePred D (fd (D.P m) 26 16383)) (N := 3510) (k := fd (D.P m) 40 4095)
    hglt (decide_eq_true hPg) hpk hpre'
  refine ⟨?_, hedge'.2.2⟩
  simpa only [edeMM] using hfind

private theorem ede_cond_split {q : Nat} (hq : q < 3510)
    (hcond : (!bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) q &&
      decide ((edWD D)[q]! < 14080) && isFar (rowInvD D) ((edWD D)[q]!)) = true) :
    bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) q = false ∧
      fd (D.P q) 26 16383 < 14080 ∧ farB D.QA (fd (D.P q) 26 16383) = true := by
  have h1 : bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) q = false := by
    rw [Bool.eq_false_iff]
    intro hb
    rw [hb] at hcond
    simpa using hcond
  have h2 : decide ((edWD D)[q]! < 14080) = true := by
    have h := hcond
    rw [h1, Bool.not_false, Bool.true_and, Bool.and_eq_true] at h
    exact h.1
  have h3 : isFar (rowInvD D) ((edWD D)[q]!) = true := by
    have h := hcond
    rw [h1, Bool.not_false, Bool.true_and, Bool.and_eq_true] at h
    exact h.2
  have he : fd (D.P q) 26 16383 < 14080 := by
    rw [ced_edWD_get hq] at h2
    exact of_decide_eq_true h2
  refine ⟨h1, he, ?_⟩
  rw [ced_edWD_get hq] at h3
  rwa [isFar_eq he] at h3

private theorem ede_find_lit (hO : OrbOK) (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = false)
    (hf : farB D.QA (fd (D.P m) 26 16383) = true) :
    List.find? (fun f => andPop ((orbDec D.QA).sets[(rowRD D)[f]!]!)
        ((orbDec D.QA).sets[(edWD D)[m]!]!) == 63 &&
          decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
            ((orbDec D.QA).sets[(rowRD D)[f]!]!) ((orbDec D.QA).sets[(edWD D)[m]!]!) < 3510))
      (edeMM D) = some (fd (D.P m) 40 4095) ∧
      edgeWit (tauAll orbL) (commBits (tauAll orbL))
        ((orbDec D.QA).sets[(rowRD D)[fd (D.P m) 40 4095]!]!)
        ((orbDec D.QA).sets[(edWD D)[m]!]!) = fd (D.P m) 52 4095 := by
  have he : fd (D.P m) 26 16383 < 14080 := (ede_nonfar_facts h hm hb).1
  obtain ⟨-, hi, hg, -⟩ := ede_far_facts h hm hb hf
  have hglt : fd (D.P m) 40 4095 < 3510 := by rw [← hg]; exact (ced_ml_facts h).2.2.1 _ hi
  have hPg : fd (D.P (fd (D.P m) 40 4095)) 14 4095 < 3510 := by
    rw [← hg]; exact ede_ml_inS h hi
  obtain ⟨hfind, hedge⟩ := ede_find_far hO h hm hb hf
  have hcongr : List.find? (fun f => andPop ((orbDec D.QA).sets[(rowRD D)[f]!]!)
      ((orbDec D.QA).sets[(edWD D)[m]!]!) == 63 &&
        decide (edgeWit (tauAll orbL) (commBits (tauAll orbL))
          ((orbDec D.QA).sets[(rowRD D)[f]!]!) ((orbDec D.QA).sets[(edWD D)[m]!]!) < 3510))
      (edeMM D) = (edeMM D).find? (edePred D (fd (D.P m) 26 16383)) := by
    refine List.find?_congr fun f hf' => ?_
    dsimp only [edeMM] at hf'
    rw [List.mem_filter] at hf'
    have hf3510 : f < 3510 := List.mem_range.1 hf'.1
    have hPf : fd (D.P f) 14 4095 < 3510 := of_decide_eq_true hf'.2
    rw [ede_set_get h hf3510 hPf, ced_edWD_get hm,
      orbDec_sets (Q := D.QA) (k := fd (D.P m) 26 16383) he, ede_pred_eq]
  refine ⟨?_, ?_⟩
  · rw [hcongr]
    exact hfind
  · rw [ede_set_get h hglt hPg, ced_edWD_get hm,
      orbDec_sets (Q := D.QA) (k := fd (D.P m) 26 16383) he]
    exact hedge

private noncomputable def edeVBits (D : LHData) : Bits := (orbDec D.QA).sets[fd D.mt 0 16383]!

private noncomputable def edeC (D : LHData) : Nat → Bool := fun q =>
  !bitAt (edeVBits D) q && decide ((edWD D)[q]! < 14080) && isFar (rowInvD D) ((edWD D)[q]!)

private noncomputable def edeG (D : LHData) : Nat → Nat := fun q => fd (D.P q) 40 4095

private noncomputable def edeK (D : LHData) : Nat → Nat := fun q => fd (D.P q) 52 4095

private theorem ede_nonmem_val (h : LHChecks D) {m : Nat} (hm : m < 3510)
    (hb : (sb (D.QA (fd D.mt 0 16383))).testBit m = false) (hc : edeC D m = false) :
    fd (D.P m) 40 4095 = 3510 ∧ fd (D.P m) 52 4095 = 3510 := by
  have hV : bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) m = false := by
    rw [ede_bitAt_V h hm]
    exact hb
  obtain ⟨he, hnf⟩ := ede_nonfar_facts h hm hb
  refine hnf ?_
  rw [← isFar_eq he, Bool.eq_false_iff]
  intro his
  have hcm : edeC D m = true := by
    dsimp only [edeC, edeVBits]
    rw [hV, ced_edWD_get hm, decide_eq_true he, his]
    rfl
  rw [hcm] at hc
  exact Bool.noConfusion hc

private theorem ede_val (h : LHChecks D) {m : Nat} (hm : m < 3510) :
    (if edeC D m then edeG D m else 3510) = fd (D.P m) 40 4095 ∧
      (if edeC D m then edeK D m else 3510) = fd (D.P m) 52 4095 := by
  cases hc : edeC D m with
  | true => exact ⟨if_pos rfl, if_pos rfl⟩
  | false =>
    rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
    cases hb : (sb (D.QA (fd D.mt 0 16383))).testBit m with
    | true =>
      obtain ⟨-, h2, h3⟩ := ede_mem_facts h hm hb
      exact ⟨h2.symm, h3.symm⟩
    | false =>
      obtain ⟨h2, h3⟩ := ede_nonmem_val h hm hb hc
      exact ⟨h2.symm, h3.symm⟩

private noncomputable def edeInv (D : LHData) (q : Nat) (s : Array Nat × Array Nat) : Prop :=
  s.1.size = 3510 ∧ s.2.size = 3510 ∧
    (∀ m < 3510, s.1[m]! = if m < q then (if edeC D m then edeG D m else 3510) else 3510) ∧
    ∀ m < 3510, s.2[m]! = if m < q then (if edeC D m then edeK D m else 3510) else 3510

private theorem ede_set_entry {q m : Nat} {c : Nat → Bool} {f : Nat → Nat} {d : Nat}
    (b : Array Nat) (hc : c q = true)
    (h3 : b[m]! = if m < q then (if c m then f m else d) else d) :
    (if q = m then f q else b[m]!) =
      (if m < q + 1 then (if c m then f m else d) else d) := by
  rcases Nat.lt_trichotomy m q with hlt | heq | hgt
  · rw [if_neg (by omega), h3, if_pos hlt, if_pos (show m < q + 1 by omega)]
  · subst heq
    rw [if_pos rfl, if_pos (show m < m + 1 by omega), if_pos hc]
  · rw [if_neg (by omega), h3, if_neg (by omega), if_neg (show ¬m < q + 1 by omega)]

private theorem ede_skip_entry {q m d : Nat} {c : Nat → Bool} {f : Nat → Nat}
    (hc : c q = false) :
    (if m < q then (if c m then f m else d) else d) =
      (if m < q + 1 then (if c m then f m else d) else d) := by
  rcases Nat.lt_trichotomy m q with hlt | heq | hgt
  · rw [if_pos hlt, if_pos (show m < q + 1 by omega)]
  · rw [if_neg (show ¬m < q by omega), if_pos (show m < q + 1 by omega), heq, hc,
      if_neg Bool.false_ne_true]
  · rw [if_neg (by omega), if_neg (show ¬m < q + 1 by omega)]

private theorem ede_inv_zero :
    edeInv D 0 (Array.replicate 3510 3510, Array.replicate 3510 3510) := by
  refine ⟨by rw [Array.size_replicate], by rw [Array.size_replicate], fun m hm => ?_,
    fun m hm => ?_⟩
  · rw [getElem!_pos _ m (by simpa using hm), Array.getElem_replicate]
    simp
  · rw [getElem!_pos _ m (by simpa using hm), Array.getElem_replicate]
    simp

private theorem ede_inv_set {q : Nat} {s : Array Nat × Array Nat} (hq : q < 3510)
    (hI : edeInv D q s) (hc : edeC D q = true) :
    edeInv D (q + 1) (s.1.set! q (edeG D q), s.2.set! q (edeK D q)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  refine ⟨by rw [size_set!, h1], by rw [size_set!, h2], fun m hm => ?_, fun m hm => ?_⟩
  · rw [get!_set! _ (by rw [h1]; omega) (by rw [h1]; exact hm)]
    exact ede_set_entry s.1 hc (h3 m hm)
  · rw [get!_set! _ (by rw [h2]; omega) (by rw [h2]; exact hm)]
    exact ede_set_entry s.2 hc (h4 m hm)

private theorem ede_inv_skip {q : Nat} {s : Array Nat × Array Nat} (hI : edeInv D q s)
    (hc : edeC D q = false) : edeInv D (q + 1) s := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  refine ⟨h1, h2, fun m hm => ?_, fun m hm => ?_⟩
  · rw [h3 m hm]
    exact ede_skip_entry hc
  · rw [h4 m hm]
    exact ede_skip_entry hc

private theorem run_bind_forIn_pair {α β : Type} (n : Nat) (b : α × β)
    (f : Nat → α × β → Id (ForInStep (α × β))) :
    Id.run (forIn [:n] b f >>= fun s => pure (s.1, s.2)) = forIn [:n] b f := rfl

theorem ed_eq (hO : OrbOK) (h : LHChecks D) :
    mkEd (tauAll orbL) (commBits (tauAll orbL)) (orbDec D.QA) (rowRD D) (rowInvD D) (muWD D)
      (edWD D) (fd D.mt 0 16383) =
      (Array.ofFn (n := 3510) fun f => fd (D.P f.val) 40 4095,
        Array.ofFn (n := 3510) fun f => fd (D.P f.val) 52 4095) := by
  have hM : List.filter (fun f => decide ((muWD D)[f]! < 3510)) (List.range 3510) = edeMM D := by
    unfold edeMM
    refine List.filter_congr fun f hf => ?_
    rw [muw_muWD_get (List.mem_range.1 hf)]
  unfold mkEd
  rw [hM]
  dsimp only
  rw [run_bind_forIn_pair]
  refine range_loop (I := edeInv D)
    (Q := fun s => s = (Array.ofFn (n := 3510) fun f => fd (D.P f.val) 40 4095,
      Array.ofFn (n := 3510) fun f => fd (D.P f.val) 52 4095)) _ 3510 _ ?_ ?_ ?_
  · intro q s hq hI
    by_cases hcond : (!bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) q &&
        decide ((edWD D)[q]! < 14080) && isFar (rowInvD D) ((edWD D)[q]!)) = true
    · obtain ⟨h1, -, hfar⟩ := ede_cond_split hq hcond
      obtain ⟨hfind, hedge⟩ :=
        ede_find_lit hO h hq ((ede_bitAt_V h hq).symm.trans h1) hfar
      rw [if_pos hcond]
      simp only [hfind]
      rw [hedge]
      exact ede_inv_set hq hI hcond
    · rw [if_neg hcond]
      exact ede_inv_skip hI (Bool.eq_false_iff.2 hcond)
  · intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hs
    refine Prod.ext (ext_get! h1 (by rw [Array.size_ofFn]) fun m hm => ?_)
      (ext_get! h2 (by rw [Array.size_ofFn]) fun m hm => ?_)
    · rw [h3 m hm, if_pos hm, getElem!_pos _ m (by rw [Array.size_ofFn]; exact hm),
        Array.getElem_ofFn]
      exact (ede_val h hm).1
    · rw [h4 m hm, if_pos hm, getElem!_pos _ m (by rw [Array.size_ofFn]; exact hm),
        Array.getElem_ofFn]
      exact (ede_val h hm).2
  · exact ede_inv_zero

theorem c_mu (hO : OrbOK) (h : LHChecks D) :
    muOK (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) (rowRD D) (muWD D)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 0 4095)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 12 1023)
      (Array.ofFn (n := fd D.mt 70 1023) fun k => fd (D.M k.val) 22 4095) (fd D.mt 0 16383) =
        true :=
  c_mu_of hO h

private theorem ced_edF_get {f : Nat} (hf : f < 3510) :
    (Array.ofFn (n := 3510) fun k => fd (D.P k.val) 40 4095)[f]! = fd (D.P f) 40 4095 := by
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem ced_edK_get {f : Nat} (hf : f < 3510) :
    (Array.ofFn (n := 3510) fun k => fd (D.P k.val) 52 4095)[f]! = fd (D.P f) 52 4095 := by
  rw [getElem!_pos _ f (by rw [Array.size_ofFn]; exact hf), Array.getElem_ofFn]

private theorem ced_mapsOnto (hO : OrbOK) (hchk : LHChecks D) {f e : Nat} (hf : f < 3510)
    (he : e < 14080)
    (hsub : ∀ j < 351, memB (sb (D.QA e))
      (ent (D.R f) (ent (D.QA (fd D.mt 0 16383)) j)) = true) :
    mapsOnto (tauAll orbL)[f]! (bitsOfNat (sb (D.QA (fd D.mt 0 16383))))
      (bitsOfNat (sb (D.QA e))) = true := by
  obtain ⟨hv0, -⟩ := farK_spec hchk
  have hs := hchk.setA
  have hent := ent_inj_of_setSl hs hv0
  have hf' : ∀ x < 3510, ∀ y < 3510, ent (D.R f) x = ent (D.R f) y → x = y :=
    fun x hx y hy e => row_inj hO hchk hf hx hy e
  have hiff : ∀ x < 3510, (sb (D.QA e)).testBit (ent (D.R f) x) = true ↔
      (sb (D.QA (fd D.mt 0 16383))).testBit x = true := by
    intro x hx
    have key := img_eq_of_sub (g := fun j => ent (D.R f) (ent (D.QA (fd D.mt 0 16383)) j))
      (e := fun j => ent (D.QA e) j)
      (fun i hi j hj e => hent i hi j hj (hf' _ (mem_lt hs hv0 hi) _ (mem_lt hs hv0 hj) e))
      (fun j hj => by
        have hj' := hsub j hj
        rw [memB_eq] at hj'
        exact (sb_mem hs he _).1 hj')
      (ent (D.R f) x)
    rw [sb_mem hs he, key, sb_mem hs hv0]
    constructor
    · rintro ⟨j, hj, hje⟩
      exact ⟨j, hj, hf' _ (mem_lt hs hv0 hj) _ hx hje⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  refine mapsOnto_of (bitsIs_bitsOfNat _) (bitsIs_bitsOfNat _) (fun x hx => ?_) fun x hx => ?_
  · rw [((tauAll_TR hO hchk f hf).2 x hx).1]
    exact row_lt hO hchk hf hx
  · rw [((tauAll_TR hO hchk f hf).2 x hx).1]
    exact hiff x hx

private theorem ced_edgeK_notB {R Z : Nat → Nat} {q bA bB w : Nat}
    (he : edgeK R Z q bA bB w = true) : memB bA w = false := by
  unfold edgeK at he
  rw [bAnd_eq, Bool.and_eq_true] at he
  obtain ⟨hmin, -⟩ := he
  unfold minWitK at hmin
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true] at hmin
  have hnot : notB (memB bA w) = true := hmin.2.2.1
  rwa [notB_eq, Bool.not_eq_true'] at hnot

private theorem ced_far_conj (hO : OrbOK) (hchk : LHChecks D) {e g w i : Nat} (he : e < 14080)
    (hi : i < 648) (hmlg : ent D.ml i = g)
    (hedge : edgeK D.R D.Z (rowSet D.P D.QA g) (D.G (fld(D.mq, 10 * g, 1023)))
      (sb (D.QA e)) w = true) :
    g < 3510 ∧ bitAt (bitsOf (lhData ())[0]!) g = false ∧
      fd (D.P g) 14 4095 < 3510 ∧ w < 3510 ∧
      bitAt ((orbDec D.QA).sets[(rowRD D)[g]!]!) w = false ∧
      mapsOnto (tauAll orbL)[w]! ((orbDec D.QA).sets[(rowRD D)[g]!]!)
        ((orbDec D.QA).sets[e]!) = true := by
  obtain ⟨-, -, hentlt, hpos⟩ := ced_ml_facts hchk
  have hg : g < 3510 := by
    rw [← hmlg]
    exact hentlt i hi
  have hposg : fld(D.mq, 10 * g, 1023) < 648 := by
    rw [← hmlg]
    exact hpos i hi
  obtain ⟨hG, -, hposM, -⟩ := ced_muTree_spec hchk
  have hMg : fd (D.M (fld(D.mq, 10 * g, 1023))) 0 4095 = g := by
    rcases hposM g hg with e | ⟨-, e⟩
    · omega
    · exact e
  have hGg := hG (fld(D.mq, 10 * g, 1023)) hposg
  rw [hMg] at hGg
  have hroot : (bs D.lb0).testBit g = false := by
    rw [Bool.eq_false_iff]
    intro hb
    have h3510 := ced_root_muW hchk hg hb
    omega
  obtain ⟨hrowR, -, -, -, -⟩ := (rowF_spec hchk hg).2 hroot
  have hq : rowSet D.P D.QA g = D.QA (fd (D.P g) 0 16383) := rfl
  rw [hGg.2, hq] at hedge
  obtain ⟨hw, hmaps, -⟩ := edgeWit_eq_of_edgeK hO hchk hrowR he hedge
  have hnot := ced_edgeK_notB hedge
  have hB0 : bitAt (bitsOf (lhData ())[0]!) g = false := by
    rw [B0_at hchk hg, hroot]
  have hout : bitAt ((orbDec D.QA).sets[(rowRD D)[g]!]!) w = false := by
    rw [rowR_get hg, orbDec_sets _ hrowR]
    have hbit : bitAt (bitsOfNat (sb (D.QA (fd (D.P g) 0 16383)))) w =
        memB (sb (D.QA (fd (D.P g) 0 16383))) w := by
      rw [memB_eq, Bool.eq_iff_iff]
      exact (bitsIs_bitsOfNat _).2 w (by omega)
    rw [hbit, hnot]
  have hmaps' : mapsOnto (tauAll orbL)[w]! ((orbDec D.QA).sets[(rowRD D)[g]!]!)
      ((orbDec D.QA).sets[e]!) = true := by
    rw [rowR_get hg, orbDec_sets _ hrowR, orbDec_sets _ he]
    exact hmaps
  exact ⟨hg, hB0, hGg.1, hw, hout, hmaps'⟩

theorem c_ed (hO : OrbOK) (h : LHChecks D) :
    edOK (tauAll orbL) (bitsOf (lhData ())[0]!) (orbDec D.QA) (rowRD D) (rowInvD D) (muWD D)
      (edWD D) (Array.ofFn (n := 3510) fun f => fd (D.P f.val) 40 4095)
      (Array.ofFn (n := 3510) fun f => fd (D.P f.val) 52 4095) (fd D.mt 0 16383) = true := by
  obtain ⟨hv0, -⟩ := farK_spec h
  have hV : (orbDec D.QA).sets[fd D.mt 0 16383]! =
      bitsOfNat (sb (D.QA (fd D.mt 0 16383))) := orbDec_sets _ hv0
  unfold edOK
  rw [allIn_iff]
  intro f hf
  have hbitV : bitAt ((orbDec D.QA).sets[fd D.mt 0 16383]!) f =
      memB (sb (D.QA (fd D.mt 0 16383))) f := by
    rw [hV, memB_eq, Bool.eq_iff_iff]
    exact (bitsIs_bitsOfNat _).2 f (by omega)
  cases hm : memB (sb (D.QA (fd D.mt 0 16383))) f with
  | true => rw [hbitV, hm]; rfl
  | false =>
    have hed := ced_edK hf h
    unfold edK at hed
    simp only [strictB_eq] at hed
    rw [bIf_eq] at hed
    rw [if_neg (by rw [hm]; simp)] at hed
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hed
    obtain ⟨he_lt, hsub, hfar_branch⟩ := hed
    have hmap : mapsOnto (tauAll orbL)[f]! ((orbDec D.QA).sets[fd D.mt 0 16383]!)
        ((orbDec D.QA).sets[fd (D.P f) 26 16383]!) = true := by
      rw [hV, orbDec_sets _ he_lt]
      exact ced_mapsOnto hO h hf he_lt (fun j hj => allN_iff.1 hsub j hj)
    have hWlt : fd (D.P f) 26 16383 < 14080 := he_lt
    rw [ced_edWD_get hf]
    simp only [hbitV, hm, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hWlt, hmap⟩, ?_⟩
    by_cases hfar : isFar (rowInvD D) (fd (D.P f) 26 16383) = true
    · have hfarB : farB D.QA (fd (D.P f) 26 16383) = true := by
        rw [← isFar_eq he_lt]
        exact hfar
      simp only [hfar, Bool.not_true, Bool.false_or]
      rw [bIf_eq] at hfar_branch
      rw [if_pos (by rw [hfarB])] at hfar_branch
      simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hfar_branch
      obtain ⟨hi, hmlg, -, -, hedge⟩ := hfar_branch
      have hconj := ced_far_conj hO h he_lt hi hmlg hedge
      rw [ced_edF_get hf, ced_edK_get hf, muw_muWD_get hconj.1]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · exact hconj.1
      · simpa using hconj.2.1
      · exact hconj.2.2.1
      · exact hconj.2.2.2.1
      · simpa using hconj.2.2.2.2.1
      · exact hconj.2.2.2.2.2
    · have hfar' : isFar (rowInvD D) (fd (D.P f) 26 16383) = false :=
        Bool.eq_false_iff.2 hfar
      rw [hfar']
      simp

end CFSG.KS.Fi22LH
