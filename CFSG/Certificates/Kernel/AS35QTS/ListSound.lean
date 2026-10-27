module

public import CFSG.Certificates.Kernel.AS35QTS.CenterSound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 isInv codes il sl sq)

@[expose] def dcG (G : List Nat) (c : Nat) : Cd := decN (2 ^ 18 * (c / 648) + G.getD (c % 648) 0)

theorem lenR_eq : ∀ L : List Nat, lenR L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lenR_eq L)

@[expose] def bOpsT (b : Bool) : Ops Bool := ⟨and, xor, b, fun y k => k y⟩

theorem eqP_laneT (t c : Nat) (X Y : PL Nat) :
    (eqP (natOps t) X Y).testBit c = eqP (bOpsT (t.testBit c)) (laneOf c X) (laneOf c Y) := by
  simp only [eqP, eqV, isEq, bnot, laneOf, mapP, natOps, bOpsT, tb_land, tb_xor]

theorem eqP_beq (x y : Cd) : eqP bOps (ofCd x) (ofCd y) = (x == y) := by
  rw [Bool.eq_iff_iff, eqP_e, beq_iff_eq]

theorem isI3_lane {t c : Nat} (ht : t.testBit c = true) (X : PL Nat) :
    (isI3 (natOps t) X).testBit c = isI3 bOps (laneOf c X) := by
  simp only [isI3, isOne, isZero, bnot, laneOf, mapP, natOps, bOps, tb_land, tb_xor, ht]

theorem isI3_beq (x : Cd) : isI3 bOps (ofCd x) = (x.m == I3) := by
  rw [Bool.eq_iff_iff, isI3_e, beq_iff_eq]

theorem invM_lane {t c : Nat} (ht : t.testBit c = true) (X XX : PL Nat) :
    (invM t X XX).testBit c = (eqP bOps (laneOf c XX) (laneOf c (cst t ixE)) &&
      !(eqP bOps (laneOf c X) (laneOf c (cst t ixE)))) := by
  unfold invM
  rw [tb_land, bnot_natOps, tb_xor, eqP_lane ht, eqP_lane ht, ht, Bool.xor_true]

theorem mulbit_tb (p s t c : Nat) :
    (Nat.mul (bitN p s) t).testBit c = (p.testBit s && t.testBit c) := by
  have := bitN_lt p s
  rw [← bitN_testBit p s]
  interval_cases h : bitN p s
  · simp [Nat.mul_eq]
  · simp [Nat.mul_eq]

theorem lane_atLane {t c : Nat} (ht : t.testBit c = true) (X : PL Nat) (s : Nat) :
    laneOf c (atLane t X s) = laneOf s X := by
  simp only [laneOf, mapP, atLane, mulbit_tb, ht, Bool.and_true]

@[expose] def zPL : PL Bool := ofIx fun _ => false

theorem lane_atLane_f {t c : Nat} (ht : t.testBit c = false) (X : PL Nat) (s : Nat) :
    laneOf c (atLane t X s) = zPL := by
  simp only [laneOf, mapP, atLane, mulbit_tb, ht, Bool.and_false, zPL, ofIx]

set_option exponentiation.threshold 700 in
theorem lanePl_high {G : List Nat} (hG : G.length = 648) (b c : Nat) (hc : 82944 ≤ c) :
    (lanePl G b).testBit c = false := by
  have hc' : ¬ c < 648 * 128 := by omega
  unfold lanePl
  cases Nat.blt b 18
  · change (blk 648 (fun i => Nat.mul (bitN i (Nat.sub b 18)) (Nat.sub (Nat.pow 2 648) 1))
      128).testBit c = false
    rw [blkMask_testBit (by norm_num)]
    simp [hc']
  · change (blk 648 (fun _ => colB b G) 128).testBit c = false
    rw [blk_testBit (by norm_num) (fun _ _ => by rw [← hG]; exact colB_lt b G) c]
    simp [hc']

theorem lane_high {G : List Nat} (hG : G.length = 648) {c : Nat} (hc : 82944 ≤ c) :
    laneOf c (ofIx (lanePl G)) = zPL := by
  simp only [laneOf, mapP, ofIx, lanePl_high hG _ c hc, zPL]

theorem allT_high {c : Nat} (hc : 82944 ≤ c) : allT.testBit c = false := by
  unfold allT
  generalize hm : (82944 : Nat) = m at hc ⊢
  rw [allOnes_testBit m c]
  exact decide_eq_false (by omega)

theorem tb_zero {P : Nat} (h : Nat.beq P 0 = true) (c : Nat) : P.testBit c = false := by
  rw [Nat.eq_of_beq_eq_true h, Nat.zero_testBit]

theorem isInv_eq (c : Cd) : isInv c = (mulC c c == e0 && !(c == e0)) := rfl

theorem bor_tb (t p q c : Nat) : (bor (natOps t) p q).testBit c = (p.testBit c || q.testBit c) := by
  simp only [bor, natOps, tb_xor, tb_land]
  cases p.testBit c <;> cases q.testBit c <;> rfl

theorem anyEq_tb {t c : Nat} (X Q : PL Nat) : ∀ S : List Nat,
    (anyEq t X Q S).testBit c = S.any fun s => (eqP (natOps t) Q (atLane t X s)).testBit c
  | [] => by
    change Nat.testBit 0 c = _
    simp
  | s :: S => by
    change (bor (natOps t) (eqP (natOps t) Q (atLane t X s)) (anyEq t X Q S)).testBit c = _
    rw [bor_tb, anyEq_tb X Q S, List.any_cons]

theorem allHit_spec (t : Nat) (X Q : PL Nat) : ∀ S : List Nat, allHit t X Q S = true →
    ∀ s ∈ S, 0 < eqP (natOps t) Q (atLane t X s)
  | [], _ => by simp
  | s :: S, h => by
    change Bool.and' (Nat.blt 0 (eqP (natOps t) Q (atLane t X s))) (allHit t X Q S) = true at h
    rw [and'_eq, Bool.and_eq_true, Nat.blt_eq] at h
    intro s' hs'
    rcases List.mem_cons.1 hs' with rfl | hs'
    · exact h.1
    · exact allHit_spec t X Q S h.2 s' hs'

theorem decN_inj {n m : Nat} (hn : n < 2 ^ 25) (hm : m < 2 ^ 25) (h : decN n = decN m) :
    n = m := by
  have h' := congrArg ofCd h
  rw [ofCd_decN, ofCd_decN] at h'
  simp only [ofIx, PL.mk.injEq, V3T.mk.injEq] at h'
  obtain ⟨h24, ⟨h22, h23, h20, h21, h18, h19⟩, ⟨h16, h17, h14, h15, h12, h13⟩,
    ⟨h10, h11, h8, h9, h6, h7⟩, ⟨h4, h5, h2, h3, h0, h1⟩⟩ := h'
  refine Nat.eq_of_testBit_eq fun b => ?_
  by_cases hb : b < 25
  · interval_cases b <;> assumption
  · have h25 : (2 : Nat) ^ 25 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hn h25),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hm h25)]

section Lanes

variable {G : List Nat} (hg : gOK G = true)
include hg

theorem gb_of : ∀ g ∈ G, g < 2 ^ 18 := fun g hg' => by
  have := incB_lt (gOK_spec hg).1 g hg'
  omega

theorem gpw_of : G.Pairwise (· < ·) := (incB_go G 0 (gOK_spec hg).1).2

variable (hG : G.length = 648)
include hG

theorem codes_dc : codes = (List.range 82944).map (dcG G) :=
  codes_eq hG (gu3s_eq hg) (gb_of hg)

theorem lane_dc {c : Nat} (hc : c < 82944) : laneOf c (ofIx (lanePl G)) = ofCd (dcG G c) :=
  lane_lanes hG (gb_of hg) hc

theorem getD_G (k : Nat) (hk : k < 648) : G.getD k 0 = G[k]'(by omega) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : k < G.length),
    Option.getD_some]

theorem dc_inj {c d : Nat} (hc : c < 82944) (hd : d < 82944) (h : dcG G c = dcG G d) : c = d := by
  have hgc := getD_G hg hG (c % 648) (Nat.mod_lt _ (by norm_num))
  have hgd := getD_G hg hG (d % 648) (Nat.mod_lt _ (by norm_num))
  have bc : G[c % 648]'(by rw [hG]; exact Nat.mod_lt _ (by norm_num)) < 2 ^ 18 :=
    gb_of hg _ (List.getElem_mem _)
  have bd : G[d % 648]'(by rw [hG]; exact Nat.mod_lt _ (by norm_num)) < 2 ^ 18 :=
    gb_of hg _ (List.getElem_mem _)
  unfold dcG at h
  rw [hgc, hgd] at h
  have hi := decN_inj (by omega) (by omega) h
  have hq : c / 648 = d / 648 := by omega
  have hr : G[c % 648]'(by rw [hG]; exact Nat.mod_lt _ (by norm_num)) =
      G[d % 648]'(by rw [hG]; exact Nat.mod_lt _ (by norm_num)) := by omega
  have hm := (List.Nodup.getElem_inj_iff (List.Pairwise.imp (fun h => Nat.ne_of_lt h)
    (gpw_of hg))).1 hr
  omega

theorem codes_nodup : codes.Nodup := by
  rw [codes_dc hg hG]
  refine List.Nodup.map_on (fun c hc d hd h => ?_) List.nodup_range
  exact dc_inj hg hG (List.mem_range.1 hc) (List.mem_range.1 hd) h

theorem codes_filter (p : Cd → Bool) {L : List Nat} (hL : incB 82944 L = true)
    (hm : ∀ c < 82944, (p (dcG G c) = true ↔ c ∈ L)) : codes.filter p = L.map (dcG G) := by
  rw [codes_dc hg hG, List.filter_map]
  exact congrArg (List.map (dcG G)) (filter_range_eq (p ∘ dcG G) hL hm)

theorem invM_dc {c : Nat} (hc : c < 82944) :
    (invM allT (ofIx (lanePl G)) (mulD (natOps allT) (ofIx (lanePl G)) (ofIx (lanePl G)))).testBit
      c = isInv (dcG G c) := by
  have ht := allT_testBit hc
  have hX := lane_dc hg hG hc
  rw [invM_lane ht, lane_mulP _ _ hX hX, hX, lane_cst ht, decN_ixE, eqP_beq, eqP_beq]
  rfl

theorem il_eq {IL : List Nat} (h : ilOK G IL = true) : il = IL.map (dcG G) := by
  unfold ilOK at h
  rw [and'_eq, Bool.and_eq_true, frc_eqL, lanesK_eq, mulK_frc] at h
  obtain ⟨hinc, h2⟩ := h
  have he := Nat.eq_of_beq_eq_true h2
  refine codes_filter hg hG _ hinc fun c hc => ?_
  have hb := congrArg (fun p => Nat.testBit p c) he
  rw [invM_dc hg hG hc, ind_testBit] at hb
  rw [hb, decide_eq_true_iff]

theorem anyEq_dc {S : List Nat} (hS : ∀ s ∈ S, s < 82944) {d : Nat} (hd : d < 82944)
    {Q : PL Nat} {q : Cd} (hQ : laneOf d Q = ofCd q) :
    (anyEq allT (ofIx (lanePl G)) Q S).testBit d = decide (∃ s ∈ S, q = dcG G s) := by
  rw [anyEq_tb]
  have ht := allT_testBit hd
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [eqP_lane ht, hQ, lane_atLane ht, lane_dc hg hG (hS s hs), eqP_e] at h
    exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [eqP_lane ht, hQ, lane_atLane ht, lane_dc hg hG (hS s hs), eqP_e]
    exact h

theorem sl_eq {S : List Nat} (h : slOK G S = true) : sl = S.map (dcG G) := by
  unfold slOK at h
  rw [and'_eq, Bool.and_eq_true, frc_eqL, lanesK_eq] at h
  obtain ⟨hinc, h2⟩ := h
  simp only [mulK_frc, and'_eq, Bool.and_eq_true] at h2
  obtain ⟨ha, hh, hc⟩ := h2
  have hSb := incB_lt hinc
  have hA : ∀ c ∈ S, isInv (dcG G c) = true ∧ (dcG G c).m ≠ I3 := by
    intro c hcS
    have hc := hSb c hcS
    have ht := allT_testBit hc
    have hb := tb_zero ha c
    rw [tb_land, ind_testBit, decide_eq_true hcS, Bool.true_and, bnot_natOps, tb_xor, ht,
      tb_land, invM_dc hg hG hc, bnot_natOps, tb_xor, ht, isI3_lane ht, lane_dc hg hG hc,
      isI3_beq] at hb
    cases h1 : isInv (dcG G c) <;> cases h2 : ((dcG G c).m == I3) <;> rw [h1, h2] at hb <;>
      first
      | exact absurd hb (by decide)
      | exact ⟨rfl, by simpa using h2⟩
  have hB : ∀ s ∈ S, ∃ d < 82944, mulC (dcG G d) (dcG G d) = dcG G s := by
    intro s hsS
    have hs := hSb s hsS
    obtain ⟨d, hd⟩ := Nat.exists_testBit_of_ne_zero
      (Nat.pos_iff_ne_zero.1 (allHit_spec _ _ _ S hh s hsS))
    by_cases hdN : d < 82944
    · have ht := allT_testBit hdN
      rw [eqP_lane ht, lane_mulP _ _ (lane_dc hg hG hdN) (lane_dc hg hG hdN), lane_atLane ht,
        lane_dc hg hG hs] at hd
      exact ⟨d, hdN, (eqP_e _ _).1 hd⟩
    · have hdh : 82944 ≤ d := by omega
      rw [eqP_laneT, allT_high hdh, lane_mulD, lane_high hG hdh,
        lane_atLane_f (allT_high hdh)] at hd
      exact absurd hd (by decide)
  have hC : ∀ d < 82944, isInv (mulC (dcG G d) (dcG G d)) = true →
      (mulC (dcG G d) (dcG G d)).m ≠ I3 → ∃ s ∈ S, mulC (dcG G d) (dcG G d) = dcG G s := by
    intro d hd hi hm
    have ht := allT_testBit hd
    have hX := lane_dc hg hG hd
    have hQ := lane_mulP allT d hX hX
    have hQQ := lane_mulP allT d hQ hQ
    have hb := tb_zero hc d
    rw [tb_land, tb_land, invM_lane ht, bnot_natOps, tb_xor, ht, isI3_lane ht, bnot_natOps,
      tb_xor, ht, anyEq_dc hg hG hSb hd hQ, hQ, hQQ, lane_cst ht, decN_ixE, eqP_beq, eqP_beq,
      isI3_beq, ← isInv_eq, hi, beq_eq_false_iff_ne.2 hm] at hb
    by_contra hne
    rw [decide_eq_false hne] at hb
    exact absurd hb (by decide)
  have e : sl = codes.filter (fun c => (c.m != I3 && sq.contains c) && isInv c) := by
    change (codes.filter isInv).filter _ = _
    rw [List.filter_filter]
  rw [e]
  refine codes_filter hg hG _ hinc fun c hc => ?_
  rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨hm, hsq⟩, hi⟩
    change dcG G c ∈ codes.map (fun s => mulC s s) at hsq
    obtain ⟨y, hy, hyc⟩ := List.mem_map.1 hsq
    rw [codes_dc hg hG] at hy
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
    rw [← hyc] at hi hm
    obtain ⟨s, hs, hq⟩ := hC d (List.mem_range.1 hd) hi hm
    rw [hyc] at hq
    rw [dc_inj hg hG hc (hSb s hs) hq]
    exact hs
  · intro hcS
    obtain ⟨hi, hm⟩ := hA c hcS
    obtain ⟨d, hd, hdc⟩ := hB c hcS
    refine ⟨⟨hm, ?_⟩, hi⟩
    change dcG G c ∈ codes.map (fun s => mulC s s)
    rw [codes_dc hg hG, List.map_map]
    exact List.mem_map.2 ⟨d, List.mem_range.2 hd, hdc⟩

end Lanes

end CFSG.KC.AS35QTS

end
