module

public import CFSG.Certificates.Kernel.AS35QTS.PairSound
public import CFSG.Certificates.Kernel.AS35QTS.CountSound
public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 codes il sl t0c)

local notation "dlC" => CFSG.LargeExtraspecial.AS35QTS.dl

theorem anyComm_tb (t c : Nat) (X X' : PL Nat) : ∀ R : List Nat,
    (anyComm t X X' R).testBit c = R.any fun r => (commP t X (atLane t X' r)).testBit c
  | [] => by
    change Nat.testBit 0 c = _
    simp
  | r :: R => by
    change (Nat.lor (commP t X (atLane t X' r)) (anyComm t X X' R)).testBit c = _
    rw [tb_lor, anyComm_tb t c X X' R, List.any_cons]

theorem indINV_tb (c : Nat) : ∀ INV : List Nat,
    (List.rec (motive := fun _ => Nat) 0
      (fun w _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.land w (ones 17))) ih) INV).testBit c = true →
    ∃ w ∈ INV, Nat.land w (ones 17) = c
  | [], h => by
    change Nat.testBit 0 c = true at h
    simp at h
  | w :: INV, h => by
    change (Nat.lor (Nat.shiftLeft 1 (Nat.land w (ones 17))) (List.rec (motive := fun _ => Nat) 0
      (fun w _ ih => Nat.lor (Nat.shiftLeft 1 (Nat.land w (ones 17))) ih) INV)).testBit c =
        true at h
    rw [tb_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · refine ⟨w, List.mem_cons_self, ?_⟩
      change (1 <<< (w &&& ones 17)).testBit c = true at h
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h
      exact of_decide_eq_true h
    · obtain ⟨w', hw, he⟩ := indINV_tb c INV h
      exact ⟨w', List.mem_cons_of_mem _ hw, he⟩

theorem Dmask_tb (S : List Nat) (a : Nat) :
    (Nat.lor (Nat.shiftLeft 1 laneT) (ind S)).testBit a = decide (a ∈ laneT :: S) := by
  change ((1 <<< laneT) ||| ind S).testBit a = _
  rw [Nat.testBit_or, ind_testBit, Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : laneT = a
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem bitN_one {D a : Nat} (h : Nat.beq (bitN D a) 1 = true) : D.testBit a = true := by
  rw [← bitN_testBit, Nat.eq_of_beq_eq_true h]
  rfl

theorem laneT_lt : laneT < 82944 := by decide

section Lanes

variable {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
include hg hG

theorem lane1 {c : Nat} (hc : c < 82944) :
    laneOf 0 (atLane 1 (ofIx (lanePl G)) c) = ofCd (dcG G c) := by
  rw [lane_atLane one_tb0, lane_dc hg hG hc]

theorem laneT_dc {IL S INV : List Nat} (h : invOK G IL S INV = true) : dcG G laneT = tau0 := by
  unfold invOK at h
  simp only [and'_eq, Bool.and_eq_true, frc_eqL, lanesK_eq] at h
  have hb := beq_one_tb h.1
  rw [eqP_lane one_tb0, lane1 hg hG laneT_lt, lane_cst one_tb0, decN_ixT, eqP_e] at hb
  exact hb

theorem dl_eq {IL S INV : List Nat} (hs : slOK G S = true) (h : invOK G IL S INV = true) :
    dlC = (laneT :: S).map (dcG G) := by
  change tau0 :: sl = _
  rw [sl_eq hg hG hs, List.map_cons, laneT_dc hg hG h]

theorem incS {S : List Nat} (hs : slOK G S = true) : ∀ s ∈ S, s < 82944 := by
  unfold slOK at hs
  rw [and'_eq, Bool.and_eq_true] at hs
  exact incB_lt hs.1

theorem incD {S : List Nat} (hs : slOK G S = true) : ∀ s ∈ laneT :: S, s < 82944 := by
  intro s h
  rcases List.mem_cons.1 h with rfl | h
  · exact laneT_lt
  · exact incS hg hG hs s h

theorem incIL {IL : List Nat} (h : ilOK G IL = true) : ∀ s ∈ IL, s < 82944 := by
  unfold ilOK at h
  rw [and'_eq, Bool.and_eq_true] at h
  exact incB_lt h.1

theorem invOK_spec {IL S INV : List Nat} (hil : ilOK G IL = true) (hs : slOK G S = true)
    (h : invOK G IL S INV = true) :
    ∀ c ∈ il, c = tau0 ∨ c ∈ sl ∨
      ∃ a ∈ dlC, ∃ b ∈ dlC, a ≠ b ∧ mulC a b = mulC b a ∧ mulC a b = c := by
  have hD := incD hg hG hs
  have hdl := dl_eq hg hG hs h
  have hτ := laneT_dc hg hG h
  rw [il_eq hg hG hil, sl_eq hg hG hs]
  intro c hc
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
  have hlN := incIL hg hG hil l hl
  unfold invOK at h
  simp only [and'_eq, Bool.and_eq_true, frc_eqL, lanesK_eq] at h
  obtain ⟨-, hW, hZ⟩ := h
  have ht := allT_testBit hlN
  have hb := tb_zero hZ l
  rw [tb_land, ind_testBit, decide_eq_true hl, Bool.true_and, bnot_natOps, tb_xor, ht,
    Bool.xor_true, tb_lor, Dmask_tb, Bool.not_eq_false', Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · rcases List.mem_cons.1 (of_decide_eq_true hb) with rfl | hb
    · exact Or.inl hτ
    · exact Or.inr (Or.inl (List.mem_map_of_mem hb))
  · right
    right
    obtain ⟨w, hw, hwl⟩ := indINV_tb l INV hb
    obtain ⟨j, hj⟩ := allI_mem hW w hw
    simp only [and'_eq, Bool.and_eq_true] at hj
    obtain ⟨ha, hb', hne, hcomm, hprod⟩ := hj
    rw [hwl] at hprod
    have ha' := of_decide_eq_true ((Dmask_tb S _).symm.trans (bitN_one ha))
    have hb2 := of_decide_eq_true ((Dmask_tb S _).symm.trans (bitN_one hb'))
    refine ⟨_, hdl ▸ List.mem_map_of_mem ha', _, hdl ▸ List.mem_map_of_mem hb2, ?_, ?_, ?_⟩
    · intro e
      have := dc_inj hg hG (hD _ ha') (hD _ hb2) e
      rw [this, Nat.beq_refl] at hne
      exact absurd hne (by decide)
    · have h1 := beq_one_tb hcomm
      rw [commP_lane one_tb0, lane_mulP _ _ (lane1 hg hG (hD _ ha')) (lane1 hg hG (hD _ hb2)),
        lane_mulP _ _ (lane1 hg hG (hD _ hb2)) (lane1 hg hG (hD _ ha')), eqP_e] at h1
      exact h1
    · rw [mulK_frc] at hprod
      have h1 := beq_one_tb hprod
      rw [eqP_lane one_tb0, lane_mulP _ _ (lane1 hg hG (hD _ ha')) (lane1 hg hG (hD _ hb2)),
        lane1 hg hG hlN, eqP_e] at h1
      exact h1

theorem mem_codes {c : Nat} (hc : c < 82944) : dcG G c ∈ codes := by
  rw [codes_dc hg hG]
  exact List.mem_map_of_mem (List.mem_range.2 hc)

theorem rootOK_spec {IL R : List Nat} (hil : ilOK G IL = true) (h : rootOK G IL R = true) :
    ∀ c ∈ il, c.m ≠ I3 → ∃ q ∈ codes, q.m = I3 ∧ mulC q q = tau0 ∧ mulC q c = mulC c q := by
  rw [il_eq hg hG hil]
  intro c hc hm
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  rw [List.length_map] at hj
  rw [List.getElem_map] at hm ⊢
  have hlN := incIL hg hG hil IL[j] (List.getElem_mem _)
  unfold rootOK at h
  simp only [and'_eq, Bool.and_eq_true, frc_eqL, lanesK_eq, mulK_frc, bindP_eq] at h
  obtain ⟨hR, hr1, hr2⟩ := h
  have hRb := incB_lt hR
  have htj : (ones (lenR IL)).testBit j = true := by
    rw [ones_testBit, lenR_eq]
    exact decide_eq_true hj
  have hXj : laneOf j (cmpP (ofIx (lanePl G)) IL) = ofCd (dcG G IL[j]) := by
    rw [lane_cmpP hj, lane_dc hg hG (by simpa [List.getD_eq_getElem?_getD, hj] using hlN)]
    simp [List.getD_eq_getElem?_getD, hj]
  have hb := tb_zero hr2 j
  rw [tb_land, bnot_natOps, tb_xor, htj, isI3_lane htj, hXj, isI3_beq,
    beq_eq_false_iff_ne.2 hm, bnot_natOps, tb_xor, htj, anyComm_tb] at hb
  have hany : (R.any fun r => (commP (ones (lenR IL)) (cmpP (ofIx (lanePl G)) IL)
      (atLane (ones (lenR IL)) (ofIx (lanePl G)) r)).testBit j) = true := by
    revert hb
    cases (R.any fun r => (commP (ones (lenR IL)) (cmpP (ofIx (lanePl G)) IL)
      (atLane (ones (lenR IL)) (ofIx (lanePl G)) r)).testBit j) <;> decide
  obtain ⟨r, hr, hcr⟩ := List.any_eq_true.1 hany
  have hrN := hRb r hr
  have hXr := lane_dc hg hG hrN
  have hAr : laneOf j (atLane (ones (lenR IL)) (ofIx (lanePl G)) r) = ofCd (dcG G r) := by
    rw [lane_atLane htj, hXr]
  rw [commP_lane htj, lane_mulP _ _ hXj hAr, lane_mulP _ _ hAr hXj, eqP_e] at hcr
  have ht := allT_testBit hrN
  have hb1 := tb_zero hr1 r
  rw [tb_land, ind_testBit, decide_eq_true hr, Bool.true_and, bnot_natOps, tb_xor, ht,
    tb_land, isI3_lane ht, hXr, isI3_beq, eqP_lane ht, lane_mulP _ _ hXr hXr, lane_cst ht,
    decN_ixT, eqP_beq] at hb1
  refine ⟨dcG G r, mem_codes hg hG hrN, ?_, ?_, hcr.symm⟩
  · revert hb1
    cases h1 : ((dcG G r).m == I3) <;> cases (mulC (dcG G r) (dcG G r) == tau0) <;>
      first
      | exact fun hb => absurd hb (by decide)
      | exact fun _ => beq_iff_eq.1 h1
  · revert hb1
    cases h1 : ((dcG G r).m == I3) <;> cases h2 : (mulC (dcG G r) (dcG G r) == tau0) <;>
      first
      | exact fun hb => absurd hb (by decide)
      | exact fun _ => beq_iff_eq.1 h2

theorem classOK_spec {S CLS : List Nat} (hs : slOK G S = true) (h : classOK G S CLS = true) :
    ∀ t ∈ sl, ∃ m ∈ codes, mulC m t0c = mulC t m := by
  have hSb := incS hg hG hs
  cases S with
  | nil => exact absurd h (by unfold classOK; rw [lanesK_eq]; exact Bool.false_ne_true)
  | cons s0 S' =>
  have h0 := t0c_eq hg hG hs rfl
  have hs0 : s0 < 82944 := hSb s0 List.mem_cons_self
  rw [sl_eq hg hG hs, h0]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  rw [List.length_map] at hj
  rw [List.getElem_map]
  unfold classOK at h
  rw [lanesK_eq] at h
  change allI2 (s0 :: S') CLS _ = true at h
  obtain ⟨hjc, hf⟩ := allI2_spec h j hj
  simp only [and'_eq, Bool.and_eq_true, mulK_frc, Nat.blt_eq] at hf
  obtain ⟨hmN, he⟩ := hf
  have hsN : (s0 :: S')[j] < 82944 := hSb _ (List.getElem_mem _)
  have h1 := beq_one_tb he
  rw [eqP_lane one_tb0, lane_mulP _ _ (lane1 hg hG hmN) (lane1 hg hG hs0),
    lane_mulP _ _ (lane1 hg hG hsN) (lane1 hg hG hmN), eqP_e] at h1
  exact ⟨_, mem_codes hg hG hmN, h1⟩

theorem ordOK_spec {IL S INV : List Nat} (hs : slOK G S = true) (hi : invOK G IL S INV = true)
    (h : ordOK G S = true) :
    ∀ a ∈ dlC, ∀ b ∈ dlC, mulC (mulC a b) (mulC a b) = e0 ∨
      mulC (mulC (mulC a b) (mulC a b)) (mulC a b) = e0 := by
  have hD := incD hg hG hs
  rw [dl_eq hg hG hs hi]
  intro a ha b hb
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  rw [List.length_map] at hi' hk
  rw [List.getElem_map, List.getElem_map]
  unfold ordOK at h
  simp only [frc_eqL, lanesK_eq, mulK_frc, bindP_eq, lenR_eq, Nat.mul_eq] at h
  set D := laneT :: S with hDdef
  have hn : 0 < D.length := by simp [hDdef]
  set c := i * D.length + k with hc
  have hcn : c < D.length * D.length := by
    have : (i + 1) * D.length ≤ D.length * D.length := Nat.mul_le_mul_right _ hi'
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have htp : (ones (D.length * D.length)).testBit c = true := by
    rw [ones_testBit]
    exact decide_eq_true hcn
  have hb' := congrArg (fun p => Nat.testBit p c) (Nat.eq_of_beq_eq_true h)
  rw [htp] at hb'
  have hgi : D.getD i 0 = D[i] := by simp [List.getD_eq_getElem?_getD, hi']
  have hgk : D.getD k 0 = D[k] := by simp [List.getD_eq_getElem?_getD, hk]
  have hA : laneOf c (mapP (fun p => pairA D.length D.length (cmp D p)) (ofIx (lanePl G))) =
      ofCd (dcG G D[i]) := by
    rw [hc, lane_pairA hn hi' hk, hgi, lane_dc hg hG (hD _ (List.getElem_mem _))]
  have hB : laneOf c (mapP (fun p => pairB D.length D.length (cmp D p)) (ofIx (lanePl G))) =
      ofCd (dcG G D[k]) := by
    rw [hc, lane_pairB hn hi' hk, hgk, lane_dc hg hG (hD _ (List.getElem_mem _))]
  have hY := lane_mulP (ones (D.length * D.length)) c hA hB
  have hY2 := lane_mulP (ones (D.length * D.length)) c hY hY
  have hY3 := lane_mulP (ones (D.length * D.length)) c hY2 hY
  rw [bor_tb, eqP_lane htp, eqP_lane htp, hY2, hY3, lane_cst htp, decN_ixE, eqP_beq, eqP_beq,
    Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hb'
  exact hb'

end Lanes

end CFSG.KC.AS35QTS

end
