module

public import CFSG.Certificates.Kernel.AS35QTS.ConjSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 codes il sl t0c commB lineIn)

local notation "dlC" => CFSG.LargeExtraspecial.AS35QTS.dl

theorem take5_eq (L : List Nat) : take5 L = L.take 5 := by
  unfold take5
  generalize 5 = n
  induction L generalizing n with
  | nil => cases n <;> rfl
  | cons x L ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change x :: (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
        (fun x _ ih n => Nat.rec (motive := fun _ => List Nat) [] (fun m _ => x :: ih m) n) L n) = _
      rw [ih n]
      rfl

theorem drop5_eq (L : List Nat) : drop5 L = L.drop 5 := by
  unfold drop5
  generalize 5 = n
  induction L generalizing n with
  | nil => cases n <;> rfl
  | cons x L ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
        (fun x xs ih n => Nat.rec (motive := fun _ => List Nat) (x :: xs) (fun m _ => ih m) n)
        L n) = _
      rw [ih n]
      rfl

theorem lineRec_spec (body : Nat → List Nat → Nat → Bool) : ∀ (S LNs CMs : List Nat) (i : Nat),
    List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) (fun _ _ _ => true)
      (fun t _ ih LNs CMs i => List.rec (motive := fun _ => Bool) false (fun row CMr _ =>
        Bool.and' (ih (drop5 LNs) CMr (Nat.succ i)) (body t LNs row)) CMs) S LNs CMs i = true →
    ∀ k (hk : k < S.length), ∃ hk' : k < CMs.length, body S[k] (LNs.drop (5 * k)) CMs[k] = true
  | [], _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | t :: S, LNs, [], i, h, _, _ => absurd h Bool.false_ne_true
  | t :: S, LNs, row :: CMs, i, h, k, hk => by
    change Bool.and' (List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool)
      (fun _ _ _ => true) (fun t _ ih LNs CMs i => List.rec (motive := fun _ => Bool) false
        (fun row CMr _ => Bool.and' (ih (drop5 LNs) CMr (Nat.succ i)) (body t LNs row)) CMs)
      S (drop5 LNs) CMs (Nat.succ i)) (body t LNs row) = true at h
    rw [and'_eq, Bool.and_eq_true] at h
    cases k with
    | zero => exact ⟨by simp, by simpa using h.2⟩
    | succ k =>
      obtain ⟨hk', hb⟩ := lineRec_spec body S (drop5 LNs) CMs (Nat.succ i) h.1 k (by simpa using hk)
      refine ⟨by simpa using hk', ?_⟩
      rw [drop5_eq, List.drop_drop] at hb
      have e : 5 + 5 * k = 5 * (k + 1) := by ring
      rw [e] at hb
      simpa using hb

theorem lane_cmpP_hi {L : List Nat} {j : Nat} (hj : L.length ≤ j) (X : PL Nat) :
    laneOf j (cmpP X L) = zPL := by
  have h : ¬ j < L.length := by omega
  simp only [laneOf, cmpP, mapP, cmp_testBit, h, decide_false, Bool.false_and, zPL, ofIx]

theorem mulD_zPL : mulD bOps zPL zPL = zPL := rfl

theorem commP_zero {t c : Nat} (ht : t.testBit c = false) {X C : PL Nat} (hX : laneOf c X = zPL)
    (hC : laneOf c C = zPL) : (commP t X C).testBit c = false := by
  unfold commP
  rw [mulK_eq _ frcN_eq, mulK_eq _ frcN_eq, eqP_laneT, ht, lane_mulD, lane_mulD, hX, hC,
    mulD_zPL]
  decide

theorem filter_range_split {P : Nat → Bool} {n N : Nat} (hn : n ≤ N)
    (hz : ∀ c, n ≤ c → c < N → P c = false) :
    ((List.range N).filter P).length = ((List.range n).filter P).length := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [List.range_add, List.filter_append, List.length_append]
  have : ((List.range m).map (n + ·)).filter P = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rw [hz _ (by omega) (by have := List.mem_range.1 hb; omega)]
    simp
  rw [this]
  rfl

theorem filter_getD_length (L : List Nat) (p : Nat → Bool) :
    ((List.range L.length).filter fun j => p (L.getD j 0)).length = (L.filter p).length := by
  have e := map_getD_range (L := L) rfl id
  rw [List.map_id] at e
  conv_rhs => rw [e]
  rw [List.filter_map, List.length_map]
  rfl

theorem PL_ext {P Q : PL Nat} (h : ∀ i, laneOf i P = laneOf i Q) : P = Q := by
  obtain ⟨e, ⟨a0, a1, a2, a3, a4, a5⟩, ⟨b0, b1, b2, b3, b4, b5⟩, ⟨c0, c1, c2, c3, c4, c5⟩,
    ⟨d0, d1, d2, d3, d4, d5⟩⟩ := P
  obtain ⟨e', ⟨a0', a1', a2', a3', a4', a5'⟩, ⟨b0', b1', b2', b3', b4', b5'⟩,
    ⟨c0', c1', c2', c3', c4', c5'⟩, ⟨d0', d1', d2', d3', d4', d5'⟩⟩ := Q
  simp only [laneOf, mapP, PL.mk.injEq, V3T.mk.injEq, forall_and] at h
  obtain ⟨he, ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩, ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩,
    ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩, ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩⟩ := h
  simp only [Nat.eq_of_testBit_eq he, Nat.eq_of_testBit_eq ha0, Nat.eq_of_testBit_eq ha1,
    Nat.eq_of_testBit_eq ha2, Nat.eq_of_testBit_eq ha3, Nat.eq_of_testBit_eq ha4,
    Nat.eq_of_testBit_eq ha5, Nat.eq_of_testBit_eq hb0, Nat.eq_of_testBit_eq hb1,
    Nat.eq_of_testBit_eq hb2, Nat.eq_of_testBit_eq hb3, Nat.eq_of_testBit_eq hb4,
    Nat.eq_of_testBit_eq hb5, Nat.eq_of_testBit_eq hc0, Nat.eq_of_testBit_eq hc1,
    Nat.eq_of_testBit_eq hc2, Nat.eq_of_testBit_eq hc3, Nat.eq_of_testBit_eq hc4,
    Nat.eq_of_testBit_eq hc5, Nat.eq_of_testBit_eq hd0, Nat.eq_of_testBit_eq hd1,
    Nat.eq_of_testBit_eq hd2, Nat.eq_of_testBit_eq hd3, Nat.eq_of_testBit_eq hd4,
    Nat.eq_of_testBit_eq hd5]

theorem prodC_congr (X : PL Nat) {a b a' b' : Nat}
    (h0 : laneOf 0 (mulD (natOps 1) (atLane 1 X a) (atLane 1 X b)) =
      laneOf 0 (mulD (natOps 1) (atLane 1 X a') (atLane 1 X b'))) :
    prodC X a b = prodC X a' b' := by
  unfold prodC
  rw [mulK_eq _ frcN_eq, mulK_eq _ frcN_eq]
  refine congrArg packP (PL_ext fun i => ?_)
  cases i with
  | zero => exact h0
  | succ i =>
    have h1 : (1 : Nat).testBit (i + 1) = false := by
      rw [Nat.testBit_succ]
      simp
    rw [lane_mulD, lane_mulD, lane_atLane_f h1, lane_atLane_f h1, lane_atLane_f h1,
      lane_atLane_f h1]

theorem commP_dc {t c : Nat} (ht : t.testBit c = true) {X C : PL Nat} {x y : Cd}
    (hX : laneOf c X = ofCd x) (hC : laneOf c C = ofCd y) :
    (commP t X C).testBit c = (mulC x y == mulC y x) := by
  rw [commP_lane ht, lane_mulP _ _ hX hC, lane_mulP _ _ hC hX, eqP_beq]

theorem bitN_zero {r j : Nat} (h : Nat.beq (bitN r j) 0 = true) : r.testBit j = false := by
  rw [← bitN_testBit, Nat.eq_of_beq_eq_true h]
  rfl

theorem or'_eq (a b : Bool) : Bool.or' a b = (a || b) := by
  cases a <;> cases b <;> rfl

theorem incB_nodup {N : Nat} {L : List Nat} (h : incB N L = true) : L.Nodup :=
  List.Pairwise.imp (fun h => Nat.ne_of_lt h) (incB_go L 0 h).2

section Lanes

variable {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
include hg hG

theorem lane_cmpD {L : List Nat} (hL : ∀ s ∈ L, s < 82944) {j : Nat} (hj : j < L.length) :
    laneOf j (cmpP (ofIx (lanePl G)) L) = ofCd (dcG G L[j]) := by
  have hgj : L.getD j 0 = L[j] := by simp [List.getD_eq_getElem?_getD, hj]
  rw [lane_cmpP hj, hgj, lane_dc hg hG (hL _ (List.getElem_mem hj))]

theorem line_perm {IL S INV LN CM : List Nat} (hs : slOK G S = true)
    (hi : invOK G IL S INV = true) (hS : S.length = 36) (h : lineOK G S LN CM = true) :
    ∀ k (hk : k < S.length),
      (lineIn dlC (dcG G S[k])).Perm (((LN.drop (5 * k)).take 5).map (dcG G)) ∧
      (∀ a ∈ (LN.drop (5 * k)).take 5, a < 82944) ∧ ((LN.drop (5 * k)).take 5).length = 5 ∧
      ((LN.drop (5 * k)).take 5).Nodup ∧
      allI ((LN.drop (5 * k)).take 5) (fun _ a => allI ((LN.drop (5 * k)).take 5) fun _ b =>
        Nat.beq (commP 1 (atLane 1 (ofIx (lanePl G)) a) (atLane 1 (ofIx (lanePl G)) b)) 1) =
        true ∧ distProd (ofIx (lanePl G)) ((LN.drop (5 * k)).take 5) = true := by
  have hSb := incS hg hG hs
  have hD := incD hg hG hs
  have hDl : (laneT :: S).length = 37 := by simp [hS]
  have hdl := dl_eq hg hG hs hi
  have hrec := lineRec_spec _ S LN CM 0 (by
    unfold lineOK at h
    simpa only [frc_eqL, lanesK_eq, bindP_eq] using h)
  intro k hk
  obtain ⟨hkc, hb⟩ := hrec k hk
  simp only [and'_eq, Bool.and_eq_true, take5_eq] at hb
  obtain ⟨F1, F2, F3, F4, F5, F6, -, -, -⟩ := hb
  have hl5 : ((LN.drop (5 * k)).take 5).length = 5 := by
    rw [← lenR_eq]
    exact Nat.eq_of_beq_eq_true F2
  refine ⟨?_, incB_lt F1, hl5, incB_nodup F1, F5, F6⟩
  have hsub : ((LN.drop (5 * k)).take 5).map (dcG G) ⊆ lineIn dlC (dcG G S[k]) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj⟩ := allI_mem F3 a ha
    rw [Bool.and_eq_true] at hj
    have haD := of_decide_eq_true ((Dmask_tb S _).symm.trans (bitN_one hj.1))
    have hc := beq_one_tb hj.2
    rw [commP_dc one_tb0 (lane1 hg hG (hSb _ (List.getElem_mem hk)))
      (lane1 hg hG (hD _ haD))] at hc
    unfold lineIn
    rw [List.mem_filter, hdl]
    exact ⟨List.mem_map_of_mem haD, hc⟩
  have hnd : (((LN.drop (5 * k)).take 5).map (dcG G)).Nodup :=
    List.Nodup.map_on (fun x hx y hy e => dc_inj hg hG (incB_lt F1 x hx)
      (incB_lt F1 y hy) e) (incB_nodup F1)
  have hcount : (lineIn dlC (dcG G S[k])).length = 5 := by
    have hp := Nat.eq_of_beq_eq_true F4
    have e64 : (64 : Nat) = 32 * (1 + 1) := rfl
    rw [e64, popcount_card _ 1 (by norm_num)] at hp
    rw [filter_range_split (n := 37) (by norm_num) (fun c hc1 hc2 => commP_zero
      (by rw [ones_testBit]; exact decide_eq_false (by omega))
      (lane_atLane_f (by rw [ones_testBit]; exact decide_eq_false (by omega)) _ _)
      (lane_cmpP_hi (by rw [hDl]; exact hc1) _))] at hp
    have hXk : ∀ c, (ones 37).testBit c = true →
        laneOf c (atLane (ones 37) (ofIx (lanePl G)) S[k]) = ofCd (dcG G S[k]) := fun c ht => by
      rw [lane_atLane ht]
      exact lane_dc hg hG (hSb _ (List.getElem_mem hk))
    have e : ((List.range 37).filter fun j =>
        (commP (ones 37) (atLane (ones 37) (ofIx (lanePl G)) S[k])
          (cmpP (ofIx (lanePl G)) (laneT :: S))).testBit j) =
        (List.range (laneT :: S).length).filter fun j =>
          (commB (dcG G S[k]) ∘ dcG G) ((laneT :: S).getD j 0) := by
      rw [hDl]
      refine List.filter_congr fun c hc => ?_
      have hc' := List.mem_range.1 hc
      have ht : (ones 37).testBit c = true := by
        rw [ones_testBit]
        exact decide_eq_true hc'
      rw [commP_dc ht (hXk c ht) (lane_cmpD hg hG hD (by rw [hDl]; exact hc'))]
      simp [List.getD_eq_getElem?_getD, hDl, hc', commB]
    rw [e, filter_getD_length] at hp
    unfold lineIn
    rw [hdl, List.filter_map, List.length_map]
    exact hp
  exact ((hnd.subperm hsub).perm_of_length_le (by rw [hcount, List.length_map, hl5])).symm

theorem lineOK_spec {IL S INV LN CM : List Nat} (hs : slOK G S = true)
    (hi : invOK G IL S INV = true) (hS : S.length = 36) (h : lineOK G S LN CM = true) :
    (∀ t ∈ sl, (lineIn dlC t).length = 5) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dlC t, ∀ b ∈ lineIn dlC t, mulC a b = mulC b a) ∧
    (∀ t ∈ sl, ∀ t' ∈ sl, mulC t t' = mulC t' t → ∀ s ∈ sl,
      (mulC t s = mulC s t ↔ mulC t' s = mulC s t')) ∧
    (∀ t ∈ sl, ∀ a ∈ lineIn dlC t, ∀ b ∈ lineIn dlC t, ∀ a' ∈ lineIn dlC t,
      ∀ b' ∈ lineIn dlC t, a ≠ b → a' ≠ b' → mulC a b = mulC a' b' →
        (a = a' ∧ b = b') ∨ (a = b' ∧ b = a')) ∧
    ∀ t ∈ sl, mulC tau0 t ∉ dlC := by
  have hSb := incS hg hG hs
  have hD := incD hg hG hs
  have hDl : (laneT :: S).length = 37 := by simp [hS]
  have hdl := dl_eq hg hG hs hi
  have hrec := lineRec_spec _ S LN CM 0 (by
    unfold lineOK at h
    simpa only [frc_eqL, lanesK_eq, bindP_eq] using h)
  have hline : ∀ k (hk : k < S.length), ∃ ℓ : List Nat, (lineIn dlC (dcG G S[k])).Perm
      (ℓ.map (dcG G)) ∧ (∀ a ∈ ℓ, a < 82944) ∧ ℓ.length = 5 ∧
      allI ℓ (fun _ a => allI ℓ fun _ b =>
        Nat.beq (commP 1 (atLane 1 (ofIx (lanePl G)) a) (atLane 1 (ofIx (lanePl G)) b)) 1) =
        true ∧ distProd (ofIx (lanePl G)) ℓ = true := fun k hk => by
    obtain ⟨H1, H2, H3, -, H5, H6⟩ := line_perm hg hG hs hi hS h k hk
    exact ⟨_, H1, H2, H3, H5, H6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sl_eq hg hG hs]
    intro t ht
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    rw [List.length_map] at hk
    rw [List.getElem_map]
    obtain ⟨ℓ, hp, -, h5, -⟩ := hline k hk
    rw [hp.length_eq, List.length_map, h5]
  · rw [sl_eq hg hG hs]
    intro t ht a ha b hb
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    rw [List.length_map] at hk
    rw [List.getElem_map] at ha hb
    obtain ⟨ℓ, hp, hℓ, -, h5, -⟩ := hline k hk
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (hp.subset ha)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (hp.subset hb)
    obtain ⟨_, hx'⟩ := allI_mem h5 x hx
    obtain ⟨_, hy'⟩ := allI_mem hx' y hy
    have hc := beq_one_tb hy'
    rw [commP_dc one_tb0 (lane1 hg hG (hℓ x hx)) (lane1 hg hG (hℓ y hy)), beq_iff_eq] at hc
    exact hc
  · rw [sl_eq hg hG hs]
    intro t ht t' ht' hcomm s hs'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem ht'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs'
    rw [List.length_map] at hk hk' hj
    simp only [List.getElem_map] at hcomm ⊢
    obtain ⟨hkc, hb⟩ := hrec k hk
    obtain ⟨hkc', hb'⟩ := hrec k' hk'
    simp only [and'_eq, Bool.and_eq_true] at hb hb'
    obtain ⟨-, -, -, -, -, -, F7, F8, -⟩ := hb
    obtain ⟨-, -, -, -, -, -, F7', -, -⟩ := hb'
    have hrow : ∀ (k0 : Nat) (hk0 : k0 < S.length) (r : Nat),
        commP (ones 36) (atLane (ones 36) (ofIx (lanePl G)) S[k0]) (cmpP (ofIx (lanePl G)) S) = r →
        ∀ j0 (hj0 : j0 < S.length), r.testBit j0 =
          (mulC (dcG G S[k0]) (dcG G S[j0]) == mulC (dcG G S[j0]) (dcG G S[k0])) := by
      intro k0 hk0 r hr j0 hj0
      have ht : (ones 36).testBit j0 = true := by
        rw [ones_testBit]
        exact decide_eq_true (by omega)
      have hX0 : laneOf j0 (atLane (ones 36) (ofIx (lanePl G)) S[k0]) = ofCd (dcG G S[k0]) := by
        rw [lane_atLane ht]
        exact lane_dc hg hG (hSb _ (List.getElem_mem hk0))
      rw [← hr, commP_dc ht hX0 (lane_cmpD hg hG hSb hj0)]
    have hbit : CM[k].testBit k' = true := by
      rw [hrow k hk _ (Nat.eq_of_beq_eq_true F7) k' hk', beq_iff_eq]
      exact hcomm
    obtain ⟨hk'c, hf⟩ := allI2_spec F8 k' hk'
    rw [or'_eq, Bool.or_eq_true] at hf
    rcases hf with hf | hf
    · have := bitN_zero hf
      rw [hbit] at this
      exact absurd this (by decide)
    · have he := Nat.eq_of_beq_eq_true hf
      have r1 := hrow k hk _ (Nat.eq_of_beq_eq_true F7) j hj
      have r2 := hrow k' hk' _ (Nat.eq_of_beq_eq_true F7') j hj
      rw [he] at r1
      have r := r1.symm.trans r2
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq] at r
      exact r
  · rw [sl_eq hg hG hs]
    intro t ht a ha b hb a' ha' b' hb' hab hab' he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    rw [List.length_map] at hk
    simp only [List.getElem_map] at ha hb ha' hb' hab hab' he ⊢
    obtain ⟨ℓ, hp, hℓ, h5, -, hdist⟩ := hline k hk
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hp.subset ha)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hp.subset hb)
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem (hp.subset ha')
    obtain ⟨j', hj', rfl⟩ := List.getElem_of_mem (hp.subset hb')
    rw [List.length_map] at hi hj hi' hj'
    simp only [List.getElem_map] at hab hab' he ⊢
    have h1 := allI_spec (allI_spec (allI_spec (allI_spec hdist i hi) j hj) i' hi') j' hj'
    simp only [or'_eq, and'_eq, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h1
    have hP : prodC (ofIx (lanePl G)) ℓ[i] ℓ[j] = prodC (ofIx (lanePl G)) ℓ[i'] ℓ[j'] := by
      apply prodC_congr
      rw [lane_mulP _ _ (lane1 hg hG (hℓ _ (List.getElem_mem hi)))
          (lane1 hg hG (hℓ _ (List.getElem_mem hj))),
        lane_mulP _ _ (lane1 hg hG (hℓ _ (List.getElem_mem hi')))
          (lane1 hg hG (hℓ _ (List.getElem_mem hj'))), he]
    have hPb : Nat.beq (prodC (ofIx (lanePl G)) ℓ[i] ℓ[j])
        (prodC (ofIx (lanePl G)) ℓ[i'] ℓ[j']) = true := by
      rw [hP]
      exact Nat.beq_refl _
    rcases h1 with e | e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · subst e
      exact absurd rfl hab
    · subst e
      exact absurd rfl hab'
    · first
      | (rw [hPb] at e; exact absurd e (by decide))
      | exact absurd hP e
    · subst e1
      subst e2
      exact Or.inl ⟨rfl, rfl⟩
    · subst e1
      subst e2
      exact Or.inr ⟨rfl, rfl⟩
  · rw [sl_eq hg hG hs, hdl]
    intro t ht hmem
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ht
    rw [List.length_map] at hk
    simp only [List.getElem_map] at hmem
    obtain ⟨c, hc, hce⟩ := List.getElem_of_mem hmem
    rw [List.length_map] at hc
    simp only [List.getElem_map] at hce
    obtain ⟨hkc, hb⟩ := hrec k hk
    simp only [and'_eq, Bool.and_eq_true, mulK_frc] at hb
    obtain ⟨-, -, -, -, -, -, -, -, F9⟩ := hb
    have ht : (ones 37).testBit c = true := by
      rw [ones_testBit]
      exact decide_eq_true (by omega)
    have hz := tb_zero F9 c
    rw [eqP_lane ht, lane_mulP _ _ (lane_cst ht ixT)
      (by rw [lane_atLane ht]; exact lane_dc hg hG (hSb _ (List.getElem_mem hk))),
      lane_cmpD hg hG hD hc, decN_ixT, eqP_beq, hce] at hz
    simp at hz

theorem cm_spec {S LN CM : List Nat} (hs : slOK G S = true) (hS : S.length = 36)
    (h : lineOK G S LN CM = true) : ∀ i (hi : i < S.length), ∃ hi' : i < CM.length,
      ∀ j (hj : j < S.length), CM[i].testBit j =
        (mulC (dcG G S[i]) (dcG G S[j]) == mulC (dcG G S[j]) (dcG G S[i])) := by
  have hSb := incS hg hG hs
  have hrec := lineRec_spec _ S LN CM 0 (by
    unfold lineOK at h
    simpa only [frc_eqL, lanesK_eq, bindP_eq] using h)
  intro i hi
  obtain ⟨hic, hb⟩ := hrec i hi
  simp only [and'_eq, Bool.and_eq_true] at hb
  obtain ⟨-, -, -, -, -, -, F7, -, -⟩ := hb
  refine ⟨hic, fun j hj => ?_⟩
  have ht : (ones 36).testBit j = true := by
    rw [ones_testBit]
    exact decide_eq_true (by omega)
  have hX : laneOf j (atLane (ones 36) (ofIx (lanePl G)) S[i]) = ofCd (dcG G S[i]) := by
    rw [lane_atLane ht]
    exact lane_dc hg hG (hSb _ (List.getElem_mem hi))
  rw [← Nat.eq_of_beq_eq_true F7, commP_dc ht hX (lane_cmpD hg hG hSb hj)]

end Lanes

end CFSG.KC.AS35QTS

end
