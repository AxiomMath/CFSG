module

public import CFSG.Certificates.Kernel.AS35QTS.LineSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 codes il sl wl t0c commB lineIn zpowL
  pow72 isInv)

local notation "dlC" => CFSG.LargeExtraspecial.AS35QTS.dl

@[expose] def hitB (b : Bool) (y τ : PL Bool) : Nat → PL Bool → Bool → Bool
  | 0, _, a => a
  | n + 1, p, a => hitB b y τ n (mulD bOps p y) (a || eqP (bOpsT b) p τ)

theorem hitK_lane (t c : Nat) (Y T : PL Nat) : ∀ n P acc, (hitK t Y T n P acc).testBit c =
    hitB (t.testBit c) (laneOf c Y) (laneOf c T) n (laneOf c P) (acc.testBit c)
  | 0, P, acc => rfl
  | n + 1, P, acc => by
    change (mulK (natOps t) frcN P Y fun P' => frcN (Nat.lor acc (eqP (natOps t) P T))
      fun acc' => hitK t Y T n P' acc').testBit c = _
    rw [mulK_eq _ frcN_eq, frcN_eq, hitK_lane t c Y T n, lane_mulD, tb_lor, eqP_laneT]
    rfl

theorem bOpsT_true : bOpsT true = bOps := rfl

theorem hitB_codes (y τ : Cd) : ∀ n (p : Cd) (a : Bool),
    hitB true (ofCd y) (ofCd τ) n (ofCd p) a =
      (a || decide (τ ∈ List.iterate (fun x => mulC x y) p n))
  | 0, p, a => by simp [hitB]
  | n + 1, p, a => by
    rw [hitB, mulD_ofCd, hitB_codes y τ n, bOpsT_true, eqP_beq]
    have e : List.iterate (fun x => mulC x y) p (n + 1) =
        p :: List.iterate (fun x => mulC x y) (mulC p y) n := rfl
    rw [e, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

theorem hitB_zero : ∀ n a, hitB false zPL zPL n zPL a = a
  | 0, a => rfl
  | n + 1, a => by
    rw [hitB, mulD_zPL, hitB_zero n]
    cases a <;> rfl

theorem lane_cst_f {t c : Nat} (ht : t.testBit c = false) (n : Nat) : laneOf c (cst t n) = zPL := by
  simp only [laneOf, mapP, cst, ofIx, mulbit_tb, ht, Bool.and_false, zPL]

theorem lane_pairA_hi {na nb : Nat} (hb : 0 < nb) {L : List Nat} {c : Nat} (hc : na * nb ≤ c)
    (X : PL Nat) : laneOf c (mapP (fun p => pairA na nb (cmp L p)) X) = zPL := by
  have hf : ∀ (p : Nat), ∀ i < na, Nat.mul (bitN p i) (ones nb) < 2 ^ nb := by
    intro p i _
    have h1 : bitN p i ≤ 1 := by have := bitN_lt p i; omega
    change bitN p i * (2 ^ nb - 1) < 2 ^ nb
    calc bitN p i * (2 ^ nb - 1) ≤ 1 * (2 ^ nb - 1) := Nat.mul_le_mul_right _ h1
      _ < 2 ^ nb := by rw [one_mul]; exact Nat.sub_lt (Nat.two_pow_pos _) one_pos
  have hn : ¬ c < nb * na := by rw [Nat.mul_comm]; omega
  simp only [laneOf, mapP, pairA, blk_testBit hb (hf _), hn, decide_false, Bool.false_and, zPL,
    ofIx]

theorem lane_pairB_hi {na nb : Nat} (hb : 0 < nb) {M : List Nat} (hM : M.length = nb) {c : Nat}
    (hc : na * nb ≤ c) (X : PL Nat) :
    laneOf c (mapP (fun p => pairB na nb (cmp M p)) X) = zPL := by
  have hn : ¬ c < nb * na := by rw [Nat.mul_comm]; omega
  have hf : ∀ (p : Nat), ∀ i < na, (fun _ => cmp M p) i < 2 ^ nb := fun p _ _ => hM ▸ cmp_lt p M
  simp only [laneOf, mapP, pairB, blk_testBit hb (hf _), hn, decide_false, Bool.false_and, zPL,
    ofIx]

theorem lane_pairA_c {L M : List Nat} (hM : 0 < M.length) {c : Nat}
    (hc : c < L.length * M.length) (X : PL Nat) :
    laneOf c (mapP (fun p => pairA L.length M.length (cmp L p)) X) =
      laneOf (L.getD (c / M.length) 0) X := by
  have h := lane_pairA (L := L) hM (i := c / M.length) (k := c % M.length)
    (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)) (Nat.mod_lt _ hM) X
  rwa [Nat.div_add_mod'] at h

theorem lane_pairB_c {L M : List Nat} (hM : 0 < M.length) {c : Nat}
    (hc : c < L.length * M.length) (X : PL Nat) :
    laneOf c (mapP (fun p => pairB L.length M.length (cmp M p)) X) =
      laneOf (M.getD (c % M.length) 0) X := by
  have h := lane_pairB (L := L) hM (i := c / M.length) (k := c % M.length)
    (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)) (Nat.mod_lt _ hM) X
  rwa [Nat.div_add_mod'] at h

theorem getD_mem {L : List Nat} {i : Nat} (hi : i < L.length) : L.getD i 0 ∈ L := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

theorem range_filter_card (n : Nat) (q : Nat → Bool) :
    ((List.range n).filter q).length = ((Finset.range n).filter fun c => q c = true).card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]

section Lanes

variable {G : List Nat} (hg : gOK G = true) (hG : G.length = 648)
include hg hG

theorem pair_card {L M : List Nat} (hL : ∀ a ∈ L, a < 82944) (hM : ∀ a ∈ M, a < 82944)
    (hLn : L.Nodup) (hMn : M.Nodup) (hM0 : 0 < M.length) (P : Cd × Cd → Prop)
    [DecidablePred P] :
    (((L.map (dcG G)).toFinset ×ˢ (M.map (dcG G)).toFinset).filter P).card =
      ((List.range (L.length * M.length)).filter fun c =>
        decide (P (dcG G (L.getD (c / M.length) 0), dcG G (M.getD (c % M.length) 0)))).length := by
  set m := M.length with hm
  set f : Nat → Cd × Cd := fun c => (dcG G (L.getD (c / m) 0), dcG G (M.getD (c % m) 0)) with hf
  rw [range_filter_card]
  have hdiv : ∀ c, c < L.length * m → c / m < L.length := fun c hc =>
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
  have e : ((L.map (dcG G)).toFinset ×ˢ (M.map (dcG G)).toFinset).filter P =
      ((Finset.range (L.length * m)).filter fun c => decide (P (f c)) = true).image f := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, List.mem_toFinset, Finset.mem_image,
      Finset.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨ha, hb⟩, hP⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
      have hq : (i * m + k) / m = i := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM0, Nat.div_eq_of_lt hk, Nat.zero_add]
      have hr : (i * m + k) % m = k := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
      have hfc : f (i * m + k) = (dcG G L[i], dcG G M[k]) := by
        simp only [hf, hq, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hk, Option.getD_some]
      refine ⟨i * m + k, ⟨?_, by rw [hfc]; exact hP⟩, hfc⟩
      have : (i + 1) * m ≤ L.length * m := Nat.mul_le_mul_right _ hi
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · rintro ⟨c, ⟨hc, hP⟩, hfc⟩
      have hfc' := hfc
      simp only [hf, Prod.mk.injEq] at hfc'
      obtain ⟨rfl, rfl⟩ := hfc'
      exact ⟨⟨List.mem_map_of_mem (getD_mem (hdiv c hc)),
        List.mem_map_of_mem (getD_mem (Nat.mod_lt _ hM0))⟩, hP⟩
  rw [e, Finset.card_image_of_injOn]
  intro c hc c' hc' hcc
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hc hc'
  simp only [hf, Prod.mk.injEq] at hcc
  have h1 := dc_inj hg hG (hL _ (getD_mem (hdiv c hc.1))) (hL _ (getD_mem (hdiv c' hc'.1))) hcc.1
  have h2 := dc_inj hg hG (hM _ (getD_mem (Nat.mod_lt c hM0)))
    (hM _ (getD_mem (Nat.mod_lt c' hM0))) hcc.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hdiv c hc.1), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hdiv c' hc'.1), Option.getD_some] at h1
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt c hM0), Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.mod_lt c' hM0),
    Option.getD_some] at h2
  have i1 := (List.Nodup.getElem_inj_iff hLn).1 h1
  have i2 := (List.Nodup.getElem_inj_iff hMn).1 h2
  rw [← Nat.div_add_mod c m, ← Nat.div_add_mod c' m, i1, i2]

theorem dl_nodup : List.Nodup dlC := by
  change (tau0 :: sl).Nodup
  refine List.nodup_cons.2 ⟨fun h => ?_, ?_⟩
  · change tau0 ∈ (CFSG.LargeExtraspecial.AS35QTS.il).filter _ at h
    rw [List.mem_filter, Bool.and_eq_true, bne_iff_ne] at h
    exact h.2.1 rfl
  · change ((CFSG.LargeExtraspecial.AS35QTS.il).filter _).Nodup
    refine List.Nodup.filter _ (List.Nodup.filter _ (codes_nodup hg hG))

theorem D_nodup {IL S INV : List Nat} (hs : slOK G S = true) (hi : invOK G IL S INV = true) :
    (laneT :: S).Nodup := by
  have h := dl_nodup hg hG
  rw [dl_eq hg hG hs hi] at h
  exact List.Nodup.of_map _ h

theorem mem_map_dc {L : List Nat} (hL : ∀ a ∈ L, a < 82944) {c : Nat} (hc : c < 82944) :
    dcG G c ∈ L.map (dcG G) ↔ c ∈ L := by
  constructor
  · intro h
    obtain ⟨d, hd, he⟩ := List.mem_map.1 h
    rw [dc_inj hg hG (hL d hd) hc he] at hd
    exact hd
  · exact List.mem_map_of_mem

theorem wl_eq {IL S INV W : List Nat} (hil : ilOK G IL = true) (hs : slOK G S = true)
    (hi : invOK G IL S INV = true) (hW : incB 82944 W = true)
    (hWm : ind W = Nat.land (ind IL) (Nat.xor (Nat.lor (Nat.shiftLeft 1 laneT) (ind S)) allT)) :
    wl = W.map (dcG G) := by
  have e : wl = codes.filter (fun c => !(List.contains dlC c) && isInv c) := by
    change ((codes.filter isInv).filter _) = _
    rw [List.filter_filter]
  rw [e]
  refine codes_filter hg hG _ hW fun c hc => ?_
  have hb := congrArg (fun p => Nat.testBit p c) hWm
  rw [ind_testBit, tb_land, ind_testBit, tb_xor, Dmask_tb, allT_testBit hc, Bool.xor_true] at hb
  have hinv : isInv (dcG G c) = true ↔ c ∈ IL := by
    rw [← mem_map_dc hg hG (incIL hg hG hil) hc, ← il_eq hg hG hil]
    change _ ↔ dcG G c ∈ codes.filter isInv
    rw [List.mem_filter]
    exact ⟨fun h => ⟨mem_codes hg hG hc, h⟩, fun h => h.2⟩
  have hdlm : List.contains dlC (dcG G c) = decide (c ∈ laneT :: S) := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, dl_eq hg hG hs hi, decide_eq_true_iff]
    exact mem_map_dc hg hG (incD hg hG hs) hc
  rw [Bool.and_eq_true, hdlm, hinv, ← decide_eq_true_iff (p := c ∈ W), hb]
  by_cases h1 : c ∈ laneT :: S <;> by_cases h2 : c ∈ IL <;> simp [h1, h2]

theorem nzOK_spec {IL S INV W : List Nat} (hil : ilOK G IL = true) (hs : slOK G S = true)
    (hi : invOK G IL S INV = true) (hS : S.length = 36) (hWl : W.length = 90)
    (h : nzOK G S IL W = true) :
    (∀ x ∈ dlC, ∀ v ∈ wl, pow72 (mulC x v) = e0) ∧
    (((List.toFinset dlC) ×ˢ wl.toFinset).filter fun p => tau0 ∈ zpowL (mulC p.1 p.2)).card =
      1188 := by
  unfold nzOK at h
  simp only [frc_eqL, lanesK_eq, bindP_eq, mulK_frc, lenR_eq, Nat.mul_eq, and'_eq,
    Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨hW, hWm⟩, h72, hcnt⟩ := h
  have hD := incD hg hG hs
  have hWb := incB_lt hW
  have hDl : (laneT :: S).length = 37 := by simp [hS]
  have hW0 : 0 < W.length := by omega
  have hwl := wl_eq hg hG hil hs hi hW hWm
  have hdl := dl_eq hg hG hs hi
  set D := laneT :: S with hDdef
  set X := ofIx (lanePl G) with hX
  set tp := ones (D.length * W.length) with htp
  have hlane : ∀ c, c < D.length * W.length →
      laneOf c (mulD (natOps tp) (mapP (fun p => pairA D.length W.length (cmp D p)) X)
        (mapP (fun p => pairB D.length W.length (cmp W p)) X)) =
        ofCd (mulC (dcG G (D.getD (c / W.length) 0)) (dcG G (W.getD (c % W.length) 0))) := by
    intro c hc
    rw [lane_mulP _ _ (by rw [lane_pairA_c hW0 hc]; exact lane_dc hg hG (hD _ (getD_mem
      (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)))))
      (by rw [lane_pairB_c hW0 hc]; exact lane_dc hg hG (hWb _ (getD_mem (Nat.mod_lt _ hW0))))]
  refine ⟨?_, ?_⟩
  · rw [hdl, hwl]
    intro x hx v hv
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    rw [List.length_map] at hi' hk
    simp only [List.getElem_map]
    set c := i * W.length + k with hc
    have hcn : c < D.length * W.length := by
      have : (i + 1) * W.length ≤ D.length * W.length := Nat.mul_le_mul_right _ hi'
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    have hq : c / W.length = i := by
      rw [hc, Nat.add_comm, Nat.add_mul_div_right _ _ hW0, Nat.div_eq_of_lt hk, Nat.zero_add]
    have hr : c % W.length = k := by
      rw [hc, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
    have ht : tp.testBit c = true := by
      rw [htp, ones_testBit]
      exact decide_eq_true hcn
    have hY := hlane c hcn
    rw [hq, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] at hY
    have h2 := lane_mulP tp c hY hY
    have h4 := lane_mulP tp c h2 h2
    have h8 := lane_mulP tp c h4 h4
    have h16 := lane_mulP tp c h8 h8
    have h32 := lane_mulP tp c h16 h16
    have h64 := lane_mulP tp c h32 h32
    have h72' := lane_mulP tp c h64 h8
    have hb := congrArg (fun p => Nat.testBit p c) h72
    rw [eqP_lane ht, h72', lane_cst ht, decN_ixE, ht, eqP_e] at hb
    exact hb
  · rw [hdl, hwl, pair_card hg hG hD hWb (D_nodup hg hG hs hi) (incB_nodup hW) hW0]
    have e3 : (3392 : Nat) = 32 * (105 + 1) := rfl
    rw [e3, popcount_card _ 105 (by norm_num)] at hcnt
    rw [filter_range_split (n := D.length * W.length) (by rw [hDl, hWl]; norm_num)
      (fun c hc1 hc2 => by
        have htf : tp.testBit c = false := by
          rw [htp, ones_testBit]
          exact decide_eq_false (by omega)
        rw [hitK_lane, htf, lane_mulD, lane_pairA_hi hW0 hc1, lane_pairB_hi hW0 rfl hc1,
          mulD_zPL, lane_cst_f htf, lane_cst_f htf, hitB_zero]
        exact Nat.zero_testBit c)] at hcnt
    rw [← hcnt]
    refine congrArg List.length (List.filter_congr fun c hc => ?_)
    have hc' := List.mem_range.1 hc
    have ht : tp.testBit c = true := by
      rw [htp, ones_testBit]
      exact decide_eq_true hc'
    rw [hitK_lane, ht, hlane c hc', lane_cst ht, lane_cst ht, decN_ixE, decN_ixT, hitB_codes]
    simp only [Nat.zero_testBit, Bool.false_or]
    rfl

theorem nwOK_spec {IL S INV W V0 LN CM : List Nat} (hil : ilOK G IL = true)
    (hs : slOK G S = true) (hi : invOK G IL S INV = true) (hS : S.length = 36)
    (hV : V0.length = 10) (hz : nzOK G S IL W = true) (hl : lineOK G S LN CM = true)
    (h : nwOK G S W V0 LN = true) :
    (((lineIn dlC t0c).toFinset ×ˢ (wl.filter (commB t0c)).toFinset).filter
      fun p => mulC tau0 t0c ∈ zpowL (mulC p.1 p.2)).card = 3 := by
  have hSb := incS hg hG hs
  unfold nzOK at hz
  simp only [frc_eqL, lanesK_eq, bindP_eq, mulK_frc, lenR_eq, Nat.mul_eq, and'_eq,
    Bool.and_eq_true, Nat.beq_eq] at hz
  obtain ⟨⟨hW, hWm⟩, -, -⟩ := hz
  have hWb := incB_lt hW
  have hwl := wl_eq hg hG hil hs hi hW hWm
  cases S with
  | nil => exact absurd hS (by simp)
  | cons s0 S' =>
  have h0 := t0c_eq hg hG hs rfl
  have hs0 : s0 < 82944 := hSb s0 List.mem_cons_self
  obtain ⟨hp, hℓ, h5, hℓn, -, -⟩ := line_perm hg hG hs hi hS hl 0 (by simp)
  simp only [Nat.mul_zero, List.drop_zero, List.getElem_cons_zero] at hp hℓ h5 hℓn
  rw [← h0] at hp
  unfold nwOK at h
  simp only [frc_eqL, lanesK_eq, bindP_eq, mulK_frc, lenR_eq, Nat.mul_eq, and'_eq,
    Bool.and_eq_true, Nat.beq_eq, take5_eq] at h
  change incB 82944 V0 = true ∧ _ ∧ _ at h
  obtain ⟨hV0, hVm, hcnt⟩ := h
  have hVb := incB_lt hV0
  have hV00 : 0 < V0.length := by omega
  set X := ofIx (lanePl G) with hX
  have hvl : wl.filter (commB t0c) = V0.map (dcG G) := by
    rw [hwl, List.filter_map, h0]
    refine congrArg (List.map (dcG G)) ?_
    refine eq_of_pairwise_lt (List.Pairwise.filter _ (incB_go W 0 hW).2) (incB_go V0 0 hV0).2
      fun c => ?_
    rw [List.mem_filter]
    have key : ∀ c, c < 82944 → (c ∈ V0 ↔ c ∈ W ∧ (commB (dcG G s0) ∘ dcG G) c = true) := by
      intro c hc
      have ht := allT_testBit hc
      have hb := congrArg (fun p => Nat.testBit p c) hVm
      rw [tb_land, ind_testBit, ind_testBit, commP_dc ht (lane_dc hg hG hc)
        (by rw [lane_atLane ht]; exact lane_dc hg hG hs0)] at hb
      rw [← decide_eq_true_iff (p := c ∈ V0), ← hb, Bool.and_eq_true, decide_eq_true_iff]
      simp only [Function.comp_apply, commB]
      rw [beq_comm']
    constructor
    · rintro ⟨hcW, hcc⟩
      exact (key c (hWb c hcW)).2 ⟨hcW, hcc⟩
    · intro hcV
      exact (key c (hVb c hcV)).1 hcV
  rw [List.toFinset_eq_of_perm _ _ hp, hvl, pair_card hg hG hℓ hVb hℓn (incB_nodup hV0) hV00]
  have e64 : (64 : Nat) = 32 * (1 + 1) := rfl
  rw [e64, popcount_card _ 1 (by norm_num)] at hcnt
  set ℓ := (LN.take 5) with hℓdef
  set tp := ones (5 * V0.length) with htp
  have hlA : ∀ c, c < ℓ.length * V0.length →
      laneOf c (mapP (fun p => pairA 5 V0.length (cmp ℓ p)) X) =
        ofCd (dcG G (ℓ.getD (c / V0.length) 0)) := by
    intro c hc
    have e := lane_pairA_c (L := ℓ) hV00 hc X
    rw [h5] at e
    rw [e]
    exact lane_dc hg hG (hℓ _ (getD_mem (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc))))
  have hlB : ∀ c, c < ℓ.length * V0.length →
      laneOf c (mapP (fun p => pairB 5 V0.length (cmp V0 p)) X) =
        ofCd (dcG G (V0.getD (c % V0.length) 0)) := by
    intro c hc
    have e := lane_pairB_c (L := ℓ) hV00 hc X
    rw [h5] at e
    rw [e]
    exact lane_dc hg hG (hVb _ (getD_mem (Nat.mod_lt _ hV00)))
  rw [filter_range_split (n := 5 * V0.length) (by rw [hV]; norm_num)
    (fun c hc1 hc2 => by
      have htf : tp.testBit c = false := by
        rw [htp, ones_testBit]
        exact decide_eq_false (by omega)
      rw [hitK_lane, htf, lane_mulD, lane_mulD, lane_pairA_hi hV00 hc1, lane_pairB_hi hV00 rfl hc1,
        mulD_zPL, lane_cst_f htf, lane_atLane_f htf, mulD_zPL, lane_cst_f htf, hitB_zero]
      exact Nat.zero_testBit c)] at hcnt
  rw [← hcnt, h5]
  refine congrArg List.length (List.filter_congr fun c hc => ?_)
  have hc' := List.mem_range.1 hc
  have hc5 : c < ℓ.length * V0.length := by rw [h5]; exact hc'
  have ht : tp.testBit c = true := by
    rw [htp, ones_testBit]
    exact decide_eq_true hc'
  rw [hitK_lane, ht, lane_mulP _ _ (hlA c hc5) (hlB c hc5),
    lane_mulP _ _ (lane_cst ht ixT) (by rw [lane_atLane ht]; exact lane_dc hg hG hs0),
    lane_cst ht, decN_ixE, decN_ixT, hitB_codes, h0]
  simp only [Nat.zero_testBit, Bool.false_or]
  rfl

theorem swapOK_spec {IL S LN CM : List Nat} (hil : ilOK G IL = true) (hs : slOK G S = true)
    (hS : S.length = 36) (hIL : IL.length = 127) (hl : lineOK G S LN CM = true)
    (h : swapOK G S IL CM = true) :
    ∀ p ∈ sl, ∀ p' ∈ sl, p ≠ p' → mulC p p' = mulC p' p →
      (il.toFinset.filter fun v => mulC v p = mulC p' v).card = 16 ∧
        ∀ q ∈ sl, q ≠ p → q ≠ p' → mulC p q = mulC q p → ∀ v ∈ il,
          mulC v p = mulC p' v → mulC v q ≠ mulC q v := by
  have hSb := incS hg hG hs
  have hILb := incIL hg hG hil
  have hcm := cm_spec hg hG hs hS hl
  have hiln : il.Nodup := List.Nodup.filter _ (codes_nodup hg hG)
  have hile := il_eq hg hG hil
  unfold swapOK at h
  simp only [frc_eqL, lanesK_eq, bindP_eq, lenR_eq] at h
  set X := ofIx (lanePl G) with hX
  set ti := ones IL.length with hti
  rw [sl_eq hg hG hs]
  intro p hp p' hp' hne hcomm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp'
  rw [List.length_map] at hi hj
  simp only [List.getElem_map] at hne hcomm ⊢
  have hij : i ≠ j := fun e => hne (by subst e; rfl)
  obtain ⟨hic, hrow⟩ := hcm i hi
  have hbj : CM[i].testBit j = true := by
    rw [hrow j hj, beq_iff_eq]
    exact hcomm
  obtain ⟨hic', hf⟩ := allI2_spec h i hi
  have hf2 := allI_spec hf j hj
  simp only [or'_eq, Bool.or_eq_true, Nat.beq_eq, mulK_frc, frc_eqL, and'_eq,
    Bool.and_eq_true] at hf2
  rcases hf2 with e | e | ⟨hcnt, hqa⟩
  · exact absurd e hij
  · exact absurd (bitN_zero (by rw [e]; rfl)) (by rw [hbj]; decide)
  have hXi : ∀ c, ti.testBit c = true → laneOf c (atLane ti X S[i]) = ofCd (dcG G S[i]) :=
    fun c ht => by rw [lane_atLane ht]; exact lane_dc hg hG (hSb _ (List.getElem_mem hi))
  have hXj : ∀ c, ti.testBit c = true → laneOf c (atLane ti X S[j]) = ofCd (dcG G S[j]) :=
    fun c ht => by rw [lane_atLane ht]; exact lane_dc hg hG (hSb _ (List.getElem_mem hj))
  have hM : ∀ m (hm : m < IL.length), (eqP (natOps ti) (mulD (natOps ti) (cmpP X IL)
      (atLane ti X S[i])) (mulD (natOps ti) (atLane ti X S[j]) (cmpP X IL))).testBit m =
      (mulC (dcG G IL[m]) (dcG G S[i]) == mulC (dcG G S[j]) (dcG G IL[m])) := by
    intro m hm
    have ht : ti.testBit m = true := by
      rw [hti, ones_testBit]
      exact decide_eq_true hm
    rw [eqP_lane ht, lane_mulP _ _ (lane_cmpD hg hG hILb hm) (hXi m ht),
      lane_mulP _ _ (hXj m ht) (lane_cmpD hg hG hILb hm), eqP_beq]
  refine ⟨?_, ?_⟩
  · have e128 : (128 : Nat) = 32 * (3 + 1) := rfl
    rw [e128, popcount_card _ 3 (by norm_num)] at hcnt
    rw [filter_range_split (n := IL.length) (by rw [hIL]; norm_num)
      (fun c hc1 hc2 => by
        have htf : ti.testBit c = false := by
          rw [hti, ones_testBit]
          exact decide_eq_false (by omega)
        rw [eqP_laneT, htf, lane_mulD, lane_mulD, lane_cmpP_hi hc1, lane_atLane_f htf,
          lane_atLane_f htf, mulD_zPL]
        rfl)] at hcnt
    have ef : il.toFinset.filter (fun v => mulC v (dcG G S[i]) = mulC (dcG G S[j]) v) =
        (il.filter fun v => decide (mulC v (dcG G S[i]) = mulC (dcG G S[j]) v)).toFinset := by
      ext v
      simp [List.mem_filter]
    rw [ef, List.toFinset_card_of_nodup (hiln.filter _), hile,
      List.filter_map, List.length_map, ← hcnt, ← filter_getD_length]
    refine congrArg List.length (List.filter_congr fun c hc => ?_)
    have hc' := List.mem_range.1 hc
    rw [hM c hc']
    simp [List.getD_eq_getElem?_getD, hc']
    rfl
  · intro q hq hqp hqp' hpq v hv hvp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
    rw [List.length_map] at hk
    simp only [List.getElem_map] at hqp hqp' hpq ⊢
    rw [hile] at hv
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hv
    rw [List.length_map] at hm
    simp only [List.getElem_map] at hvp ⊢
    have hki : k ≠ i := fun e => hqp (by subst e; rfl)
    have hkj : k ≠ j := fun e => hqp' (by subst e; rfl)
    have hbk : CM[i].testBit k = true := by
      rw [hrow k hk, beq_iff_eq]
      exact hpq
    have hq2 := allI_spec hqa k hk
    simp only [or'_eq, Bool.or_eq_true, Nat.beq_eq] at hq2
    rcases hq2 with e | e | e | e
    · exact absurd e hki
    · exact absurd e hkj
    · exact absurd (bitN_zero (by rw [e]; rfl)) (by rw [hbk]; decide)
    have ht : ti.testBit m = true := by
      rw [hti, ones_testBit]
      exact decide_eq_true hm
    have hb := congrArg (fun p => Nat.testBit p m) e
    rw [Nat.zero_testBit, tb_land, hM m hm, commP_dc ht (lane_cmpD hg hG hILb hm)
      (by rw [lane_atLane ht]; exact lane_dc hg hG (hSb _ (List.getElem_mem hk))),
      (beq_iff_eq).2 hvp, Bool.true_and] at hb
    intro hvq
    rw [(beq_iff_eq).2 hvq] at hb
    exact absurd hb (by decide)

end Lanes

end CFSG.KC.AS35QTS

end
