
module

public import CFSG.Certificates.Kernel.M24L2.L2DSound
public import CFSG.Certificates.Kernel.M24L2.BfsClose
public import Certificates.Data.Kernel.M24L2.FC

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.KC.Enum

theorem sortedK_pairwise : ∀ L : List Nat, sortedK L = true → L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    unfold sortedK at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    have ih := sortedK_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem dLinB_of {c : Nat} (h : normBK c = true) : dLinB (c / 16) = true := by
  unfold normBK normKK conjInK at h
  simp only [Bool.and_eq_true, List.any_eq_true, Nat.beq_eq] at h
  obtain ⟨k, hk, hke⟩ := h.1.1.1
  unfold dLinB
  rw [List.any_eq_true]
  refine ⟨k, hk, ?_⟩
  rw [Nat.beq_eq]
  have e1 := mulC_div16 c b0C
  have e2 := mulC_div16 k c
  rw [hke] at e1
  have h3 := mulC_mod16_lin (c / 16) (b0C / 16)
  have h4 := mulC_mod16_lin (k / 16) (c / 16)
  change mulC (16 * (c / 16)) (16 * (b0C >>> 4)) = mulC (16 * (k >>> 4)) (16 * (c / 16))
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  change mulC (16 * (c / 16)) (16 * (b0C / 16)) = mulC (16 * (k / 16)) (16 * (c / 16))
  omega

theorem dLM_spec {D : List Nat} {m : Nat} (h : dLM D m = true) :
    ∀ v < 16, normBK (v + 16 * m) = true → v + 16 * m ∈ D := by
  intro v hv hn
  unfold dLM at h
  have hl : dLinB m = true := by
    have := dLinB_of hn
    rwa [show (v + 16 * m) / 16 = m by omega] at this
  rw [hl] at h
  change allN 16 _ = true at h
  rw [CFSG.KS.Raw.Orb.allN_iff] at h
  have := h v hv
  rw [letN_eq] at this
  change bIf(normBK (v + 16 * m), D.contains (v + 16 * m), true) = true at this
  rw [hn] at this
  exact List.contains_iff_mem.1 this

theorem dList_pairwise : (mkCtx ()).dList.Pairwise (· < ·) := by
  unfold Ctx8.dList Ctx8.codes
  exact ((List.pairwise_lt_range).filter _).filter _

theorem dList_eq {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) {D : List Nat} (hs : sortedK D = true)
    (hD : ∀ d ∈ D, validK G d = true ∧ normBK d = true) (h : ∀ m ∈ L, dLM D m = true) :
    (mkCtx ()).dList = D := by
  have hmem : ∀ c, c ∈ (mkCtx ()).dList ↔ c ∈ D := by
    intro c
    rw [dList_mem]
    constructor
    · rintro ⟨hc, hn⟩
      rw [tab_of_mem hR hc, normB_tabC] at hn
      exact forall_codes hR hL (P := fun c => normBK c = true → c ∈ D)
        (fun m hm v hv => dLM_spec (h m hm) v hv) c hc hn
    · intro hc
      have hcc := hG c (hD c hc).1
      refine ⟨hcc, ?_⟩
      rw [tab_of_mem hR hcc, normB_tabC]
      exact (hD c hc).2
  have hp : (mkCtx ()).dList.Perm D :=
    (List.perm_ext_iff_of_nodup dList_pairwise.nodup (sortedK_pairwise D hs).nodup).2 hmem
  exact List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _))
    dList_pairwise (sortedK_pairwise D hs) hp

theorem isTt_evT (w : List (Fin 3)) : (mkCtx ()).isTt (evT dT w) = isTtK (evK dC w) := by
  rw [evT_dT, isTt_tabC (evK_lt _ _)]

theorem isBt_evT (w : List (Fin 3)) : isBt (evT dT w) = isBtK (evK dC w) := by
  rw [evT_dT, isBt_tabC (evK_lt _ _)]

theorem evT_beq_id (w : List (Fin 3)) : (evT dT w == idT 16) = Nat.beq (evK dC w) idC := by
  rw [evT_dT, idT_beq (evK_lt _ _)]

theorem evT_beq (w w' : List (Fin 3)) :
    (evT dT w == evT dT w') = Nat.beq (evK dC w) (evK dC w') := by
  rw [evT_dT, evT_dT, beq_tabC (evK_lt _ _) (evK_lt _ _)]

theorem codeOf_compT_dT (x : Nat) (k : Fin 3) : codeOf (compT 16 (tabC x) (dT k)) = mulC x (dC k) := by
  rw [dT_eq, compT_tabC, codeOf_tabC (mulC_lt _ _)]

theorem fcAll_eq : fcAll (mkCtx ()) = fcAllK := by
  have hq : (dBFSq ()).2.toList = dQ.map entT := dBFSq_twin.1
  have hlook : ∀ (x : Nat) (k : Fin 3), (dBFSq ()).1[codeOf (compT 16 (tabC x) (dT k))]! =
      (dQ.find? fun e => e.1 == mulC x (dC k)).map Prod.snd := by
    intro x k
    rw [codeOf_compT_dT, dBFSq_twin.2.2.1 _ (mulC_lt _ _)]
    rfl
  unfold fcAll fcAllK
  simp only [hq, List.map_map, List.flatMap_map]
  have e1 : (Prod.snd ∘ entT : Nat × List (Fin 3) → List (Fin 3)) = Prod.snd := rfl
  rw [e1]
  have e2 : (fun xw : Nat × List (Fin 3) => (List.finRange 3).map fun k =>
      ((entT xw).2 ++ [k], ((dBFSq ()).1[codeOf (compT 16 (entT xw).1 (dT k))]!).getD [])) =
      fun xw => (List.finRange 3).map fun k =>
        (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD []) := by
    funext xw
    refine congrArg (fun f => List.map f (List.finRange 3)) (funext fun k => ?_)
    change (xw.2 ++ [k], ((dBFSq ()).1[codeOf (compT 16 (tabC xw.1) (dT k))]!).getD []) = _
    rw [hlook]
  rw [e2]
  simp only [isTt_evT, isBt_evT, evT_beq_id, evT_beq]

theorem bfsT_closed_len {α : Type} {N : Nat} {keyN : Nat → Nat} {lc : α → Nat} {lets : List α}
    {c0 : Nat} (hN : ∀ c < 2 ^ 20, keyN c < N) (h0 : c0 < 2 ^ 20) {F : Nat}
    (hF : (bfsT F keyN lc lets c0).all.length ≤ F) :
    ∀ e ∈ (bfsT F keyN lc lets c0).all, Closed keyN lc lets (bfsT F keyN lc lets c0).all e := by
  have h := ti_loop (lets := lets) (lc := lc) hN F 0 _ (ti_init hN h0)
  rw [Nat.zero_add] at h
  change TI N keyN lc lets c0 F (bfsT F keyN lc lets c0) at h
  obtain ⟨P, hsplit, hlen, hcl⟩ := h.split
  have hq : queueOf (bfsT F keyN lc lets c0) = [] := by
    rcases hlen with hlen | hlen
    · by_contra hne
      have := congrArg List.length hsplit
      rw [List.length_reverse, List.length_append, hlen] at this
      have : 0 < (queueOf (bfsT F keyN lc lets c0)).length := List.length_pos_iff.2 hne
      omega
    · exact hlen
  rw [hq, List.append_nil] at hsplit
  intro e he
  exact hcl e (by rw [← hsplit, List.mem_reverse]; exact he)

theorem dQ_good {e : Nat × List (Fin 3)} (he : e ∈ dQ) : evK dC e.2 = e.1 := by
  rw [dQ, List.mem_reverse] at he
  obtain ⟨_, h, _⟩ := dBFSq_twin.2.2.2 e he
  unfold evK
  rw [foldL_eq, h]

theorem fcAllK_eq (hlen : dTwin.all.length ≤ 2048) : fcAllK = fcAllK2 := by
  have hcl := bfsT_closed_len (N := 2 ^ 20) (keyN := fun c => c) (lc := dC)
    (lets := List.finRange 3) (fun c hc => hc) idC_lt hlen
  unfold fcAllK fcAllK2
  simp only []
  refine congrArg (List.map · (List.range 3)) (funext fun j => ?_)
  have hps : ∀ p ∈ dQ.flatMap (fun xw => (List.finRange 3).map fun k =>
      (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD [])),
      Nat.beq (evK dC p.1) (evK dC p.2) = true := by
    intro p hp
    obtain ⟨xw, hxw, hp⟩ := List.mem_flatMap.1 hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hp
    have hx := dQ_good hxw
    have h1 : evK dC (xw.2 ++ [k]) = mulC xw.1 (dC k) := by
      unfold evK at hx ⊢
      rw [foldL_eq] at hx ⊢
      rw [List.foldl_append, hx]
      rfl
    have hxw' : xw ∈ dTwin.all := by rw [dQ, List.mem_reverse] at hxw; exact hxw
    obtain ⟨e', he', hk'⟩ := hcl xw hxw' k (List.mem_finRange k)
    have hfind : (dQ.find? fun e => e.1 == mulC xw.1 (dC k)).isSome := by
      rw [List.find?_isSome]
      exact ⟨e', by rw [dQ, List.mem_reverse]; exact he', by simpa using hk'⟩
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hfind
    have hee := List.find?_some he
    have hem := List.mem_of_find?_eq_some he
    simp only [beq_iff_eq] at hee
    simp only [he, Option.map_some, Option.getD_some]
    rw [h1, dQ_good hem, hee, Nat.beq_refl]
  have hfil : ∀ (q : Nat × List (Fin 3) → Bool),
      (dQ.map Prod.snd).filter (fun w => q (evK dC w, w)) = (dQ.filter q).map Prod.snd := by
    intro q
    rw [List.filter_map]
    refine congrArg (List.map Prod.snd) (List.filter_congr fun e he => ?_)
    change q (evK dC e.2, e.2) = q e
    rw [dQ_good he]
  have eA := hfil fun e => maxL e.2 == j && isTtK e.1
  have eB := hfil fun e => maxL e.2 == j && isBtK e.1
  have eN := hfil fun e => maxL e.2 == j && !(Nat.beq e.1 idC)
  simp only at eA eB eN
  have eP : (dQ.flatMap fun xw => (List.finRange 3).map fun k =>
      (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD [])).filter
        (fun p => max (maxL p.1) (maxL p.2) == j && Nat.beq (evK dC p.1) (evK dC p.2)) =
      (dQ.flatMap fun xw => (List.finRange 3).map fun k =>
      (xw.2 ++ [k], ((dQ.find? fun e => e.1 == mulC xw.1 (dC k)).map Prod.snd).getD [])).filter
        (fun p => max (maxL p.1) (maxL p.2) == j) :=
    List.filter_congr fun p hp => by rw [hps p hp, Bool.and_true]
  rw [eA, eB, eN, eP]

section Tree

variable {L : List Nat} (hR : ReachL L) (h0 : L.contains 0 = false)
include hR

theorem tab_zero (h0 : L.contains 0 = false) : (mkCtx ()).tab 0 = tabC idC := by
  rw [tab_eq hR (by norm_num), tabK, if_neg (by rw [show 0 / 16 = 0 from rfl, h0]; simp)]
  rfl

include h0 in
theorem asg_eq {P : List Nat} (hP : ∀ p ∈ P, p ∈ (mkCtx ()).codes) :
    (mkCtx ()).asg P = fun k => tabC (asgK P k) := by
  funext k
  unfold Ctx8.asg asgK
  by_cases hk : k.val < P.length
  · rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk]
    exact tab_of_mem hR (hP _ (List.getElem_mem _))
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    exact tab_zero hR h0

omit hR in
theorem goodC_tabC (cs : FCConds) (u : Fin 3 → Nat) :
    (mkCtx ()).goodC cs (fun k => tabC (u k)) = goodCK cs u := by
  unfold Ctx8.goodC goodCK
  simp only [evT_tabC, isBt_tabC (evK_lt _ _), isTt_tabC (evK_lt _ _), idT_beq (evK_lt _ _),
    beq_tabC (evK_lt _ _) (evK_lt _ _)]
  rw [Bool.and_assoc (cs.wA.all _ && cs.wB.all _), Bool.and_assoc (cs.wA.all _ && cs.wB.all _),
    Bool.and_comm (cs.wN.all _)]

theorem conjEq_eq {e v r : Nat} (he : e ∈ (mkCtx ()).codes) (hv : v ∈ (mkCtx ()).codes)
    (hr : r ∈ (mkCtx ()).codes) : (mkCtx ()).conjEq e v r = conjEqK e v r := by
  unfold Ctx8.conjEq conjEqK
  rw [tab_of_mem hR he, tab_of_mem hR hv, tab_of_mem hR hr, compT_tabC, compT_tabC,
    beq_tabC (mulC_lt _ _) (mulC_lt _ _)]

theorem mkReps_step {C : List Nat} (hC : ∀ e ∈ C, e ∈ (mkCtx ()).codes) {v : Nat}
    (hv : v ∈ (mkCtx ()).codes) {acc : List Nat} (hacc : ∀ x ∈ acc, x ∈ (mkCtx ()).codes) :
    (acc.any fun r => C.any fun e => (mkCtx ()).conjEq e v r) =
      acc.any fun r => C.any fun e => conjEqK e v r :=
  any_mem_congr fun r hr => any_mem_congr fun e he' => conjEq_eq hR (hC e he') hv (hacc r hr)

theorem mkReps_eq {C : List Nat} (hC : ∀ e ∈ C, e ∈ (mkCtx ()).codes) (G : List Nat) :
    ∀ (acc : List Nat), (∀ x ∈ G, x ∈ (mkCtx ()).codes) → (∀ x ∈ acc, x ∈ (mkCtx ()).codes) →
      G.foldl (fun reps v => if reps.any fun r => C.any fun e => (mkCtx ()).conjEq e v r
        then reps else reps ++ [v]) acc =
      G.foldl (fun reps v => if reps.any fun r => C.any fun e => conjEqK e v r
        then reps else reps ++ [v]) acc := by
  induction G with
  | nil =>
    intro acc _ _
    rw [List.foldl_nil, List.foldl_nil]
  | cons v G ih =>
    intro acc hG hacc
    have hv := hG v List.mem_cons_self
    have hG' : ∀ x ∈ G, x ∈ (mkCtx ()).codes := fun x hx => hG x (List.mem_cons_of_mem _ hx)
    simp only [List.foldl_cons]
    rw [mkReps_step hR hC hv hacc]
    by_cases hc : (acc.any fun r => C.any fun e => conjEqK e v r) = true
    · rw [if_pos hc]
      exact ih acc hG' hacc
    · rw [if_neg hc]
      refine ih (acc ++ [v]) hG' ?_
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hacc x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        exact hv

omit hR in
theorem mkRepsK_sub {C : List Nat} : ∀ (G acc : List Nat) (x : Nat),
    x ∈ G.foldl (fun reps v => if reps.any fun r => C.any fun e => conjEqK e v r
      then reps else reps ++ [v]) acc → x ∈ acc ∨ x ∈ G
  | [], _, _, h => Or.inl h
  | v :: G, acc, x, h => by
    rw [List.foldl_cons] at h
    split at h
    · rcases mkRepsK_sub G acc x h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases mkRepsK_sub G (acc ++ [v]) x h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton] at h
          exact Or.inr (h ▸ List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h)

include h0 in
theorem fcTree_eq {dl : List Nat} (hdl : ∀ e ∈ dl, e ∈ (mkCtx ()).codes) (cs : List FCConds)
    (thc : List Nat) : ∀ (fuel : Nat) (P : List Nat), (∀ p ∈ P, p ∈ (mkCtx ()).codes) →
      (mkCtx ()).fcTree dl cs thc fuel P = fcTreeK dl cs thc fuel P
  | 0, _, _ => rfl
  | fuel + 1, P, hP => by
    unfold Ctx8.fcTree fcTreeK
    have hC : (dl.filter fun e => P.all fun p => commT ((mkCtx ()).tab e) ((mkCtx ()).tab p)) =
        dl.filter fun e => P.all fun p => commK e p := by
      refine List.filter_congr fun e he => all_mem_congr fun p hp => ?_
      rw [tab_of_mem hR (hdl e he), tab_of_mem hR (hP p hp), commT_tabC']
    have hG : (dl.filter fun v => (mkCtx ()).goodC (cs.getD P.length default)
        ((mkCtx ()).asg (P ++ [v]))) =
        dl.filter fun v => goodCK (cs.getD P.length default) (asgK (P ++ [v])) := by
      refine List.filter_congr fun v hv => ?_
      have hPv : ∀ p ∈ P ++ [v], p ∈ (mkCtx ()).codes := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hP p hp
        · rw [List.mem_singleton] at hp
          rw [hp]
          exact hdl v hv
      rw [asg_eq hR h0 hPv, goodC_tabC]
    simp only [hC, hG]
    set C := dl.filter fun e => P.all fun p => commK e p
    set G := dl.filter fun v => goodCK (cs.getD P.length default) (asgK (P ++ [v]))
    have hCv : ∀ e ∈ C, e ∈ (mkCtx ()).codes := fun e he => hdl e (List.mem_filter.1 he).1
    have hGv : ∀ v ∈ G, v ∈ (mkCtx ()).codes := fun v hv => hdl v (List.mem_filter.1 hv).1
    have hG'v : ∀ v ∈ (if G.contains (thc.getD P.length 0) = true then
        thc.getD P.length 0 :: G else G), v ∈ (mkCtx ()).codes := by
      intro v hv
      split at hv
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact hGv _ (List.contains_iff_mem.1 ‹_›)
        · exact hGv v hv
      · exact hGv v hv
    have hreps : (mkCtx ()).mkReps C (if G.contains (thc.getD P.length 0) = true then
        thc.getD P.length 0 :: G else G) = mkRepsK C (if G.contains (thc.getD P.length 0) = true
          then thc.getD P.length 0 :: G else G) :=
      mkReps_eq hR hCv _ [] hG'v (by simp)
    rw [hreps]
    set R := mkRepsK C (if G.contains (thc.getD P.length 0) = true then
        thc.getD P.length 0 :: G else G)
    have hRv : ∀ r ∈ R, r ∈ (mkCtx ()).codes := by
      intro r hr
      rcases mkRepsK_sub _ [] r hr with h | h
      · simp at h
      · exact hG'v r h
    have e1 : (G.all fun v => R.any fun r => C.any fun e => (mkCtx ()).conjEq e v r) =
        G.all fun v => R.any fun r => C.any fun e => conjEqK e v r :=
      all_mem_congr fun v hv => any_mem_congr fun r hr => any_mem_congr fun e he =>
        conjEq_eq hR (hCv e he) (hGv v hv) (hRv r hr)
    have e2 : (R.all fun r => (mkCtx ()).fcTree dl cs thc fuel (P ++ [r])) =
        R.all fun r => fcTreeK dl cs thc fuel (P ++ [r]) := by
      refine all_mem_congr fun r hr => fcTree_eq hdl cs thc fuel (P ++ [r]) ?_
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hP p hp
      · rw [List.mem_singleton] at hp
        rw [hp]
        exact hRv r hr
    rw [e1, e2]

end Tree

theorem fcCheck_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536)
    (h0 : L.contains 0 = false) {G : Nat} (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes)
    {D : List Nat} (hs : sortedK D = true) (hD : ∀ d ∈ D, validK G d = true ∧ normBK d = true)
    (hDL : ∀ m ∈ L, dLM D m = true) (hth : ∀ i : Fin 3, validK G (thC i) = true)
    (htree : fcTreeK D fcAllK thCodesK 3 [] = true) : fcCheck (mkCtx ()) = true := by
  unfold fcCheck
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [List.all_eq_true]
    intro i _
    have hv := hG _ (hth i)
    have hlt := ((mem_codes_iff hR).1 hv).1
    rw [thT_eq, codeOf_tabC hlt, tab_of_mem hR hv, beq_tabC hlt hlt]
    have hlt' : thC i < 1048576 := hlt
    simp [hlt']
  · have hdl := dList_eq hR hL hG hs hD hDL
    have hthc : thCodes = thCodesK := by
      unfold thCodes thCodesK
      refine congrArg (List.map · (List.finRange 3)) (funext fun i => ?_)
      rw [thT_eq, codeOf_tabC (thC_lt i)]
    rw [hdl, fcAll_eq, hthc, fcTree_eq hR h0 (fun d hd => hG d (hD d hd).1) fcAllK thCodesK 3 []
      (by simp)]
    exact htree

end CFSG.KC.M24L2
