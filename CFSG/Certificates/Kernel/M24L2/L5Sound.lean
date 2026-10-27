module

public import Certificates.Data.Kernel.M24L2.L5
public import CFSG.Certificates.Kernel.M24L2.L2FbSound

public section

namespace CFSG.KC.M24L2

open CFSG.Sporadic.Th.Native CFSG.CGT.M24R CFSG.CGT.L5R CFSG.KC.Enum

theorem betaT_eq (i : Fin 3) : betaT i = tabC (betaC i) := wTab_tabC _

theorem gamT_eq : gamT = tabC gamC := wTab_tabC _

theorem dT2_eq (i : Fin 2) : dT2 i = tabC (d2C i) := wTab_tabC _

theorem thT2_eq (i : Fin 2) : thT2 i = tabC (th2C i) := wTab_tabC _

theorem betaC_lt (i : Fin 3) : betaC i < 2 ^ 20 := cwK_lt _

theorem gamC_lt : gamC < 2 ^ 20 := cwK_lt _

theorem d2C_lt (i : Fin 2) : d2C i < 2 ^ 20 := cwK_lt _

theorem th2C_lt (i : Fin 2) : th2C i < 2 ^ 20 := cwK_lt _

theorem eightT_tabC (p q r : Nat) : eightT (tabC p) (tabC q) (tabC r) = (eightC p q r).map tabC := by
  unfold eightT eightC
  simp only [idT_tabC, compT_tabC, List.map_cons, List.map_nil]

theorem eightC_lt (p q r : Nat) (hp : p < 2 ^ 20) (hq : q < 2 ^ 20) (hr : r < 2 ^ 20) :
    ∀ a ∈ eightC p q r, a < 2 ^ 20 := by
  intro a ha
  unfold eightC at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · exact hp
  · exact hq
  · exact mulC_lt _ _
  · exact hr
  · exact mulC_lt _ _
  · exact mulC_lt _ _
  · exact mulC_lt _ _

theorem b8List_eq : b8List = b8C.map tabC := by
  unfold b8List b8C
  rw [betaT_eq, betaT_eq, betaT_eq, eightT_tabC]

theorem b8C_lt : ∀ a ∈ b8C, a < 2 ^ 20 :=
  eightC_lt _ _ _ (betaC_lt 0) (betaC_lt 1) (betaC_lt 2)

theorem isB8_tabC {x : Nat} (hx : x < 2 ^ 20) : isB8 (tabC x) = isB8K x := by
  unfold isB8 isB8K
  rw [b8List_eq, contains_tabC _ b8C_lt hx]

theorem normAll_tabC (L : List Nat) (x : Nat) : normAll (L.map tabC) (tabC x) = normAllK L x := by
  unfold normAll normAllK
  rw [List.all_map]
  refine congrArg (List.all L) (funext fun p => ?_)
  change (conjIn (tabC x) (tabC p) (L.map tabC) && conjInR (tabC x) (tabC p) (L.map tabC)) = _
  rw [conjIn_tabC, conjInR_tabC]

theorem nodup_tabC {L : List Nat} (hL : ∀ a ∈ L, a < 2 ^ 20) : (L.map tabC).Nodup ↔ L.Nodup := by
  constructor
  · exact List.Nodup.of_map _
  · intro h
    exact h.map_on fun a ha b hb e => tabC_inj (hL a ha) (hL b hb) e

theorem all_map_tabC {L : List Nat} {f : Table → Bool} {g : Nat → Bool}
    (h : ∀ x ∈ L, f (tabC x) = g x) : (L.map tabC).all f = L.all g := by
  rw [List.all_map]
  exact all_mem_congr fun x hx => h x hx

theorem bChecks_eq (L : List Nat) (hL : ∀ a ∈ L, a < 2 ^ 20) :
    (decide (L.map tabC).Nodup && (L.map tabC).all (fun X => compT 16 X X == idT 16) &&
      (L.map tabC).all (fun X => (L.map tabC).all fun Y => (L.map tabC).contains (compT 16 X Y)) &&
      (L.map tabC).tail.all fun X => !((mkCtx ()).isTt X)) =
    (decide L.Nodup && L.all (fun x => Nat.beq (mulC x x) idC) &&
      L.all (fun x => L.all fun y => L.contains (mulC x y)) && L.tail.all fun x => !(isTtK x)) := by
  have e1 : decide (L.map tabC).Nodup = decide L.Nodup := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact nodup_tabC hL
  have e2 : (L.map tabC).all (fun X => compT 16 X X == idT 16) =
      L.all fun x => Nat.beq (mulC x x) idC :=
    all_map_tabC fun x _ => by rw [compT_tabC, idT_beq (mulC_lt x x)]
  have e3 : ((L.map tabC).all fun X => (L.map tabC).all fun Y =>
      (L.map tabC).contains (compT 16 X Y)) = L.all fun x => L.all fun y => L.contains (mulC x y) :=
    all_map_tabC fun x _ => all_map_tabC fun y _ => by
      rw [compT_tabC, contains_tabC _ hL (mulC_lt x y)]
  have e4 : ((L.map tabC).tail.all fun X => !((mkCtx ()).isTt X)) =
      L.tail.all fun x => !(isTtK x) := by
    rw [← List.map_tail]
    exact all_map_tabC fun x hx => by rw [isTt_tabC (hL x (List.mem_of_mem_tail hx))]
  rw [e1, e2, e3, e4]

theorem bCheckL_eq : bCheckL (mkCtx ()) = bCheckLK := by
  unfold bCheckL bCheckLK
  rw [b8List_eq, gamT_eq, isTt_tabC gamC_lt, bChecks_eq b8C b8C_lt]

theorem ev2_foldl (u : Fin 2 → Nat) (w : List (Fin 2)) : ∀ c : Nat,
    w.foldl (fun X k => compT 16 X (tabC (u k))) (tabC c) =
      tabC (w.foldl (fun c k => mulC c (u k)) c) := by
  induction w with
  | nil => intro c; rfl
  | cons k w ih =>
    intro c
    rw [List.foldl_cons, List.foldl_cons, compT_tabC, ih]

theorem evT2_tabC (u : Fin 2 → Nat) (w : List (Fin 2)) :
    evT2 (fun k => tabC (u k)) w = tabC (ev2K u w) := by
  unfold evT2 ev2K
  rw [idT_tabC, ev2_foldl, foldL_eq]

theorem ev2K_lt (u : Fin 2 → Nat) (w : List (Fin 2)) : ev2K u w < 2 ^ 20 := by
  unfold ev2K
  rw [foldL_eq]
  exact foldl_mulC_lt _ w _ (by decide)

theorem evT2_dT2 (w : List (Fin 2)) : evT2 dT2 w = tabC (ev2K d2C w) := by
  rw [show dT2 = fun k => tabC (d2C k) from funext dT2_eq, evT2_tabC]

theorem evT2_thT2 (w : List (Fin 2)) : evT2 thT2 w = tabC (ev2K th2C w) := by
  rw [show thT2 = fun k => tabC (th2C k) from funext thT2_eq, evT2_tabC]

theorem wCheckL_eq : wCheckL (mkCtx ()) = wCheckLK := by
  unfold wCheckL wCheckLK
  simp only [evT2_dT2, beq_tabC (ev2K_lt _ _) (ev2K_lt _ _), idT_beq (ev2K_lt _ _),
    isTt_tabC (ev2K_lt _ _), isB8_tabC (ev2K_lt _ _), commCount_tabC]
  rw [dT2_eq, idT_beq (d2C_lt 0), show wTab nzW10 = tabC nzC from wTab_tabC _, b8List_eq,
    conjIn_tabC]

section Maps

variable {L : List Nat} (hR : ReachL L)
include hR

theorem conjVia_of {p x : Nat} (hp : p < 2 ^ 20) (hx : x < 2 ^ 20)
    (h : ∃ n ∈ (mkCtx ()).codes, mulC n p = mulC x n) :
    conjVia (mkCtx ()) (conjMap (mkCtx ()) (mkCtx ()).codes (tabC p)) (tabC p) (tabC x) = true := by
  obtain ⟨n0, hn0c, hn0⟩ := h
  have hkey : ∀ n ∈ (mkCtx ()).codes, codeOf (compT 16 (compT 16 ((mkCtx ()).tab n) (tabC p))
      (invT 16 ((mkCtx ()).tab n))) = conjKey n (tabC p) := by
    intro n hn
    rw [tab_of_mem hR hn]
    rfl
  obtain ⟨n', hn', hk', hfm⟩ := foldSet_get (key := fun n => codeOf (compT 16 (compT 16
    ((mkCtx ()).tab n) (tabC p)) (invT 16 ((mkCtx ()).tab n)))) (mkCtx ()).codes
    (Array.replicate 1048576 0) (by simpa using hx)
    ⟨n0, hn0c, by rw [hkey n0 hn0c]; exact (conjKey_eq hR hn0c hp hx).2 hn0⟩
  rw [hkey n' hn'] at hk'
  have hconj := (conjKey_eq hR hn' hp hx).1 hk'
  have hfm' : (conjMap (mkCtx ()) (mkCtx ()).codes (tabC p))[x]! = n' := hfm
  unfold conjVia
  rw [codeOf_tabC hx, hfm']
  change (decide (n' < 1048576) && compT 16 ((mkCtx ()).tab n') (tabC p) ==
    compT 16 (tabC x) ((mkCtx ()).tab n')) = true
  rw [tab_of_mem hR hn', compT_tabC, compT_tabC,
    beq_tabC (mulC_lt _ _) (mulC_lt _ _), hconj]
  have hn'lt : n' < 1048576 := ((mem_codes_iff hR).1 hn').1
  simp [hn'lt]

theorem conjKeyD_eq {e r x : Nat} (he : e ∈ (mkCtx ()).codes) (hr : r < 2 ^ 20) (hx : x < 2 ^ 20) :
    codeOf (compT 16 (compT 16 (invT 16 (tabC e)) (tabC r)) (tabC e)) = x ↔
      mulC e x = mulC r e := by
  obtain ⟨i, hi, hinv, h1, h2⟩ := inv_of_mem hR he
  have hel := ((mem_codes_iff hR).1 he).1
  rw [hinv, compT_tabC, compT_tabC, codeOf_tabC (mulC_lt _ _)]
  constructor
  · intro h
    rw [← h, ← mulC_assoc, ← mulC_assoc, h1, idC_mulC hr]
  · intro h
    rw [mulC_assoc, ← h, ← mulC_assoc, h2, idC_mulC hx]

theorem viaD_of {dl : List Nat} (hdl : ∀ e ∈ dl, e ∈ (mkCtx ()).codes ∧ normAllK b8C e = true)
    {r x : Nat} (hr : r < 2 ^ 20) (hx : x < 2 ^ 20) (h : ∃ e ∈ dl, mulC e x = mulC r e) :
    viaD (mkCtx ()) (conjMapD (mkCtx ()) dl (tabC r)) (tabC r) (tabC x) = true := by
  obtain ⟨e0, he0, he0x⟩ := h
  have hkey : ∀ e ∈ dl, codeOf (compT 16 (compT 16 (invT 16 ((mkCtx ()).tab e)) (tabC r))
      ((mkCtx ()).tab e)) = codeOf (compT 16 (compT 16 (invT 16 (tabC e)) (tabC r)) (tabC e)) := by
    intro e he
    rw [tab_of_mem hR (hdl e he).1]
  obtain ⟨e', he', hk', hfm⟩ := foldSet_get (key := fun e => codeOf (compT 16 (compT 16
    (invT 16 ((mkCtx ()).tab e)) (tabC r)) ((mkCtx ()).tab e))) dl
    (Array.replicate 1048576 0) (by simpa using hx)
    ⟨e0, he0, by rw [hkey e0 he0]; exact (conjKeyD_eq hR (hdl e0 he0).1 hr hx).2 he0x⟩
  rw [hkey e' he'] at hk'
  have hconj := (conjKeyD_eq hR (hdl e' he').1 hr hx).1 hk'
  have hfm' : (conjMapD (mkCtx ()) dl (tabC r))[x]! = e' := hfm
  unfold viaD
  rw [codeOf_tabC hx, hfm']
  change (decide (e' < 1048576) && normAll b8List ((mkCtx ()).tab e') &&
    compT 16 ((mkCtx ()).tab e') (tabC x) == compT 16 (tabC r) ((mkCtx ()).tab e')) = true
  rw [tab_of_mem hR (hdl e' he').1, b8List_eq, normAll_tabC, compT_tabC,
    compT_tabC, beq_tabC (mulC_lt _ _) (mulC_lt _ _), hconj, (hdl e' he').2]
  have he'lt : e' < 1048576 := ((mem_codes_iff hR).1 (hdl e' he').1).1
  simp [he'lt]

end Maps

theorem sq_ne_of_lin {m v : Nat} (hv : v < 16) (hl : sqLin m = false) :
    Nat.beq (mulC (v + 16 * m) (v + 16 * m)) idC = false := by
  rw [Bool.eq_false_iff]
  intro h1
  have h2 := mulC_lin_eq (Nat.eq_of_beq_eq_true h1)
  rw [show (v + 16 * m) / 16 = m by omega] at h2
  unfold sqLin at hl
  change Nat.beq (mulC (16 * m) (16 * m)) idC = false at hl
  rw [h2] at hl
  simp at hl

theorem allN_letN {f : Nat → Bool} {m : Nat}
    (h : allN 16 (fun v => letN (Nat.add v (Nat.mul (nat_lit 16) m)) f) = true) :
    ∀ v < 16, f (v + 16 * m) = true := by
  intro v hv
  rw [CFSG.KS.Raw.Orb.allN_iff] at h
  have := h v hv
  rw [letN_eq] at this
  exact this

theorem faLM_spec {G : Nat} {W1 W2 : List (Nat × Nat)} {m : Nat} (h : faLM G W1 W2 m = true) :
    ∀ v < 16, faLBody G W1 W2 (v + 16 * m) = true := by
  intro v hv
  unfold faLM at h
  rcases hl : sqLin m with _ | _
  · unfold faLBody
    rw [sq_ne_of_lin hv hl]
  · rw [hl] at h
    exact allN_letN h v hv

theorem faCheckL_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    {W1 W2 : List (Nat × Nat)} (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes)
    (h : ∀ m ∈ L, faLM G W1 W2 m = true) : faCheckL (mkCtx ()) = true := by
  unfold faCheckL
  simp only [List.all_eq_true]
  intro c hc
  have hlt := ((mem_codes_iff hR).1 hc).1
  have hb := forall_codes hR hL (P := fun c => faLBody G W1 W2 c = true)
    (fun m hm v hv => faLM_spec (h m hm) v hv) c hc
  rw [tab_of_mem hR hc, compT_tabC, idT_beq (mulC_lt c c), isTt_tabC hlt, commCount_tabC]
  unfold faLBody at hb
  rcases h1 : Nat.beq (mulC c c) idC with _ | _
  · simp
  rcases h2 : isTtK c with _ | _
  · rcases h3 : commCountK c == 8 with _ | _
    · simp
    · rw [h1, h2, h3] at hb
      change (witK G (betaC 0) W1 c || witK G gamC W2 c) = true at hb
      rw [Bool.or_eq_true] at hb
      rcases hb with hw | hw
      · obtain ⟨n, hv, hn⟩ := witK_spec hw
        rw [betaT_eq, conjVia_of hR (betaC_lt 0) hlt ⟨n, hG n hv, hn⟩]
        simp
      · obtain ⟨n, hv, hn⟩ := witK_spec hw
        rw [gamT_eq, conjVia_of hR gamC_lt hlt ⟨n, hG n hv, hn⟩]
        simp
  · simp

theorem candL_tabC {p x : Nat} (hp : p < 2 ^ 20) (hx : x < 2 ^ 20) :
    candL (mkCtx ()) (tabC p) (tabC x) = candLK p x := by
  unfold candL candLK
  have e : ((List.range 16).all fun k => commT (mkCtx ()).tt[k]! (tabC x) ==
      commT (mkCtx ()).tt[k]! (tabC p)) =
      (List.range 16).all fun k => commK (ttC k) x == commK (ttC k) p :=
    all_mem_congr fun k hk => by rw [ctx_tt_tabC (range16 hk), commT_tabC', commT_tabC']
  rw [compT_tabC, idT_beq (mulC_lt x x), commT_tabC', isTt_tabC hx, beq_tabC hx hp, compT_tabC,
    isTt_tabC (mulC_lt p x), e]

theorem pairPre_tabC {p x y : Nat} (hp : p < 2 ^ 20) (hx : x < 2 ^ 20) (hy : y < 2 ^ 20) :
    pairPre (mkCtx ()) (tabC p) (tabC x) (tabC y) = pairPreK p x y := by
  unfold pairPre pairPreK
  rw [commT_tabC', beq_tabC hy hp, beq_tabC hy hx, compT_tabC, beq_tabC hy (mulC_lt p x),
    compT_tabC, candL_tabC hp (mulC_lt x y), compT_tabC, candL_tabC hp (mulC_lt _ _)]

theorem refL_tabC (L : List Nat) (x y z : Nat) :
    refL (L.map tabC) (tabC x) (tabC y) (tabC z) = refLK L x y z := by
  unfold refL refLK
  rw [conjIn_tabC, conjIn_tabC]

theorem candM_spec {p : Nat} {Cd : List Nat} {m : Nat} (h : candM p Cd m = true) :
    ∀ v < 16, candLK p (v + 16 * m) = true → v + 16 * m ∈ Cd := by
  intro v hv hc
  unfold candM at h
  rcases hl : sqLin m with _ | _
  · unfold candLK at hc
    rw [sq_ne_of_lin hv hl] at hc
    simp at hc
  · rw [hl] at h
    have := allN_letN h v hv
    change bIf(candLK p (v + 16 * m), Cd.contains (v + 16 * m), true) = true at this
    rw [hc] at this
    exact List.contains_iff_mem.1 this

theorem fbCheckL_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) {p : Nat} (hp : p < 2 ^ 20)
    {allowB : Bool} {Cd : List Nat} {W : List ((Nat × Nat) × Nat)}
    (hc : ∀ m ∈ L, candM p Cd m = true) (hfb : fbLK G p allowB Cd W = true) :
    fbCheckL (mkCtx ()) (tabC p) allowB = true := by
  unfold fbCheckL
  simp only [List.all_eq_true]
  have hcd : ∀ c ∈ (mkCtx ()).codes.filter (fun c => candL (mkCtx ()) (tabC p) ((mkCtx ()).tab c)),
      c ∈ (mkCtx ()).codes ∧ c ∈ Cd := by
    intro c hc'
    obtain ⟨hcc, hcand⟩ := List.mem_filter.1 hc'
    refine ⟨hcc, ?_⟩
    rw [tab_of_mem hR hcc, candL_tabC hp ((mem_codes_iff hR).1 hcc).1] at hcand
    exact forall_codes hR hL (P := fun c => candLK p c = true → c ∈ Cd)
      (fun m hm v hv => candM_spec (hc m hm) v hv) c hcc hcand
  intro c hc1 c' hc2
  obtain ⟨hcc1, hcd1⟩ := hcd c hc1
  obtain ⟨hcc2, hcd2⟩ := hcd c' hc2
  have hx := ((mem_codes_iff hR).1 hcc1).1
  have hy := ((mem_codes_iff hR).1 hcc2).1
  have hpair := hfb
  unfold fbLK at hpair
  rw [allL_eq, List.all_eq_true] at hpair
  have hpair' := hpair c hcd1
  rw [allL_eq, List.all_eq_true] at hpair'
  have hb := hpair' c' hcd2
  unfold fbPairK at hb
  rw [tab_of_mem hR hcc1, tab_of_mem hR hcc2, pairPre_tabC hp hx hy, eightT_tabC,
    isB8_tabC hx, isB8_tabC hy]
  have hnd : decide ((eightC p c c').map tabC).Nodup = decide (eightC p c c').Nodup := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact nodup_tabC (eightC_lt _ _ _ hp hx hy)
  rw [hnd]
  rcases h1 : pairPreK p c c' with _ | _
  · simp
  rw [h1] at hb
  change (decide (eightC p c c').Nodup && ((allowB && isB8K c && isB8K c') ||
    fbLWit G p W c c')) = true at hb
  rw [Bool.and_eq_true, Bool.or_eq_true] at hb
  obtain ⟨hb1, hb2⟩ := hb
  simp only [Bool.not_true, Bool.false_or, hb1, Bool.true_and]
  rcases hb2 with hb2 | hb2
  · rw [hb2]
    rfl
  · unfold fbLWit at hb2
    rw [anyL_eq, List.any_eq_true] at hb2
    obtain ⟨e, _, he⟩ := hb2
    simp only [Bool.and_eq_true, Nat.beq_eq] at he
    obtain ⟨⟨⟨⟨_, _⟩, hv⟩, hcomm⟩, hrefl⟩ := he
    have hyc := hG e.2 hv
    rw [Bool.or_eq_true, List.any_eq_true]
    right
    refine ⟨e.2, List.mem_filter.2 ⟨hyc, ?_⟩, ?_⟩
    · rw [tab_of_mem hR hyc, commT_tabC']
      exact hcomm
    · have h := (refL_tabC (eightC p c c') c c' e.2).trans hrefl
      rw [← tab_of_mem hR hyc] at h
      exact h

theorem dListL_mem {c : Nat} : c ∈ dListL (mkCtx ()) ↔
    c ∈ (mkCtx ()).codes ∧ normAll b8List ((mkCtx ()).tab c) = true := by
  unfold dListL
  rw [List.mem_filter]

theorem dML_spec {m : Nat} (h : dML m = true) : ∀ v < 16, dBodyL (v + 16 * m) = true := by
  intro v hv
  unfold dML at h
  rcases hl : dLinL m with _ | _
  · unfold dBodyL
    have : (!(commK (v + 16 * m) (d2C 0)) || !(commK (v + 16 * m) (d2C 1)) ||
        Nat.beq (v + 16 * m) idC) = true := by
      rcases h0 : commK (v + 16 * m) (d2C 0) with _ | _
      · rfl
      rcases h1 : commK (v + 16 * m) (d2C 1) with _ | _
      · rfl
      have k0 := commK_lin h0
      have k1 := commK_lin h1
      rw [show (v + 16 * m) / 16 = m by omega] at k0 k1
      unfold dLinL at hl
      change (commK (16 * m) (16 * (d2C 0 >>> 4)) && commK (16 * m) (16 * (d2C 1 >>> 4))) =
        false at hl
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, k0, k1] at hl
      simp at hl
    rw [this]
    cases normAllK b8C (v + 16 * m) <;> rfl
  · rw [hl] at h
    exact allN_letN h v hv

theorem dCheckL_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) (h1 : dPart1L = true)
    (h2 : ∀ m ∈ L, dML m = true) (h3 : dPart3L = true) : dCheckL (mkCtx ()) = true := by
  unfold dCheckL
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold dPart1L at h1
    rw [← h1]
    refine all_mem_congr fun i _ => ?_
    rw [dT2_eq, thT2_eq, b8List_eq, normAll_tabC, normAll_tabC]
  · rw [List.all_eq_true]
    intro z hz
    obtain ⟨hzc, hzn⟩ := dListL_mem.1 hz
    have hzl := ((mem_codes_iff hR).1 hzc).1
    have hb := forall_codes hR hL (P := fun c => dBodyL c = true)
      (fun m hm v hv => dML_spec (h2 m hm) v hv) z hzc
    rw [tab_of_mem hR hzc] at hzn ⊢
    rw [b8List_eq, normAll_tabC] at hzn
    unfold dBodyL at hb
    rw [hzn] at hb
    rw [dT2_eq, dT2_eq]
    change (!commT (tabC z) (tabC (d2C 0)) || !commT (tabC z) (tabC (d2C 1)) ||
      tabC z == idT 16) = true
    rw [commT_tabC', commT_tabC', idT_tabC, beq_tabC hzl (by decide)]
    exact hb
  · unfold dPart3L at h3
    rw [← h3]
    refine all_mem_congr fun i _ => ?_
    rw [evT2_dT2, evT2_thT2, thT2_eq, dT2_eq, beq_tabC (ev2K_lt _ _) (th2C_lt i),
      beq_tabC (ev2K_lt _ _) (d2C_lt i)]

theorem b8_beta0 : betaC 0 ∈ b8C := by
  unfold b8C eightC
  simp

theorem dLinB8_of {c : Nat} (h : normAllK b8C c = true) : dLinB8 (c / 16) = true := by
  unfold normAllK at h
  rw [List.all_eq_true] at h
  have h0 := h _ b8_beta0
  unfold conjInK at h0
  simp only [Bool.and_eq_true, List.any_eq_true, Nat.beq_eq] at h0
  obtain ⟨k, hk, hke⟩ := h0.1
  unfold dLinB8
  rw [List.any_eq_true]
  refine ⟨k, hk, ?_⟩
  rw [Nat.beq_eq]
  have e1 := mulC_div16 c (betaC 0)
  have e2 := mulC_div16 k c
  rw [hke] at e1
  have h3 := mulC_mod16_lin (c / 16) (betaC 0 / 16)
  have h4 := mulC_mod16_lin (k / 16) (c / 16)
  change mulC (16 * (c / 16)) (16 * (betaC 0 >>> 4)) = mulC (16 * (k >>> 4)) (16 * (c / 16))
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  change mulC (16 * (c / 16)) (16 * (betaC 0 / 16)) = mulC (16 * (k / 16)) (16 * (c / 16))
  omega

theorem s0M_spec {G : Nat} {W : List (Nat × Nat × Nat)} {m : Nat} (h : s0M G W m = true) :
    ∀ v < 16, s0Body G W (v + 16 * m) = true := by
  intro v hv
  unfold s0M at h
  rcases hl : dLinB8 m with _ | _
  · unfold s0Body
    rcases hn : normAllK b8C (v + 16 * m) with _ | _
    · rfl
    · have := dLinB8_of hn
      rw [show (v + 16 * m) / 16 = m by omega, hl] at this
      simp at this
  · rw [hl] at h
    exact allN_letN h v hv

theorem s1M_spec {G : Nat} {W : List ((Nat × Nat) × Nat)} {m : Nat} (h : s1M G W m = true) :
    ∀ v < 16, (s1Body G W 0 (th2C 0) (v + 16 * m) && s1Body G W 1 rep2Code (v + 16 * m)) = true := by
  intro v hv
  unfold s1M at h
  rcases hl : dLinB8 m with _ | _
  · unfold s1Body
    rcases hn : normAllK b8C (v + 16 * m) with _ | _
    · rfl
    · have := dLinB8_of hn
      rw [show (v + 16 * m) / 16 = m by omega, hl] at this
      simp at this
  · rw [hl] at h
    exact allN_letN h v hv

theorem evT2_const (c : Nat) (w : List (Fin 2)) :
    evT2 (fun _ => tabC c) w = tabC (ev2K (fun _ => c) w) :=
  evT2_tabC (fun _ => c) w

theorem evT2_vec (r c : Nat) (w : List (Fin 2)) :
    evT2 ![tabC r, tabC c] w = tabC (ev2K ![r, c] w) := by
  have e : (![tabC r, tabC c] : Fin 2 → Table) = fun k => tabC (![r, c] k) := by
    funext k
    fin_cases k <;> rfl
  rw [e, evT2_tabC]

theorem powT_tabC (r : Nat) : ∀ k, powT 16 k (tabC r) = tabC (powK r k)
  | 0 => by rw [powT, powK, idT_tabC]
  | k + 1 => by rw [powT, powK, powT_tabC r k, compT_tabC]

theorem goodL_tabC (fm : Array Nat) (r c : Nat) :
    goodL (mkCtx ()) fm ![tabC r, tabC c] =
      (first4K ![r, c] && !(conjVia (mkCtx ()) fm (betaT 0) (tabC (ev2K ![r, c] z2DW)))) := by
  unfold goodL first4K
  simp only [evT2_vec, beq_tabC (ev2K_lt _ _) (ev2K_lt _ _), idT_beq (ev2K_lt _ _),
    isTt_tabC (ev2K_lt _ _), isB8_tabC (ev2K_lt _ _), commCount_tabC]

theorem disj_tabC {r c : Nat} (hr : r < 2 ^ 20) :
    (tabC r == tabC (th2C 0) && (List.range 7).any fun k =>
      compT 16 (powT 16 k (tabC (th2C 0))) (tabC c) ==
        compT 16 (thT2 1) (powT 16 k (tabC (th2C 0)))) = disjK r c := by
  unfold disjK
  have e : ((List.range 7).any fun k => compT 16 (powT 16 k (tabC (th2C 0))) (tabC c) ==
      compT 16 (thT2 1) (powT 16 k (tabC (th2C 0)))) =
      (List.range 7).any fun k =>
        Nat.beq (mulC (powK (th2C 0) k) c) (mulC (th2C 1) (powK (th2C 0) k)) :=
    any_mem_congr fun k _ => by
      rw [powT_tabC, thT2_eq, compT_tabC, compT_tabC, beq_tabC (mulC_lt _ _) (mulC_lt _ _)]
  rw [beq_tabC hr (th2C_lt 0), e]

theorem stage0L_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) (hrep : rep2Code ∈ (mkCtx ()).codes)
    {dl : List Nat} (hdl : ∀ e, e ∈ dl ↔ e ∈ (mkCtx ()).codes ∧ normAllK b8C e = true)
    {W : List (Nat × Nat × Nat)} (h : ∀ m ∈ L, s0M G W m = true) :
    stage0L (mkCtx ()) dl (thT2 0) ((mkCtx ()).tab rep2Code) = true := by
  have hdl1 : ∀ e ∈ dl, e ∈ (mkCtx ()).codes ∧ normAllK b8C e = true := fun e he => (hdl e).1 he
  have hr2 := ((mem_codes_iff hR).1 hrep).1
  unfold stage0L
  rw [tab_of_mem hR hrep, thT2_eq 0]
  simp only [List.all_eq_true]
  intro v hv
  obtain ⟨hvc, hvn⟩ := hdl1 v hv
  have hvl := ((mem_codes_iff hR).1 hvc).1
  have hb := forall_codes hR hL (P := fun c => s0Body G W c = true)
    (fun m hm u hu => s0M_spec (h m hm) u hu) v hvc
  unfold s0Body at hb
  rw [hvn] at hb
  rw [tab_of_mem hR hvc, idT_beq hvl, evT2_const, idT_beq (ev2K_lt _ _)]
  rcases h1 : Nat.beq v idC with _ | _
  · rcases h2 : Nat.beq (ev2K (fun _ => v) sevenW) idC with _ | _
    · simp only [Bool.not_false, Bool.or_true, Bool.true_or]
    · rw [h1, h2] at hb
      change s0Wit G W v = true at hb
      unfold s0Wit at hb
      rw [anyL_eq, List.any_eq_true] at hb
      obtain ⟨e, _, he⟩ := hb
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at he
      obtain ⟨⟨⟨_, hvalid⟩, hnorm⟩, hcl⟩ := he
      have hed : e.2.1 ∈ dl := (hdl _).2 ⟨hG _ hvalid, hnorm⟩
      rcases h3 : Nat.beq e.2.2 1 with _ | _
      · rw [h3] at hcl
        change Nat.beq (mulC e.2.1 v) (mulC rep2Code e.2.1) = true at hcl
        have k := viaD_of hR hdl1 hr2 hvl ⟨e.2.1, hed, Nat.eq_of_beq_eq_true hcl⟩
        simp only [k, Bool.or_true]
      · rw [h3] at hcl
        change Nat.beq (mulC e.2.1 v) (mulC (th2C 0) e.2.1) = true at hcl
        have k := viaD_of hR hdl1 (th2C_lt 0) hvl ⟨e.2.1, hed, Nat.eq_of_beq_eq_true hcl⟩
        simp only [k, Bool.or_true, Bool.true_or]
  · simp only [Bool.true_or]

theorem s1Body_sound {L : List Nat} (hR : ReachL L) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) {W : List ((Nat × Nat) × Nat)}
    {i r v : Nat} (hr : r < 2 ^ 20) (hvn : normAllK b8C v = true)
    (hb : s1Body G W i r v = true) :
    (!(goodL (mkCtx ()) (conjMap (mkCtx ()) (mkCtx ()).codes (betaT 0)) ![tabC r, tabC v]) ||
      (tabC r == tabC (th2C 0) && (List.range 7).any fun k =>
        compT 16 (powT 16 k (tabC (th2C 0))) (tabC v) ==
          compT 16 (thT2 1) (powT 16 k (tabC (th2C 0))))) = true := by
  rw [goodL_tabC, disj_tabC hr]
  unfold s1Body at hb
  rw [hvn] at hb
  rcases h1 : first4K ![r, v] with _ | _
  · simp only [Bool.false_and, Bool.not_false, Bool.true_or]
  rcases h2 : disjK r v with _ | _
  · rw [h1, h2] at hb
    change s1Wit G W i r v = true at hb
    unfold s1Wit at hb
    rw [anyL_eq, List.any_eq_true] at hb
    obtain ⟨e, _, he⟩ := hb
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at he
    obtain ⟨⟨⟨_, _⟩, hvalid⟩, hconj⟩ := he
    rw [betaT_eq, conjVia_of hR (betaC_lt 0) (ev2K_lt _ _)
      ⟨e.2, hG _ hvalid, Nat.eq_of_beq_eq_true hconj⟩]
    simp only [Bool.not_true, Bool.and_false, Bool.not_false, Bool.true_or]
  · simp only [Bool.and_true, Bool.or_true]

theorem stage1L_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) (hrep : rep2Code ∈ (mkCtx ()).codes)
    {dl : List Nat} (hdl : ∀ e, e ∈ dl ↔ e ∈ (mkCtx ()).codes ∧ normAllK b8C e = true)
    {W : List ((Nat × Nat) × Nat)} (h : ∀ m ∈ L, s1M G W m = true) :
    stage1L (mkCtx ()) dl (conjMap (mkCtx ()) (mkCtx ()).codes (betaT 0)) (thT2 0)
      ((mkCtx ()).tab rep2Code) = true := by
  have hb := forall_codes hR hL
    (P := fun c => (s1Body G W 0 (th2C 0) c && s1Body G W 1 rep2Code c) = true)
    (fun m hm v hv => s1M_spec (h m hm) v hv)
  have hr2 := ((mem_codes_iff hR).1 hrep).1
  unfold stage1L
  rw [tab_of_mem hR hrep, thT2_eq 0]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro v hv
    obtain ⟨hvc, hvn⟩ := (hdl v).1 hv
    have hb' := hb v hvc
    rw [Bool.and_eq_true] at hb'
    rw [tab_of_mem hR hvc]
    exact s1Body_sound hR hG (th2C_lt 0) hvn hb'.1
  · intro v hv
    obtain ⟨hvc, hvn⟩ := (hdl v).1 hv
    have hb' := hb v hvc
    rw [Bool.and_eq_true] at hb'
    rw [tab_of_mem hR hvc]
    exact s1Body_sound hR hG hr2 hvn hb'.2

theorem fcCheckL_of {L : List Nat} (hR : ReachL L) (hL : ∀ m ∈ L, m < 65536) {G : Nat}
    (hG : ∀ n, validK G n = true → n ∈ (mkCtx ()).codes) (hrep : validK G rep2Code = true)
    {W0 : List (Nat × Nat × Nat)} {W1 : List ((Nat × Nat) × Nat)}
    (h0 : ∀ m ∈ L, s0M G W0 m = true) (h1 : ∀ m ∈ L, s1M G W1 m = true) :
    fcCheckL (mkCtx ()) = true := by
  have hrc := hG _ hrep
  have hdl : ∀ e, e ∈ (mkCtx ()).codes.filter (fun c => normAll b8List ((mkCtx ()).tab c)) ↔
      e ∈ (mkCtx ()).codes ∧ normAllK b8C e = true := by
    intro e
    rw [List.mem_filter]
    constructor
    · rintro ⟨hec, hen⟩
      rw [tab_of_mem hR hec, b8List_eq, normAll_tabC] at hen
      exact ⟨hec, hen⟩
    · rintro ⟨hec, hen⟩
      rw [tab_of_mem hR hec, b8List_eq, normAll_tabC]
      exact ⟨hec, hen⟩
  unfold fcCheckL
  simp only [Bool.and_eq_true]
  exact ⟨stage0L_of hR hL hG hrc hdl h0, stage1L_of hR hL hG hrc hdl h1⟩

end CFSG.KC.M24L2
