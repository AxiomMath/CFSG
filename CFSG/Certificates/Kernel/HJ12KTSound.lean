module

public import Certificates.Data.Kernel.HJ12KT
public import CFSG.Certificates.Kernel.HJ12KSound

public section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.Quasithin.H13.MatNCert CFSG.GammaU.Native
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

theorem bitQ_eq (m n : ℕ) : bitQ m n = m.testBit n := by
  change Nat.beq ((m >>> n) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  exact Bool.eq_iff_iff.2 (by rw [Nat.beq_eq, decide_eq_true_iff])

theorem beq_symm (a b : ℕ) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.2 (by simp only [beq_iff_eq]; exact eq_comm)

theorem testBit_ins (m t k : ℕ) :
    (Nat.lor m (Nat.shiftLeft 1 t)).testBit k = (t == k || m.testBit k) := by
  change (m ||| 1 <<< t).testBit k = _
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_comm]
  by_cases h : t = k <;> simp [h]

theorem maskOf_testBit : ∀ (L : List ℕ) (m s : ℕ),
    (maskOf m L).testBit s = (m.testBit s || L.contains s)
  | [], m, s => by simp [maskOf]
  | x :: L, m, s => by
    change (maskOf (Nat.lor m (Nat.shiftLeft 1 x)) L).testBit s = _
    rw [maskOf_testBit L, testBit_ins, List.contains_cons, beq_symm x s]
    cases m.testBit s <;> cases s == x <;> cases L.contains s <;> rfl

theorem contains_bitQ (L : List ℕ) (s : ℕ) : L.contains s = bitQ (maskOf 0 L) s := by
  rw [bitQ_eq, maskOf_testBit, Nat.zero_testBit, Bool.false_or]

@[expose] def MRel (h : Std.HashSet ℕ) (m : ℕ) : Prop := ∀ k, h.contains k = m.testBit k

@[expose] def stepH (acc : List ℕ × Std.HashSet ℕ) (t : ℕ) : List ℕ × Std.HashSet ℕ :=
  match acc with
  | (l, h) => if h.contains (id t) then (l, h) else (t :: l, h.insert (id t))

theorem foldl_stepO : ∀ (L l : List ℕ) (h : Std.HashSet ℕ) (m : ℕ), MRel h m →
    (L.foldl stepH (l, h)).1 = (L.foldl stepO (l, m)).1 ∧
      MRel (L.foldl stepH (l, h)).2 (L.foldl stepO (l, m)).2
  | [], _, _, _, hr => ⟨rfl, hr⟩
  | x :: L, l, h, m, hr => by
    rw [List.foldl_cons, List.foldl_cons]
    have hc : h.contains x = bitQ m x := by rw [bitQ_eq]; exact hr x
    cases hb : bitQ m x
    · have e1 : stepH (l, h) x = (x :: l, h.insert x) := by
        simp only [stepH, id, hc, hb, Bool.false_eq_true, if_false]
      have e2 : stepO (l, m) x = (x :: l, Nat.lor m (Nat.shiftLeft 1 x)) := by
        simp only [stepO, hb, Bool.false_eq_true, if_false]
      rw [e1, e2]
      refine foldl_stepO L _ _ _ fun k => ?_
      rw [Std.HashSet.contains_insert, testBit_ins, hr k]
    · have e1 : stepH (l, h) x = (l, h) := by simp only [stepH, id, hc, hb, if_true]
      have e2 : stepO (l, m) x = (l, m) := by simp only [stepO, hb, if_true]
      rw [e1, e2]
      exact foldl_stepO L l h m hr

theorem bfsClosure_O (fs : List (ℕ → ℕ)) : ∀ (fuel : ℕ) (fr vis : List ℕ) (h : Std.HashSet ℕ)
    (m : ℕ), MRel h m → bfsClosure id fs fuel fr h vis = closO fs fuel fr m vis
  | 0, fr, vis, h, m, _ => by rw [bfsClosure, closO]
  | fuel + 1, fr, vis, h, m, hr => by
    have e1 : bfsRound id fs fr h =
        (fr.flatMap fun s => fs.map fun f => f s).foldl stepH ([], h) := rfl
    have e2 : roundO fs fr m = (fr.flatMap fun s => fs.map fun f => f s).foldl stepO ([], m) := rfl
    obtain ⟨r1, r2⟩ := foldl_stepO (fr.flatMap fun s => fs.map fun f => f s) [] h m hr
    rw [bfsClosure, closO, e1, e2, r1]
    split_ifs
    · rfl
    · exact bfsClosure_O fs fuel _ _ _ _ r2

theorem appN_hjAc : appN hjAc = mvNR acL :=
  funext fun n => by rw [GammaUList.appN_eq (by decide) (by decide) n, appL_eq_mvNR]; rfl

theorem appN_hjBc : appN hjBc = mvNR bcL :=
  funext fun n => by rw [GammaUList.appN_eq (by decide) (by decide) n, appL_eq_mvNR]; rfl

theorem orbitOf_eq (p : ℕ) : orbitOf gensL p = orbitQ p := by
  rw [orbitOf, orbitQ, gensL, List.map_cons, List.map_cons, List.map_nil, appN_hjAc, appN_hjBc]
  refine bfsClosure_O _ 4096 [p] [] _ _ fun k => ?_
  rw [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
  change _ = (1 <<< p).testBit k
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : p = k <;> simp [h]

theorem all_map_congr {L : List ℕ} {p : Array ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ x ∈ L, p (unpackA x) = q x) : (L.map unpackA).all p = L.all q := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H x hx
    rw [← h x hx]
    exact H _ (List.mem_map_of_mem hx)
  · intro H y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    rw [h x hx]
    exact H x hx

theorem any_map_congr {L : List ℕ} {p : Array ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ x ∈ L, p (unpackA x) = q x) : (L.map unpackA).any p = L.any q := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, e⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact ⟨x, hx, by rw [← h x hx]; exact e⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨_, List.mem_map_of_mem hx, by rw [h x hx]; exact e⟩

theorem filter_map_congr {L : List ℕ} {p : Array ℕ → Bool} {q : ℕ → Bool}
    (h : ∀ x ∈ L, p (unpackA x) = q x) : (L.map unpackA).filter p = (L.filter q).map unpackA := by
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun x hx => by rw [Function.comp_apply, h x hx]

theorem isInvol_unpackA {x : ℕ} (hx : x < 2 ^ 144) : isInvol (unpackA x) = isInvolQ x := by
  rw [isInvol, isInvolQ, bne, mulR_unpackA, idR_eq, beq_unpackA hx oneQ_lt,
    beq_unpackA (mulQ_lt _ _) oneQ_lt, nat_beq, nat_beq]

theorem commR_unpackA (x y : ℕ) : commR (unpackA x) (unpackA y) = commQ x y := by
  rw [commR, commQ, mulR_unpackA, mulR_unpackA, beq_unpackA (mulQ_lt _ _) (mulQ_lt _ _), nat_beq]

theorem filter_invol {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 144) :
    (X.map unpackA).filter isInvol = (X.filter isInvolQ).map unpackA :=
  filter_map_congr fun x hx => isInvol_unpackA (hX x hx)

theorem filter_lt {X : List ℕ} (hX : ∀ q ∈ X, q < 2 ^ 144) (p : ℕ → Bool) :
    ∀ q ∈ X.filter p, q < 2 ^ 144 := fun q hq => hX q (List.mem_filter.1 hq).1

theorem hjTauc_eq : hjTauc = unpackA tauQ := by decide

theorem hjTauCheck_of (h : tauQCheck = true) : hjTauCheck = true := by
  have h1 : invOKQ tauQ (invQ tauQ) = true := by
    rw [tauQCheck, Bool.and_eq_true, Bool.and_eq_true] at h
    exact h.1.1
  simp only [hjTauCheck, hjTauc_eq, invR_unpackA h1, hjAc_eq, hjBc_eq, idR_eq, mulR_unpackA,
    wordR_eq, beq_unpackA (mulQ_lt _ _) oneQ_lt, beq_unpackA (mulQ_lt _ _) (wordQ_lt _), nat_beq]
  rw [tauQCheck, invOKQ] at h
  exact h

@[expose] def e16M (invs : List (Array ℕ)) (t : Array ℕ) : Bool :=
  let C := invs.filter fun s => s != t && commR s t
  C.any fun s =>
    let g2 := [idR, t, s, mulR t s]
    C.any fun r =>
      !g2.contains r && commR r s &&
        let g3 := g2 ++ g2.map (fun y => mulR y r)
        C.any fun q => !g3.contains q && commR q s && commR q r

theorem e16M_eq {I : List ℕ} (hI : ∀ q ∈ I, q < 2 ^ 144) {t : ℕ} (ht : t < 2 ^ 144) :
    e16M (I.map unpackA) (unpackA t) = e16Q I t := by
  have hC : (I.map unpackA).filter (fun s => s != unpackA t && commR s (unpackA t)) =
      (I.filter fun s => !Nat.beq s t && commQ s t).map unpackA :=
    filter_map_congr fun s hs => by rw [bne, beq_unpackA (hI s hs) ht, commR_unpackA, nat_beq]
  have hCb := filter_lt hI (fun s => !Nat.beq s t && commQ s t)
  simp only [e16M]
  rw [hC, e16Q]
  refine any_map_congr fun s hs => ?_
  have hs' := hCb s hs
  rw [e16r]
  refine any_map_congr fun r hr => ?_
  have hr' := hCb r hr
  simp only [idR_eq, mulR_unpackA, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.contains_cons, List.contains_nil, beq_unpackA hr' oneQ_lt, beq_unpackA hr' ht,
    beq_unpackA hr' hs', beq_unpackA hr' (mulQ_lt _ _), commR_unpackA, nat_beq]
  congr 1
  rw [e16q]
  refine any_map_congr fun q hq => ?_
  have hq' := hCb q hq
  simp only [List.contains_cons, List.contains_nil, beq_unpackA hq' oneQ_lt, beq_unpackA hq' ht,
    beq_unpackA hq' hs', beq_unpackA hq' hr', beq_unpackA hq' (mulQ_lt _ _), commR_unpackA,
    nat_beq]

theorem fixOK_eq (O : List ℕ) (t : ℕ) :
    ((fixCodes (unpackA t)).length == 64 ||
      ((fixCodes (unpackA t)).length == 256 && (fixCodes (unpackA t)).any fun s₁ =>
        O.contains s₁ && (fixCodes (unpackA t)).any fun s₂ =>
          O.contains s₂ && O.contains (s₁ ^^^ s₂))) =
      fixOK (maskOf 0 O) t := by
  rw [fixCodes_length, fixCodes_unpackA, fixOK]
  simp only [contains_bitQ, nat_beq]

theorem t1_sound (O g0 a1 a2 X0 X1 A1 A2 : List ℕ) (tq : ℕ) (hO : orbitOf gensL 1024 = O)
    (e0 : hj_t0Words.map wordR = g0.map unpackA) (et : hjTauc = unpackA tq)
    (ea1 : hj_a1Words.map wordR = a1.map unpackA) (ea2 : hj_a2Words.map wordR = a2.map unpackA)
    (E0 : enumGrp (g0.map unpackA) = X0.map unpackA)
    (E1 : enumGrp ((g0 ++ [tq]).map unpackA) = X1.map unpackA)
    (EA1 : enumGrp (a1.map unpackA) = A1.map unpackA)
    (EA2 : enumGrp (a2.map unpackA) = A2.map unpackA)
    (B0 : ∀ q ∈ X0, q < 2 ^ 144) (B1 : ∀ q ∈ X1, q < 2 ^ 144) (BA1 : ∀ q ∈ A1, q < 2 ^ 144)
    (BA2 : ∀ q ∈ A2, q < 2 ^ 144)
    (h : t1At (maskOf 0 O) g0 (g0 ++ [tq]) a1 a2 X0 X1 A1 A2 = true) : hjT1Check = true := by
  have e1 : hj_t0Words.map wordR ++ [hjTauc] = (g0 ++ [tq]).map unpackA := by
    rw [e0, et, List.map_append, List.map_singleton]
  have BI := filter_lt B1 isInvolQ
  simp only [t1At, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩,
    h13⟩, h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩ := h
  simp only [hjT1Check, Bool.and_eq_true]
  rw [e1, e0, ea1, ea2, E0, E1, EA1, EA2, filter_invol B1, hO]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    ?_⟩, ?_⟩, ?_⟩
  · exact gensOKN_of _ h1
  · rw [← List.map_append]
    exact gensOKN_of _ h2
  · rw [closedCheck_eq _ _ B0]
    exact h3
  · rw [closedCheck_eq _ _ B1]
    exact h4
  · exact (congrArg (· == 128) (dedup_length B0 h5)).trans ((nat_beq _ _).trans h6)
  · exact (congrArg (· == 256) (dedup_length B1 h7)).trans ((nat_beq _ _).trans h8)
  · rw [closedCheck_eq _ _ BA1]
    exact h9
  · rw [closedCheck_eq _ _ BA2]
    exact h10
  · exact (congrArg (· == 16) (dedup_length BA1 h11)).trans ((nat_beq _ _).trans h12)
  · exact (congrArg (· == 16) (dedup_length BA2 h13)).trans ((nat_beq _ _).trans h14)
  · refine (all_map_congr fun x hx => ?_).trans h15
    rw [contains_map B0 (BA1 x hx), mulR_unpackA, idR_eq, beq_unpackA (mulQ_lt _ _) oneQ_lt,
      nat_beq]
  · refine (all_map_congr fun x hx => ?_).trans h16
    rw [contains_map B0 (BA2 x hx), mulR_unpackA, idR_eq, beq_unpackA (mulQ_lt _ _) oneQ_lt,
      nat_beq]
  · exact (all_map_congr fun x _ => all_map_congr fun y _ => commR_unpackA x y).trans h17
  · exact (all_map_congr fun x _ => all_map_congr fun y _ => commR_unpackA x y).trans h18
  · refine (any_map_congr fun x hx => ?_).trans h19
    rw [contains_map BA2 (BA1 x hx)]
  · have hf : (((X1.filter isInvolQ).map unpackA).filter fun t =>
        !(A1.map unpackA).contains t && !(A2.map unpackA).contains t) =
        ((X1.filter isInvolQ).filter fun t => !A1.contains t && !A2.contains t).map unpackA :=
      filter_map_congr fun x hx => by
        rw [contains_map BA1 (BI x hx), contains_map BA2 (BI x hx)]
    rw [hf]
    exact (all_map_congr fun t ht =>
      congrArg Bool.not (e16M_eq BI (filter_lt BI _ t ht))).trans h20
  · refine (all_map_congr fun t _ => ?_).trans h21
    exact fixOK_eq O t

theorem hjT1Check_of (h : t1Q = true) : hjT1Check = true := by
  rw [t1Q] at h
  obtain ⟨E0, B0⟩ := enumGrp_eq g0Q
  obtain ⟨E1, B1⟩ := enumGrp_eq (g0Q ++ [tauQ])
  obtain ⟨EA1, BA1⟩ := enumGrp_eq (hj_a1Words.map wordQ)
  obtain ⟨EA2, BA2⟩ := enumGrp_eq (hj_a2Words.map wordQ)
  exact t1_sound _ g0Q _ _ _ _ _ _ tauQ (orbitOf_eq 1024) (words_eq _) hjTauc_eq (words_eq _)
    (words_eq _) E0 E1 EA1 EA2 B0 B1 BA1 BA2 h

theorem hjT1Gens_eq : hjT1Gens () = (g0Q ++ [tauQ]).map unpackA := by
  rw [hjT1Gens, words_eq, hjTauc_eq, List.map_append, List.map_singleton]
  rfl

theorem g1_lt : ∀ g ∈ enumQ (g0Q ++ [tauQ]), g < 2 ^ 144 := (enumGrp_eq _).2

theorem hjT1Invs_eq :
    hjT1Invs () = ((enumQ (g0Q ++ [tauQ])).filter isInvolQ).map unpackA := by
  rw [hjT1Invs, hjT1Gens_eq, (enumGrp_eq _).1, filter_invol g1_lt]

theorem hjT1Tab_eq : hjT1Tab () =
    ((enumQ (g0Q ++ [tauQ])).filter isInvolQ).map fun x => (unpackA x, fixCnt x) := by
  rw [hjT1Tab, hjT1Invs_eq, List.map_map]
  exact List.map_congr_left fun x _ => by rw [Function.comp_apply, fixCodes_length]

theorem lookup_eq (L : List ℕ) (hL : ∀ q ∈ L, q < 2 ^ 144) {r : ℕ} (hr : r < 2 ^ 144) :
    hjLookup (L.map fun x => (unpackA x, fixCnt x)) (unpackA r) =
      if L.contains r then fixCnt r else 0 := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx := hL x List.mem_cons_self
    have ih' := ih fun q hq => hL q (List.mem_cons_of_mem x hq)
    unfold hjLookup at ih' ⊢
    rw [List.map_cons, List.find?_cons, beq_unpackA hx hr, List.contains_cons, beq_symm r x]
    cases e : (x == r)
    · exact ih'
    · obtain rfl := beq_iff_eq.1 e
      rfl

theorem lookup_mem {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {r : ℕ} (hr : r ∈ L) :
    hjLookup (L.map fun x => (unpackA x, fixCnt x)) (unpackA r) = fixCnt r := by
  rw [lookup_eq L hL (hL r hr), if_pos (List.contains_iff_mem.2 hr)]

theorem lookup_set {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {r : ℕ} (hr : r < 2 ^ 144) {n : ℕ}
    (hn : n ≠ 0) :
    (hjLookup (L.map fun x => (unpackA x, fixCnt x)) (unpackA r) == n) = memP (setOf L n) r := by
  rw [lookup_eq L hL hr, setOf, memP_ofListP]
  split_ifs with h
  · rw [Bool.eq_iff_iff, beq_iff_eq, List.contains_iff_mem, List.mem_filter, Nat.beq_eq]
    exact ⟨fun e => ⟨List.contains_iff_mem.1 h, e⟩, fun e => e.2⟩
  · rw [Bool.eq_iff_iff, beq_iff_eq, List.contains_iff_mem, List.mem_filter, Nat.beq_eq]
    exact ⟨fun e => absurd e.symm hn, fun e => absurd (List.contains_iff_mem.2 e.1) h⟩

theorem lookup64 {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {r : ℕ} (hr : r < 2 ^ 144) :
    (hjLookup (L.map fun x => (unpackA x, fixCnt x)) (unpackA r) == 64) = memP (setOf L 64) r :=
  lookup_set hL hr (by norm_num)

theorem lookup256 {L : List ℕ} (hL : ∀ q ∈ L, q < 2 ^ 144) {r : ℕ} (hr : r < 2 ^ 144) :
    (hjLookup (L.map fun x => (unpackA x, fixCnt x)) (unpackA r) == 256) =
      memP (setOf L 256) r :=
  lookup_set hL hr (by norm_num)

theorem rowAux_low (x : ℕ) : ∀ (L : List ℕ) (j b : ℕ), b < j → (rowAux x L j).testBit b = false
  | [], _, _, _ => by simp [rowAux]
  | y :: L, j, b, hb => by
    change (Nat.lor (if commQ x y then Nat.shiftLeft 1 j else 0) (rowAux x L (j + 1))).testBit b = _
    change ((if commQ x y then Nat.shiftLeft 1 j else 0) ||| rowAux x L (j + 1)).testBit b = _
    rw [Nat.testBit_or, rowAux_low x L (j + 1) b (by omega), Bool.or_false]
    split_ifs
    · change (1 <<< j).testBit b = false
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [decide_eq_false_iff_not]
      omega
    · exact Nat.zero_testBit b

theorem rowAux_testBit (x : ℕ) : ∀ (L : List ℕ) (j k : ℕ) (hk : k < L.length),
    (rowAux x L j).testBit (j + k) = commQ x L[k]
  | [], _, _, hk => absurd hk (by simp)
  | y :: L, j, k, hk => by
    change ((if commQ x y then Nat.shiftLeft 1 j else 0) ||| rowAux x L (j + 1)).testBit (j + k) = _
    rw [Nat.testBit_or]
    rcases k with _ | k
    · rw [rowAux_low x L (j + 1) (j + 0) (by omega), Bool.or_false, List.getElem_cons_zero]
      split_ifs with hc
      · change (1 <<< j).testBit (j + 0) = _
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow, hc]
        simp
      · rw [Nat.zero_testBit]
        simpa using hc
    · have e : j + (k + 1) = j + 1 + k := by omega
      rw [e, rowAux_testBit x L (j + 1) k (by simpa using hk), List.getElem_cons_succ]
      split_ifs
      · change ((1 <<< j).testBit (j + 1 + k) || _) = _
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
        simp only [Bool.or_eq_right_iff_imp, decide_eq_true_eq]
        omega
      · rw [Nat.zero_testBit, Bool.false_or]

theorem tup_mem (I : List ℕ) : ∀ (L : List ℕ) (i : ℕ) (p : Tup), p ∈ tupAux I L i →
    ∃ k, ∃ hk : k < L.length, p = (L[k], i + k, rowAux L[k] I 0, fixCnt L[k])
  | [], _, _, hp => by simp [tupAux] at hp
  | x :: L, i, p, hp => by
    rw [tupAux, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, rfl⟩ := tup_mem I L (i + 1) p hp
      refine ⟨k + 1, by simpa using hk, ?_⟩
      simp only [List.getElem_cons_succ]
      congr 2
      omega

theorem tup_fst (I : List ℕ) : ∀ (L : List ℕ) (i : ℕ), (tupAux I L i).map Prod.fst = L
  | [], _ => rfl
  | x :: L, i => by rw [tupAux, List.map_cons, tup_fst I L (i + 1)]

theorem tup_bit {I : List ℕ} {p q : Tup} (hp : p ∈ tupAux I I 0) (hq : q ∈ tupAux I I 0) :
    bitQ p.2.2.1 q.2.1 = commQ p.1 q.1 := by
  obtain ⟨k, hk, rfl⟩ := tup_mem I I 0 p hp
  obtain ⟨l, hl, rfl⟩ := tup_mem I I 0 q hq
  rw [bitQ_eq, rowAux_testBit _ I 0 l hl]

theorem tup_fst_mem {I : List ℕ} {p : Tup} (hp : p ∈ tupAux I I 0) : p.1 ∈ I := by
  obtain ⟨k, hk, rfl⟩ := tup_mem I I 0 p hp
  exact List.getElem_mem hk

theorem tup_cnt {I : List ℕ} {p : Tup} (hp : p ∈ tupAux I I 0) : p.2.2.2 = fixCnt p.1 := by
  obtain ⟨k, hk, rfl⟩ := tup_mem I I 0 p hp
  rfl

theorem all_T {T : List Tup} {p : Array ℕ → Bool} {q : Tup → Bool}
    (h : ∀ x ∈ T, p (unpackA x.1) = q x) : ((T.map Prod.fst).map unpackA).all p = T.all q := by
  rw [List.map_map, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro H x hx
    rw [← h x hx]
    exact H _ (List.mem_map_of_mem hx)
  · intro H y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    rw [Function.comp_apply, h x hx]
    exact H x hx

theorem all_or_left (A : Bool) {α : Type} (L : List α) (B : α → Bool) :
    (A || L.all B) = L.all fun r => A || B r := by
  cases A <;> simp

theorem or10 : ∀ a1 a2 a3 n4 n5 n6 ch n8 n9 mix : Bool,
    (a1 || a2 || a3 || n4 || n5 || n6 || ch || n8 || n9 || mix) =
      ((a1 || n4 || n8) || (a2 || a3 || n5 || n6 || ch || n9 || mix)) := by
  decide

theorem tri_sound (I : List ℕ) (hIb : ∀ q ∈ I, q < 2 ^ 144) (hI0 : hjT1Invs () = I.map unpackA)
    (hT : hjT1Tab () = I.map fun x => (unpackA x, fixCnt x)) (h : triI I = true) :
    hjPureTripleCheck () = true := by
  have hI : hjT1Invs () = ((tupAux I I 0).map Prod.fst).map unpackA := by
    rw [tup_fst, hI0]
  rw [triI, triAt] at h
  refine Eq.trans ?_ h
  rw [hjPureTripleCheck, hI, hT]
  refine all_T fun p hp => ?_
  refine all_T fun q hq => ?_
  rw [zLoop, all_or_left]
  refine all_T fun r hr => ?_
  have ha := hIb _ (tup_fst_mem hp)
  have hb := hIb _ (tup_fst_mem hq)
  have hc := hIb _ (tup_fst_mem hr)
  rw [hjTripleOK, hjMixedSpan, hjTripleRows]
  simp only [idR_eq, mulR_unpackA, List.any_cons, List.any_nil, lookup64 hIb ha, lookup64 hIb hb,
    lookup64 hIb hc, lookup64 hIb (mulQ_lt _ _), lookup256 hIb ha, lookup256 hIb hb,
    lookup256 hIb hc, lookup256 hIb (mulQ_lt _ _)]
  simp only [bne, beq_unpackA ha hb, beq_unpackA ha hc, beq_unpackA hb hc, commR_unpackA,
    ← tup_bit hp hq, ← tup_bit hp hr, ← tup_bit hq hr, List.contains_cons,
    List.contains_nil, beq_unpackA hc oneQ_lt, beq_unpackA hc ha, beq_unpackA hc hb,
    beq_unpackA hc (mulQ_lt _ _), lookup_mem hIb (tup_fst_mem hp), lookup_mem hIb (tup_fst_mem hq),
    lookup_mem hIb (tup_fst_mem hr), ← tup_cnt hp, ← tup_cnt hq, ← tup_cnt hr, nat_beq]
  exact (or10 _ _ _ _ _ _ _ _ _ _).trans rfl

theorem hjPureTripleCheck_of (h : triQ = true) : hjPureTripleCheck () = true := by
  rw [triQ] at h
  exact tri_sound _ (filter_lt g1_lt isInvolQ) hjT1Invs_eq hjT1Tab_eq h

theorem z_sound {w : List ℕ} (h : zCore (wordQ w) = true) :
    (isInvol (wordR w) && (fixCodes (wordR w)).length == 256) = true := by
  simp only [wordR_eq, isInvol_unpackA (wordQ_lt _), fixCodes_length, nat_beq]
  exact h

theorem hjZCheck_of (h : zQ = true) : hjZCheck () = true :=
  z_sound (w := hj_zWord) h

theorem fourQ_sound {w1 w2 w3 : List ℕ} {v : ℕ}
    (h : fourQ (wordQ w1) (wordQ w2) (wordQ w3) v = true) :
    (isInvol (wordR w1) && isInvol (wordR w2) && wordR w1 != wordR w2 &&
      commR (wordR w1) (wordR w2) && appN (wordR w1) v == v && appN (wordR w2) v == v &&
      appN (wordR w3) v != v) = true := by
  simp only [wordR_eq, isInvol_unpackA (wordQ_lt _), bne, beq_unpackA (wordQ_lt _) (wordQ_lt _),
    commR_unpackA, appN_unpackA, nat_beq]
  exact h

theorem hjE16A1Check_of (h : fourQ (wordQ hj_b1Word) (wordQ hj_b2Word) (wordQ hj_g1Word) 81 = true) :
    hjE16A1Check () = true :=
  fourQ_sound h

theorem hjE16A2Check_of
    (h : fourQ (wordQ hj_c1Word) (wordQ hj_c2Word) (wordQ hj_h1Word) 136 = true) :
    hjE16A2Check () = true :=
  fourQ_sound h

theorem hjThreeThreeCheck_of (hz : zQ = true) (ht : triQ = true)
    (h1 : fourQ (wordQ hj_b1Word) (wordQ hj_b2Word) (wordQ hj_g1Word) 81 = true)
    (h2 : fourQ (wordQ hj_c1Word) (wordQ hj_c2Word) (wordQ hj_h1Word) 136 = true) :
    hjThreeThreeCheck () = true := by
  rw [hjThreeThreeCheck, hjZCheck_of hz, hjPureTripleCheck_of ht, hjE16A1Check_of h1,
    hjE16A2Check_of h2, Bool.and_self, Bool.and_self, Bool.and_self]

end Certificates.Kernel.HJ12K

end
