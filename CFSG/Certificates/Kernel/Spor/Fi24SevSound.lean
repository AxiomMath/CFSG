module

public import Certificates.Data.Kernel.Spor.Fi24Sev
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.Fi24Sev

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Sev CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24ThreeO Finset

@[expose] def tupL (f : Nat → Nat) (q : Nat) : List Nat := (List.range 7).map fun i => f^[i] q

@[expose] def tupN (f : Nat → Nat) (q n : Nat) : List Nat := (List.range n).map fun i => f^[i] q

@[expose] def cfgL (D : Nat → Nat → Nat) (Z : List Nat) (prog : List (Nat × Nat)) : List Nat :=
  prog.foldl (fun Z p => Z ++ [D (Z.getD p.1 0) (Z.getD p.2 0)]) Z

@[expose] noncomputable def stripL (NW : Nat → Nat → Nat) (NT : Nat → Nat) :
    List (List Nat) → Nat → List Nat → Option (List Nat)
  | [], _, c => some c
  | t :: ts, i, c =>
    if (∀ l ∈ t, 4 * i ≤ l ∧ l < 26) ∧ cP NW NT t (cb.getD i 0) = c.getD i 0 then
      stripL NW NT ts (i + 1) (c.map (cP NW NT (invC t)))
    else none

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem orB_true' {a b : Bool} (h : orB a b = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [orB]

theorem ble_true {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem blt_true {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  simpa [Nat.blt_eq] using h

theorem relOK_spec {w : List Nat} {hs : List (List Nat)} (h : relOK NW NT w hs = true) :
    (∀ b ∈ cb, (cP NW NT w)^[7] b = b) ∧
      ∀ u ∈ hs, ∀ b ∈ cb, cP NW NT (u ++ w) b = cP NW NT (w ++ u) b := by
  unfold relOK at h
  obtain ⟨h1, h2⟩ := andB_true' h
  refine ⟨fun b hb => ?_, fun u hu b hb => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (allL_spec h1 b hb)
    have hf : ptC NW NT w = cP NW NT w := funext (ptC_eq NW NT w)
    rw [itN_eq, hf] at e
    exact e
  · have e := Nat.eq_of_beq_eq_true (allL_spec (allL_spec h2 u hu) b hb)
    rw [ptC_eq, ptC_eq] at e
    exact e

theorem covOK_spec (hV : VN NW NT) {ws : List (List Nat)} {d d2 om c : Nat} {reps : List Nat}
    (h : covOK NW NT ws d reps d2 om c = true) :
    ∃ F : Nat, (∀ x < 524288, F.testBit x = true → ∃ v, InW ws v ∧ cP NW NT v x = om) ∧
      #((range 524288).filter (fun x => F.testBit x = true)) = c ∧
      ∀ x < 306936, F.testBit x = true ∨ ∃ v, InW ws v ∧ cP NW NT v x ∈ reps := by
  unfold covOK at h
  rw [letB_eq'] at h
  obtain ⟨h1, h2⟩ := andB_true' h
  set F := iterW NW NT ws d2 (Nat.shiftLeft 1 om) with hF
  refine ⟨F, fun x hx hFx => ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨v, hv, hS⟩ := iterW_spec hV ws _ d2 x hx hFx
    refine ⟨v, hv, ?_⟩
    change (Nat.shiftLeft 1 om).testBit _ = true at hS
    rw [show Nat.shiftLeft 1 om = 1 <<< om from rfl, Nat.one_shiftLeft, Nat.testBit_two_pow] at hS
    exact (of_decide_eq_true hS).symm
  · have e := Nat.eq_of_beq_eq_true h2
    rw [CFSG.KS.Fi24FixP.popcount_19, CFSG.KS.Fi24FixP.sum_bits] at e
    exact e
  · rcases covW_spec hV h1 hx with e | ⟨v, hv, e⟩
    · exact Or.inl e
    · exact Or.inr ⟨v, hv, (testBit_plOf reps _).1 e⟩

theorem slOK_spec {sl : List (Nat × List Nat × List Nat)} (h : slOK NW NT sl = true) :
    ∀ e ∈ sl, (∀ z ∈ e.2.1, 2 ≤ z ∧ (z ≤ 5 ∨ (z / 2 - 3 < e.1 ∧ ∃ e' ∈ sl, e'.1 = z / 2 - 3))) ∧
      ∀ b ∈ cb, cP NW NT (expU sl e.2.1) b = cP NW NT e.2.2 b := by
  intro e he
  obtain ⟨h1, h2⟩ := andB_true' (allL_spec h e he)
  refine ⟨fun z hz => ?_, fun b hb => ?_⟩
  · obtain ⟨hz2, hz⟩ := andB_true' (allL_spec h1 z hz)
    refine ⟨ble_true hz2, ?_⟩
    rcases orB_true' hz with hz | hz
    · exact Or.inl (ble_true hz)
    · obtain ⟨hlt, hu⟩ := andB_true' hz
      refine Or.inr ⟨by simpa [Nat.shiftRight_eq_div_pow] using blt_true hlt, ?_⟩
      have key : ∀ (l : List (Nat × List Nat × List Nat)) (k : Nat), hasU l k = true →
          ∃ e' ∈ l, e'.1 = k := by
        intro l k
        induction l with
        | nil => intro h0; exact absurd h0 (by simp [hasU])
        | cons a l ih =>
          intro h0
          rcases orB_true' h0 with h0 | h0
          · exact ⟨a, List.mem_cons_self, Nat.eq_of_beq_eq_true h0⟩
          · obtain ⟨e', he', h'⟩ := ih h0
            exact ⟨e', List.mem_cons_of_mem a he', h'⟩
      simpa [Nat.shiftRight_eq_div_pow] using key sl _ hu
  · have e2 := Nat.eq_of_beq_eq_true (allL_spec h2 b hb)
    rw [ptC_eq, ptC_eq] at e2
    exact e2

open CFSG.KC.Fi24Orb (oA oB oPar oLab)

private def holderSevRp (Z : Nat) (L : List Nat) : Prop :=
  (∀ x ∈ L, x < 524288) ∧
    ∀ k, Z.testBit k = (decide (k / 20 < L.length) && (L.getD (k / 20) 0).testBit (k % 20))

private theorem holderSev_getD_of_lt {l : List Nat} {i : Nat} (h : i < l.length) :
    l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

private theorem holderSev_getD_of_ge {l : List Nat} {i : Nat} (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

private theorem holderSev_getD_lt {Z : Nat} {L : List Nat} (h : holderSevRp Z L) (i : Nat) :
    L.getD i 0 < 524288 := by
  rcases lt_or_ge i L.length with hi | hi
  · rw [holderSev_getD_of_lt hi]
    exact h.1 _ (List.getElem_mem hi)
  · rw [holderSev_getD_of_ge hi]
    norm_num

private theorem holderSev_lt_pow {x j : Nat} (hx : x < 524288) (hj : 19 ≤ j) : x < 2 ^ j :=
  lt_of_lt_of_le hx (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj))

private theorem holderSev_getP {Z : Nat} {L : List Nat} (h : holderSevRp Z L) (i : Nat) :
    getP Z i = L.getD i 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hL := holderSev_getD_lt h i
  show ((Z >>> (i * 20)) &&& 1048575).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h.2, show (1048575 : Nat) = 2 ^ 20 - 1 by norm_num,
    Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 20
  · rw [show (i * 20 + j) / 20 = i by omega, show (i * 20 + j) % 20 = j by omega]
    by_cases hi : i < L.length
    · simp [hi, hj]
    · simp [hi, hj, holderSev_getD_of_ge (Nat.le_of_not_lt hi)]
  · rw [decide_eq_false hj, Bool.and_false]
    exact (Nat.testBit_lt_two_pow (holderSev_lt_pow hL (by omega))).symm

private theorem holderSev_nil : holderSevRp 0 [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun k => by simp⟩

private theorem holderSev_putP {Z : Nat} {L : List Nat} (h : holderSevRp Z L) {x : Nat}
    (hx : x < 524288) : holderSevRp (putP Z L.length x) (L ++ [x]) := by
  refine ⟨fun y hy => ?_, fun k => ?_⟩
  · rcases List.mem_append.1 hy with hy | hy
    · exact h.1 y hy
    · rw [List.mem_singleton.1 hy]
      exact hx
  · show (Z ||| (x <<< (L.length * 20))).testBit k = _
    rw [Nat.testBit_or, h.2, Nat.testBit_shiftLeft, List.length_append, List.length_singleton]
    rcases lt_trichotomy (k / 20) L.length with hk | hk | hk
    · have h1 : ¬ k ≥ L.length * 20 := by omega
      have e : (L ++ [x]).getD (k / 20) 0 = L.getD (k / 20) 0 := by
        rw [holderSev_getD_of_lt (by simp; omega), holderSev_getD_of_lt hk,
          List.getElem_append_left hk]
      rw [e]
      simp [hk, h1, Nat.lt_succ_of_lt hk]
    · have h1 : k ≥ L.length * 20 := by omega
      have h2 : k - L.length * 20 = k % 20 := by omega
      have e : (L ++ [x]).getD (k / 20) 0 = x := by
        rw [holderSev_getD_of_lt (by simp; omega)]
        simp [hk]
      rw [e, h2, hk]
      simp [h1]
    · have h1 : k ≥ L.length * 20 := by omega
      have h2 : ¬ k / 20 < L.length + 1 := by omega
      have h3 : ¬ k / 20 < L.length := by omega
      have h4 : x.testBit (k - L.length * 20) = false :=
        Nat.testBit_lt_two_pow (holderSev_lt_pow hx (by omega))
      simp [h1, h2, h3, h4]

private theorem holderSev_mask {Z : Nat} {L : List Nat} (h : holderSevRp Z L) (n : Nat) :
    holderSevRp (Nat.land Z (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.mul n (nat_lit 20)))
      (nat_lit 1))) (L.take n) := by
  refine ⟨fun y hy => h.1 y (List.mem_of_mem_take hy), fun k => ?_⟩
  show (Z &&& (1 <<< (n * 20) - 1)).testBit k = _
  rw [Nat.testBit_and, h.2, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, List.length_take]
  by_cases hk : k / 20 < n
  · have h1 : k < n * 20 := by omega
    have e : (L.take n).getD (k / 20) 0 = L.getD (k / 20) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk, ← List.getD_eq_getElem?_getD]
    rw [e]
    simp [hk, h1]
  · have h1 : ¬ k < n * 20 := by omega
    simp [hk, h1]

private theorem holderSev_tupN_succ (f : Nat → Nat) (x n : Nat) :
    tupN f x (n + 1) = x :: tupN f (f x) n := by
  simp [tupN, List.range_succ_eq_map, Function.comp_def, Function.iterate_succ_apply]

private theorem holderSev_tupA {f : Nat → Nat} (hf : ∀ y < 524288, f y < 524288) :
    ∀ (n : Nat) {Z i : Nat} {L : List Nat} {x : Nat}, holderSevRp Z L → L.length = i →
      x < 524288 → holderSevRp (tupA f n i x Z) (L ++ tupN f x n)
  | 0, Z, _, L, x, h, _, _ => by
    show holderSevRp Z (L ++ tupN f x 0)
    simpa [tupN] using h
  | n + 1, Z, _, L, x, h, rfl, hx => by
    have e1 : tupA f (n + 1) L.length x Z = strictN (putP Z L.length x)
        (fun Z' => strictN (f x) (fun y => tupA f n (L.length + 1) y Z')) := rfl
    have e : tupA f (n + 1) L.length x Z = tupA f n (L.length + 1) (f x) (putP Z L.length x) := by
      rw [e1, Fi24NetPt.strictN_eq]
      exact Fi24NetPt.strictN_eq _ _
    rw [e, holderSev_tupN_succ, ← List.singleton_append, ← List.append_assoc]
    exact holderSev_tupA hf n (holderSev_putP h hx) (by simp) (hf x hx)

private theorem holderSev_nIf_lt {c : Bool} {t e n : Nat} (ht : t < n) (he : e < n) :
    Bool.rec (motive := fun _ => Nat) e t c < n := by
  cases c
  · exact he
  · exact ht

private theorem holderSev_oA_lt (e : Nat) : oA e < 524288 :=
  lt_of_le_of_lt (Nat.and_le_right (n := e) (m := 524287)) (by norm_num)

private theorem holderSev_oB_lt (e : Nat) : oB e < 524288 :=
  lt_of_le_of_lt (Nat.and_le_right (n := e >>> 19) (m := 524287)) (by norm_num)

private theorem holderSev_gT_lt (OL : Nat → Nat) (l q : Nat) : gT OL l q < 524288 :=
  holderSev_nIf_lt (holderSev_oA_lt _) (holderSev_oB_lt _)

private theorem holderSev_gI_lt (OL : Nat → Nat) (l q : Nat) : gI OL l q < 524288 := by
  show Bool.rec (motive := fun _ => Nat) (strictN (oB (OL q)) (fun y => oB (OL y)))
    (oA (OL q)) (Nat.beq l 1) < 524288
  refine holderSev_nIf_lt (holderSev_oA_lt _) ?_
  rw [Fi24NetPt.strictN_eq]
  exact holderSev_oB_lt _

private theorem holderSev_upF_lt (OL : Nat → Nat) :
    ∀ (f k q : Nat), q < 524288 → upF OL f k q < 524288
  | 0, _, _, hq => hq
  | f + 1, k, q, hq => by
    show Bool.rec (motive := fun _ => Nat)
      (strictN (OL k) (fun e => strictN (gI OL (oLab e) q) (upF OL f (oPar e)))) q
      (Nat.beq k 0) < 524288
    refine holderSev_nIf_lt hq ?_
    simp only [Fi24NetPt.strictN_eq]
    exact holderSev_upF_lt OL f _ _ (holderSev_gI_lt _ _ _)

private theorem holderSev_dnF_lt (OL : Nat → Nat) :
    ∀ (f k q : Nat), q < 524288 → dnF OL f k q < 524288
  | 0, _, _, hq => hq
  | f + 1, k, q, hq => by
    show Bool.rec (motive := fun _ => Nat)
      (strictN (OL k) (fun e => strictN (dnF OL f (oPar e) q) (gT OL (oLab e)))) q
      (Nat.beq k 0) < 524288
    refine holderSev_nIf_lt hq ?_
    simp only [Fi24NetPt.strictN_eq]
    exact holderSev_gT_lt _ _ _

private theorem holderSev_clsK_lt (hV : VN NW NT) (OL : Nat → Nat) (k : Nat) {p : Nat}
    (hp : p < 524288) : clsK OL NT k p < 524288 := by
  show strictN (upI OL k p) (fun y => strictN (ptF NT y) (dnT OL k)) < 524288
  simp only [Fi24NetPt.strictN_eq]
  refine holderSev_dnF_lt OL _ _ _ ?_
  rw [ptF_eq]
  exact pF_lt hV.1 (holderSev_upF_lt OL _ _ _ hp)

private theorem holderSev_cfgP (hV : VN NW NT) (OL : Nat → Nat) :
    ∀ (prog : List (Nat × Nat)) {Z n : Nat} {L : List Nat}, holderSevRp Z L → L.length = n →
      holderSevRp (cfgP OL NT prog n Z) (cfgL (clsK OL NT) L prog)
  | [], _, _, _, h, _ => h
  | p :: prog, Z, _, L, h, rfl => by
    have hx := holderSev_clsK_lt hV OL (L.getD p.1 0) (holderSev_getD_lt h p.2)
    have e1 : cfgP OL NT (p :: prog) L.length Z = strictN (clsK OL NT (getP Z p.1) (getP Z p.2))
        (fun x => strictN (putP Z L.length x) (cfgP OL NT prog (L.length + 1))) := rfl
    have e : cfgP OL NT (p :: prog) L.length Z = cfgP OL NT prog (L.length + 1)
        (putP Z L.length (clsK OL NT (L.getD p.1 0) (L.getD p.2 0))) := by
      rw [e1, Fi24NetPt.strictN_eq, holderSev_getP h, holderSev_getP h]
      exact Fi24NetPt.strictN_eq _ _
    rw [e]
    exact holderSev_cfgP hV OL prog (holderSev_putP h hx) (n := L.length + 1) (by simp)

private theorem holderSev_cfgT (hV : VN NW NT) (OL : Nat → Nat) (w : List Nat)
    (prog : List (Nat × Nat)) {q : Nat} (hq : q < 524288) :
    holderSevRp (cfgT NW NT OL w prog q) (cfgL (clsK OL NT) (tupL (cP NW NT w) q) prog) := by
  have hpw : ptC NW NT w = cP NW NT w := funext (ptC_eq NW NT w)
  have hf : ∀ y < 524288, ptC NW NT w y < 524288 := fun y hy => by
    rw [hpw]
    exact cP_lt hV w hy
  have hT : holderSevRp (tupP (ptC NW NT w) q) (tupL (cP NW NT w) q) := by
    have := holderSev_tupA hf 7 holderSev_nil rfl hq
    rw [List.nil_append] at this
    have e : tupL (cP NW NT w) q = tupN (ptC NW NT w) q 7 :=
      congrArg (fun f => tupN f q 7) hpw.symm
    rw [e]
    exact this
  exact holderSev_cfgP hV OL prog hT (by simp [tupL])

private theorem holderSev_nthD : ∀ (l : List Nat) (i : Nat), nthD (nat_lit 0) l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => holderSev_nthD l i

private theorem holderSev_lenL {α : Type} : ∀ (l : List α), lenL l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (holderSev_lenL l)

private theorem holderSev_notB {b : Bool} (h : notB b = true) : b = false := by
  cases b <;> simp_all [notB]

private theorem holderSev_take_tupN (f : Nat → Nat) (x : Nat) {n m : Nat} (h : n ≤ m) :
    (tupN f x m).take n = tupN f x n := by
  unfold tupN
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

private theorem holderSev_refOK (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {To q : Nat}
    {LT : List Nat} (hTo : holderSevRp To LT) (hq : q < 524288)
    {c : List (Nat × Nat) × Nat × Nat × Nat} (hn : c.2.2.2 ≤ LT.length)
    (h : refOK NW NT OL w To q c = true) :
    (cfgL (clsK OL NT) (tupN (ptC NW NT w) q c.2.2.2) c.1).getD c.2.1 0 =
        (cfgL (clsK OL NT) (tupN (ptC NW NT w) q c.2.2.2) c.1).getD c.2.2.1 0 ∧
      (cfgL (clsK OL NT) (LT.take c.2.2.2) c.1).getD c.2.1 0 ≠
        (cfgL (clsK OL NT) (LT.take c.2.2.2) c.1).getD c.2.2.1 0 := by
  have hf : ∀ y < 524288, ptC NW NT w y < 524288 := fun y hy => by
    rw [ptC_eq]
    exact cP_lt hV w hy
  unfold refOK at h
  simp only [letB_eq'] at h
  obtain ⟨h1, h2⟩ := andB_true' h
  have hTq : holderSevRp (tupA (ptC NW NT w) c.2.2.2 0 q 0) (tupN (ptC NW NT w) q c.2.2.2) := by
    have := holderSev_tupA hf c.2.2.2 holderSev_nil rfl hq
    rw [List.nil_append] at this
    exact this
  have hZq : holderSevRp (cfgP OL NT c.1 c.2.2.2 (tupA (ptC NW NT w) c.2.2.2 0 q 0))
      (cfgL (clsK OL NT) (tupN (ptC NW NT w) q c.2.2.2) c.1) :=
    holderSev_cfgP hV OL c.1 hTq (by simp [tupN])
  have hZo : holderSevRp (cfgP OL NT c.1 c.2.2.2 (Nat.land To (Nat.sub (Nat.shiftLeft (nat_lit 1)
      (Nat.mul c.2.2.2 (nat_lit 20))) (nat_lit 1)))) (cfgL (clsK OL NT) (LT.take c.2.2.2) c.1) :=
    holderSev_cfgP hV OL c.1 (holderSev_mask hTo c.2.2.2) (by simp only [List.length_take]; omega)
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.ne_of_beq_eq_false (holderSev_notB h2)
  refine ⟨(holderSev_getP hZq _).symm.trans (e1.trans (holderSev_getP hZq _)), fun e => e2 ?_⟩
  exact (holderSev_getP hZo _).trans (e.trans (holderSev_getP hZo _).symm)

private noncomputable def holderSevPick (Zc : Nat) (pos : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ A => A)
    (fun k _ ih i A => strictN (putP A i (getP Zc k)) (ih (Nat.succ i))) pos

private theorem holderSev_pick {Zc : Nat} {M : List Nat} (hZ : holderSevRp Zc M) :
    ∀ (pos : List Nat) {A i : Nat} {L : List Nat}, holderSevRp A L → L.length = i →
      holderSevRp (holderSevPick Zc pos i A) (L ++ pos.map fun k => M.getD k 0)
  | [], A, _, L, h, _ => by
    rw [List.map_nil, List.append_nil]
    exact h
  | k :: pos, A, _, L, h, rfl => by
    have e1 : holderSevPick Zc (k :: pos) L.length A =
        strictN (putP A L.length (getP Zc k)) (holderSevPick Zc pos (L.length + 1)) := rfl
    rw [e1, Fi24NetPt.strictN_eq, holderSev_getP hZ]
    have := holderSev_pick hZ pos (holderSev_putP h (holderSev_getD_lt hZ k)) (i := L.length + 1)
      (by simp)
    simpa using this

private theorem holderSev_mapP {C : Nat} {c : List Nat} (h : holderSevRp C c) {f : Nat → Nat}
    (hf : ∀ y < 524288, f y < 524288) :
    ∀ n, holderSevRp (mapP f n C) ((List.range n).map fun j => f (c.getD j 0))
  | 0 => holderSev_nil
  | n + 1 => by
    have e1 : mapP f (n + 1) C =
        strictN (mapP f n C) (fun A' => strictN (f (getP C n)) (putP A' n)) := rfl
    have e : mapP f (n + 1) C =
        putP (mapP f n C) ((List.range n).map fun j => f (c.getD j 0)).length (f (c.getD n 0)) := by
      rw [e1, Fi24NetPt.strictN_eq, holderSev_getP h, List.length_map, List.length_range]
      exact Fi24NetPt.strictN_eq _ _
    rw [e, List.range_succ, List.map_append, List.map_singleton]
    exact holderSev_putP (holderSev_mapP h hf n) (hf _ (holderSev_getD_lt h n))

private theorem holderSev_range_map (f : Nat → Nat) {c : List Nat} {n : Nat} (hn : c.length = n) :
    (List.range n).map (fun j => f (c.getD j 0)) = c.map f := by
  subst hn
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  rw [holderSev_getD_of_lt (by simpa using h1)]

private theorem holderSev_strip (hV : VN NW NT) : ∀ (ts : List (List Nat)) (i : Nat) {C : Nat}
    {c : List Nat}, holderSevRp C c → c.length = 6 → stripP NW NT ts i C < Nat.shiftLeft 1 120 →
      ∃ c', stripL NW NT ts i c = some c' ∧ holderSevRp (stripP NW NT ts i C) c'
  | [], _, _, c, h, _, _ => ⟨c, rfl, h⟩
  | t :: ts, i, C, c, h, hl, hlt => by
    have e1 : stripP NW NT (t :: ts) i C = Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 120)
        (strictN (mapP (ptC NW NT (invC t)) 6 C) (stripP NW NT ts (i + 1)))
        (andB (lvW i t) (Nat.beq (ptC NW NT t (nthD (nat_lit 0) cb i)) (getP C i))) := rfl
    have e : stripP NW NT (t :: ts) i C = Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 120)
        (stripP NW NT ts (i + 1) (mapP (ptC NW NT (invC t)) 6 C))
        (andB (lvW i t) (Nat.beq (ptC NW NT t (nthD (nat_lit 0) cb i)) (getP C i))) := by
      rw [e1, Fi24NetPt.strictN_eq]
    have hc : andB (lvW i t) (Nat.beq (ptC NW NT t (nthD (nat_lit 0) cb i)) (getP C i)) = true := by
      cases hc' : andB (lvW i t) (Nat.beq (ptC NW NT t (nthD (nat_lit 0) cb i)) (getP C i))
      · rw [e, hc'] at hlt
        exact absurd hlt (lt_irrefl _)
      · rfl
    obtain ⟨hlv, hb⟩ := andB_true' hc
    have e2 : stripP NW NT (t :: ts) i C =
        stripP NW NT ts (i + 1) (mapP (ptC NW NT (invC t)) 6 C) := by
      rw [e, hc]
    have hlev : ∀ l ∈ t, 4 * i ≤ l ∧ l < 26 := fun l hl => by
      obtain ⟨h1, h2⟩ := andB_true' (allL_spec hlv l hl)
      exact ⟨ble_true h1, blt_true h2⟩
    have hpt : cP NW NT t (cb.getD i 0) = c.getD i 0 := by
      have := Nat.eq_of_beq_eq_true hb
      rwa [ptC_eq, holderSev_nthD, holderSev_getP h] at this
    have hS : stripL NW NT (t :: ts) i c = stripL NW NT ts (i + 1) (c.map (cP NW NT (invC t))) := by
      show (if (∀ l ∈ t, 4 * i ≤ l ∧ l < 26) ∧ cP NW NT t (cb.getD i 0) = c.getD i 0 then
        stripL NW NT ts (i + 1) (c.map (cP NW NT (invC t))) else none) = _
      rw [if_pos ⟨hlev, hpt⟩]
    have hpi : ptC NW NT (invC t) = cP NW NT (invC t) := funext (ptC_eq NW NT _)
    have hM : holderSevRp (mapP (ptC NW NT (invC t)) 6 C) (c.map (cP NW NT (invC t))) := by
      have := holderSev_mapP h (f := ptC NW NT (invC t))
        (fun y hy => by rw [hpi]; exact cP_lt hV _ hy) 6
      rw [holderSev_range_map (ptC NW NT (invC t)) hl] at this
      rw [← hpi]
      exact this
    obtain ⟨c', hc', hR⟩ := holderSev_strip hV ts (i + 1) hM (by simp [hl])
      (by rw [← e2]; exact hlt)
    exact ⟨c', by rw [hS]; exact hc', by rw [e2]; exact hR⟩

theorem refsOK_spec (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {om : Nat} {reps : List Nat}
    {rf : List (List (Nat × Nat) × Nat × Nat × Nat)} (hom : om < 524288)
    (h : refsOK NW NT OL w om reps rf = true) :
    ∀ i < rf.length, reps.getD i 0 < 524288 → rf[i]!.2.2.2 ≤ 7 →
      (cfgL (clsK OL NT) (tupN (cP NW NT w) (reps.getD i 0) rf[i]!.2.2.2) rf[i]!.1).getD rf[i]!.2.1 0 =
        (cfgL (clsK OL NT) (tupN (cP NW NT w) (reps.getD i 0) rf[i]!.2.2.2) rf[i]!.1).getD
          rf[i]!.2.2.1 0 ∧
      (cfgL (clsK OL NT) (tupN (cP NW NT w) om rf[i]!.2.2.2) rf[i]!.1).getD rf[i]!.2.1 0 ≠
        (cfgL (clsK OL NT) (tupN (cP NW NT w) om rf[i]!.2.2.2) rf[i]!.1).getD rf[i]!.2.2.1 0 := by
  intro i hi hq hn
  unfold refsOK at h
  rw [letB_eq'] at h
  have hpw : ptC NW NT w = cP NW NT w := funext (ptC_eq NW NT w)
  have hf : ∀ y < 524288, ptC NW NT w y < 524288 := fun y hy => by
    rw [hpw]
    exact cP_lt hV w hy
  have hTo : holderSevRp (tupP (ptC NW NT w) om) (tupN (ptC NW NT w) om 7) := by
    have := holderSev_tupA hf 7 holderSev_nil rfl hom
    rw [List.nil_append] at this
    exact this
  have hj := allI_spec h i hi
  rw [show (nat_lit 0) + i = i from Nat.zero_add i, holderSev_nthD] at hj
  rw [getElem!_pos rf i hi] at hn ⊢
  obtain ⟨e1, e2⟩ := holderSev_refOK hV hTo hq (by simpa [tupN] using hn) hj
  rw [holderSev_take_tupN _ _ hn, hpw] at e2
  rw [hpw] at e1
  exact ⟨e1, e2⟩

theorem baseOK_spec (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {om : Nat}
    {prog : List (Nat × Nat)} {pos hw bs : List Nat} (hom : om < 524288)
    (h : baseOK NW NT OL w om prog pos hw bs = true) :
    pos.length = bs.length ∧ ∀ i < pos.length,
      cP NW NT hw (bs.getD i 0) = (cfgL (clsK OL NT) (tupL (cP NW NT w) om) prog).getD (pos.getD i 0) 0 := by
  unfold baseOK at h
  obtain ⟨h1, h2⟩ := andB_true' h
  rw [letB_eq'] at h2
  have hlen : pos.length = bs.length := by
    have := Nat.eq_of_beq_eq_true h1
    rwa [holderSev_lenL, holderSev_lenL] at this
  refine ⟨hlen, fun i hi => ?_⟩
  have hZ := holderSev_cfgT hV OL w prog hom
  have hj := allI_spec h2 i hi
  have e := Nat.eq_of_beq_eq_true hj
  rw [ptC_eq, show (nat_lit 0) + i = i from Nat.zero_add i, holderSev_nthD] at e
  rw [holderSev_getD_of_lt hi]
  exact e.trans (holderSev_getP hZ _)

theorem twinOK_spec (hV : VN NW NT) {OL : Nat → Nat} {w : List Nat} {q : Nat}
    {prog : List (Nat × Nat)} {pos : List Nat} {ts : List (List Nat)} (hq : q < 524288)
    (h : twinOK NW NT OL w q prog pos ts = true) :
    ts.length = 5 ∧ pos.length = 6 ∧ ∃ c, stripL NW NT ts 0
      (pos.map fun k => (cfgL (clsK OL NT) (tupL (cP NW NT w) q) prog).getD k 0) = some c ∧
      c.getD 5 0 ≠ 186844 ∧ c.getD 5 0 ≠ LN NW 24 186844 ∧ c.getD 5 0 ≠ LN NW 24 (LN NW 24 186844) := by
  unfold twinOK at h
  obtain ⟨h1, h2⟩ := andB_true' h
  obtain ⟨h3, h4⟩ := andB_true' h2
  rw [letB_eq'] at h4
  obtain ⟨h5, h6⟩ := andB_true' h4
  rw [letB_eq'] at h6
  obtain ⟨h7, h8⟩ := andB_true' h6
  obtain ⟨h9, h10⟩ := andB_true' h8
  have hts : ts.length = 5 := by
    have := Nat.eq_of_beq_eq_true h1
    rwa [holderSev_lenL] at this
  have hpos : pos.length = 6 := by
    have := Nat.eq_of_beq_eq_true h3
    rwa [holderSev_lenL] at this
  refine ⟨hts, hpos, ?_⟩
  have hZ := holderSev_cfgT hV OL w prog hq
  have hP : holderSevRp (pickP (cfgT NW NT OL w prog q) pos)
      (pos.map fun k => (cfgL (clsK OL NT) (tupL (cP NW NT w) q) prog).getD k 0) := by
    have := holderSev_pick hZ pos holderSev_nil rfl
    rw [List.nil_append] at this
    exact this
  have hlt : stripP NW NT ts 0 (pickP (cfgT NW NT OL w prog q) pos) < Nat.shiftLeft 1 120 :=
    blt_true h5
  obtain ⟨c, hc, hR⟩ := holderSev_strip hV ts 0 hP (by simp [hpos]) hlt
  have g5 := holderSev_getP hR 5
  have n7 := Nat.ne_of_beq_eq_false (holderSev_notB h7)
  have n9 := Nat.ne_of_beq_eq_false (holderSev_notB h9)
  have n10 := Nat.ne_of_beq_eq_false (holderSev_notB h10)
  refine ⟨c, hc, fun e => n7 (g5.trans e), fun e => n9 (g5.trans (e.trans ?_)),
    fun e => n10 (g5.trans (e.trans ?_))⟩
  · exact (letN_eq NW 24 186844).symm
  · rw [letN_eq, letN_eq]

end CFSG.KS.Fi24Sev

end
