module

public import Certificates.Data.Kernel.Spor.Fi24Net
public import Certificates.Data.Kernel.Spor.Fi24Orb
public import CFSG.Certificates.Kernel.KDense.SortSound
public import CFSG.Certificates.Kernel.Spor.SlpCard
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KS.Fi24Net

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KS.SC CFSG.KS.TW CFSG.Sporadic.Th.Native CFSG.KC.KDense.SortAux

theorem letB_eq' (v : Nat) (k : Nat → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases e : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true e) (by omega)

@[expose] def NV (M : Nat → Nat) : Prop := ∀ l < 37, ValidIn 524288 (ldist l) (M l)

@[expose] noncomputable def pF (M : Nat → Nat) : Nat → Nat := compF (fun l => swp (ldist l) (M l)) 0 37

@[expose] noncomputable def pR (M : Nat → Nat) : Nat → Nat := compF (fun l => swp (ldist (36 - l)) (M (36 - l))) 0 37

theorem nv_of_masksOK {M : Nat → Nat} (h : masksOK M = true) : NV M := by
  intro l hl
  unfold masksOK at h
  have h1 := recAll_right (P := fun l => dswValid (nat_lit 524288) (ldist l) (M l)) 37 h l hl
  obtain ⟨h4, h5⟩ := andB_true h1
  simp only [Nat.beq_eq] at h4 h5
  exact validIn_of_dsw h4 h5

theorem netF_eq (M : Nat → Nat) (v : Nat) :
    netF M v = iterF (fun l y => dsw (ldist l) (M l) y) 0 37 v :=
  rec_strictN (fun l y => dsw (ldist l) (M l) y) 36 37 (by decide) v

theorem netR_eq (M : Nat → Nat) (v : Nat) :
    netR M v = iterF (fun l y => dsw (ldist (36 - l)) (M (36 - l)) y) 0 37 v :=
  rec_strictN (fun l y => dsw (ldist (36 - l)) (M (36 - l)) y) 36 37 (by decide) v

theorem testBit_netF {M : Nat → Nat} (h : NV M) (v q : Nat) :
    (netF M v).testBit q = v.testBit (pF M q) := by
  rw [netF_eq]
  exact testBit_iterF (f := fun l y => dsw (ldist l) (M l) y) (τ := fun l => swp (ldist l) (M l))
    (c := 37) (fun i hi y q => testBit_dsw (validIn_disj (h i hi)) y q) 0 37 (Nat.le_refl _) v q

theorem testBit_netR {M : Nat → Nat} (h : NV M) (v q : Nat) :
    (netR M v).testBit q = v.testBit (pR M q) := by
  rw [netR_eq]
  exact testBit_iterF (f := fun l y => dsw (ldist (36 - l)) (M (36 - l)) y)
    (τ := fun l => swp (ldist (36 - l)) (M (36 - l))) (c := 37)
    (fun i hi y q => testBit_dsw (validIn_disj (h (36 - i) (by omega))) y q) 0 37 (Nat.le_refl _) v q

theorem swp_inv {M : Nat → Nat} (h : NV M) :
    ∀ i < 37, ∀ q, swp (ldist i) (M i) (swp (ldist i) (M i) q) = q :=
  fun i hi q => swp_swp (validIn_disj (h i hi)) q

theorem pR_pF {M : Nat → Nat} (h : NV M) (q : Nat) : pR M (pF M q) = q :=
  compF_rev (τ := fun l => swp (ldist l) (M l)) 37 (swp_inv h) q

theorem pF_pR {M : Nat → Nat} (h : NV M) (q : Nat) : pF M (pR M q) = q :=
  compF_rev' (τ := fun l => swp (ldist l) (M l)) 37 (swp_inv h) q

theorem pF_lt {M : Nat → Nat} (h : NV M) {q : Nat} (hq : q < 524288) : pF M q < 524288 :=
  compF_lt (τ := fun l => swp (ldist l) (M l)) (c := 37) (fun i hi _ hr => swp_lt (h i hi) hr)
    0 37 (Nat.le_refl _) q hq

theorem pR_lt {M : Nat → Nat} (h : NV M) {q : Nat} (hq : q < 524288) : pR M q < 524288 :=
  compF_lt (τ := fun l => swp (ldist (36 - l)) (M (36 - l))) (c := 37)
    (fun i hi _ hr => swp_lt (h (36 - i) (by omega)) hr) 0 37 (Nat.le_refl _) q hq

theorem testBit_idPl {k : Nat} (hk : k < 19) (p : Nat) :
    (idPl k).testBit p = (decide (p < 524288) && p.testBit k) :=
  idPlane_testBit (k := 19) hk p

theorem tpl_testBit {k : Nat} (hk : k < 19) {y : Nat} (hy : y < 524288) :
    (tpl k).testBit y = if k = 0 then y.testBit 0 else (y.testBit k ^^ y.testBit 0) := by
  by_cases k0 : k = 0
  · subst k0
    rw [if_pos rfl]
    change (idPl 0).testBit y = _
    rw [testBit_idPl (by decide), decide_eq_true hy, Bool.true_and]
  · have e : tpl k = Nat.xor (idPl k) (idPl 0) := by
      unfold tpl
      rw [beq_false k0]
    rw [e, if_neg k0, nxor, Nat.testBit_xor, testBit_idPl hk, testBit_idPl (by decide),
      decide_eq_true hy, Bool.true_and, Bool.true_and]

theorem eq_of_planes {a b : Nat} (ha : a < 524288) (hb : b < 524288)
    (h : ∀ k < 19, a.testBit k = b.testBit k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 19
  · exact h i hi
  · have h19 : (524288 : Nat) ≤ 2 ^ i := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem perm_of_tpl {f g : Nat → Nat} (hf : ∀ q < 524288, f q < 524288)
    (hg : ∀ q < 524288, g q < 524288)
    (h : ∀ k < 19, ∀ q < 524288, (tpl k).testBit (f q) = (tpl k).testBit (g q)) :
    ∀ q < 524288, f q = g q := by
  intro q hq
  have h0 := h 0 (by decide) q hq
  rw [tpl_testBit (by decide) (hf q hq), tpl_testBit (by decide) (hg q hq), if_pos rfl,
    if_pos rfl] at h0
  apply eq_of_planes (hf q hq) (hg q hq)
  intro k hk
  by_cases k0 : k = 0
  · subst k0
    exact h0
  · have e := h k hk q hq
    rw [tpl_testBit hk (hf q hq), tpl_testBit hk (hg q hq), if_neg k0, if_neg k0, h0] at e
    revert e
    cases (f q).testBit k <;> cases (g q).testBit k <;> cases (g q).testBit 0 <;> decide

theorem lidx_eq (m : Nat) :
    lidx m = if m = 1 ∨ m = 3 then 0 else if m ≤ 2 ∨ m = 4 then 1 else m - 3 := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ 5 ≤ m) with h | h | h | h | h | h
  · subst h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · subst h
    rfl
  · unfold lidx
    rw [beq_false (by omega : m ≠ 1), beq_false (by omega : m ≠ 3), ble_false (by omega : 2 < m),
      beq_false (by omega : m ≠ 4), if_neg (by omega), if_neg (by omega)]
    rfl

theorem lidx_ge {m : Nat} (h : 3 ≤ m) : lidx m = m - 3 := by
  rw [lidx_eq]
  split_ifs <;> omega

@[expose] noncomputable def lP (NW : Nat → Nat → Nat) : Int → Nat → Nat
  | Int.ofNat m => if m = 0 then pR (NW (lidx m)) else pF (NW (lidx m))
  | Int.negSucc n => if n = 0 then pF (NW 0) else pR (NW (lidx (n + 1)))

@[expose] noncomputable def GN (NW : Nat → Nat → Nat) (z : Int) : Nat → Nat :=
  if z = 1 ∨ z = -1 then pF (NW 0) else if z = 2 then pF (NW 1) else pR (NW 1)

@[expose] noncomputable def LN (NW : Nat → Nat → Nat) (l : Nat) : Nat → Nat :=
  if l % 2 = 0 then pF (NW (l / 2)) else pR (NW (l / 2))

theorem LN_even (NW : Nat → Nat → Nat) (j : Nat) : LN NW (2 * j) = pF (NW j) := by
  have e1 : 2 * j % 2 = 0 := by omega
  have e2 : 2 * j / 2 = j := by omega
  rw [LN, if_pos e1, e2]

theorem LN_odd (NW : Nat → Nat → Nat) (j : Nat) : LN NW (2 * j + 1) = pR (NW j) := by
  have e1 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have e2 : (2 * j + 1) / 2 = j := by omega
  rw [LN, if_neg e1, e2]

theorem testBit_appL {NW : Nat → Nat → Nat} (z : Int) (hz : NV (NW (lidx z.natAbs))) (v q : Nat) :
    (appL NW z v).testBit q = v.testBit (lP NW z q) := by
  cases z with
  | ofNat m =>
    have e1 : appL NW (Int.ofNat m) v = Bool.rec (motive := fun _ => Nat) (netF (NW (lidx m)) v)
        (netR (NW (lidx m)) v) (Nat.beq m 0) := rfl
    rw [e1]
    by_cases hm : m = 0
    · subst hm
      have e2 : lP NW (Int.ofNat 0) = pR (NW (lidx 0)) := if_pos rfl
      rw [e2]
      exact testBit_netR hz v q
    · have e2 : lP NW (Int.ofNat m) = pF (NW (lidx m)) := if_neg hm
      rw [e2, beq_false hm]
      exact testBit_netF hz v q
  | negSucc n =>
    have e1 : appL NW (Int.negSucc n) v = Bool.rec (motive := fun _ => Nat)
        (netR (NW (lidx (Nat.succ n))) v) (netF (NW 0) v) (Nat.beq n 0) := rfl
    rw [e1]
    by_cases hn : n = 0
    · subst hn
      have e2 : lP NW (Int.negSucc 0) = pF (NW 0) := if_pos rfl
      rw [e2]
      exact testBit_netF hz v q
    · have e2 : lP NW (Int.negSucc n) = pR (NW (lidx (n + 1))) := if_neg hn
      rw [e2, beq_false hn]
      exact testBit_netR hz v q

theorem lP_lt {NW : Nat → Nat → Nat} (z : Int) (hz : NV (NW (lidx z.natAbs))) {q : Nat}
    (hq : q < 524288) : lP NW z q < 524288 := by
  cases z with
  | ofNat m =>
    by_cases hm : m = 0
    · have e2 : lP NW (Int.ofNat m) = pR (NW (lidx m)) := if_pos hm
      rw [e2]
      exact pR_lt hz hq
    · have e2 : lP NW (Int.ofNat m) = pF (NW (lidx m)) := if_neg hm
      rw [e2]
      exact pF_lt hz hq
  | negSucc n =>
    by_cases hn : n = 0
    · subst hn
      have e2 : lP NW (Int.negSucc 0) = pF (NW 0) := if_pos rfl
      rw [e2]
      exact pF_lt hz hq
    · have e2 : lP NW (Int.negSucc n) = pR (NW (lidx (n + 1))) := if_neg hn
      rw [e2]
      exact pR_lt hz hq

theorem lP_eq (NW : Nat → Nat → Nat) (z : Int) : lP NW z = slpG (GN NW) (LN NW) z := by
  funext q
  cases z with
  | ofNat m =>
    have ea : (Int.ofNat m).natAbs = m := rfl
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ 3 ≤ m) with h | h | h | h
    · subst h
      rfl
    · subst h
      rfl
    · subst h
      rfl
    · have hm : m ≠ 0 := by omega
      have e1 : lP NW (Int.ofNat m) = pF (NW (m - 3)) := by
        rw [← lidx_ge h]
        exact if_neg hm
      have hp : (0 : Int) < Int.ofNat m := by
        rw [Int.ofNat_eq_coe]
        omega
      rw [e1, slpG, ea, if_neg (by omega), if_pos hp, LN_even]
  | negSucc n =>
    have ea : (Int.negSucc n).natAbs = n + 1 := rfl
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with h | h | h
    · subst h
      rfl
    · subst h
      rfl
    · have hn : n ≠ 0 := by omega
      have e1 : lP NW (Int.negSucc n) = pR (NW (n + 1 - 3)) := by
        rw [← lidx_ge (by omega : 3 ≤ n + 1)]
        exact if_neg hn
      have hp : ¬ (0 : Int) < Int.negSucc n := by
        rw [Int.negSucc_eq]
        omega
      rw [e1, slpG, ea, if_neg (by omega), if_neg hp, LN_odd]

theorem testBit_walkW {NW : Nat → Nat → Nat} : ∀ (w : List Int), (∀ z ∈ w, NV (NW (lidx z.natAbs))) →
    ∀ v q, (walkW NW w v).testBit q = v.testBit (w.foldr (lP NW) q)
  | [], _, _, _ => rfl
  | z :: w, h, v, q => by
    have e : walkW NW (z :: w) v = walkW NW w (appL NW z v) := strictN_eq _ _
    rw [e, testBit_walkW w (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) (appL NW z v) q,
      testBit_appL z (h z List.mem_cons_self) v]
    rfl

theorem foldr_lt {NW : Nat → Nat → Nat} : ∀ (w : List Int), (∀ z ∈ w, NV (NW (lidx z.natAbs))) →
    ∀ q < 524288, w.foldr (lP NW) q < 524288
  | [], _, _, hq => hq
  | z :: w, h, q, hq =>
    lP_lt z (h z List.mem_cons_self) (foldr_lt w (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) q hq)

theorem net_spec {M : Nat → Nat} (h : netOK M = true) :
    NV M ∧ ∀ q < 524288, (pF M q < 306936 ↔ q < 306936) := by
  obtain ⟨h1, h2⟩ := andB_true h
  have hv := nv_of_masksOK h1
  refine ⟨hv, fun q hq => ?_⟩
  have e : (netF M (Nat.xor ptsM (idPl 0))).testBit q = (Nat.xor ptsM (netF M (idPl 0))).testBit q := by
    rw [Nat.eq_of_beq_eq_true h2]
  have hp := pF_lt hv hq
  rw [testBit_netF hv, nxor, nxor, Nat.testBit_xor, Nat.testBit_xor, testBit_netF hv, ptsM,
    testBit_ones, testBit_ones] at e
  have e' : decide (pF M q < 306936) = decide (q < 306936) := by
    revert e
    cases decide (pF M q < 306936) <;> cases decide (q < 306936) <;>
      cases (idPl 0).testBit (pF M q) <;> decide
  exact decide_eq_decide.mp e'

theorem word_spec {NW : Nat → Nat → Nat} {w : List Int} {j : Nat} (hj : NV (NW j))
    (hw : ∀ z ∈ w, NV (NW (lidx z.natAbs))) (h : ∀ k < 19, wordOK NW w j k = true) :
    ∀ q < 524288, pF (NW j) q = w.foldr (lP NW) q := by
  refine perm_of_tpl (fun q hq => pF_lt hj hq) (fun q hq => foldr_lt w hw q hq) ?_
  intro k hk q _
  have e := h k hk
  unfold wordOK at e
  rw [letB_eq'] at e
  have e2 : (walkW NW w (tpl k)).testBit q = (netF (NW j) (tpl k)).testBit q := by
    rw [Nat.eq_of_beq_eq_true e]
  rw [testBit_walkW w hw, testBit_netF hj] at e2
  exact e2.symm

private theorem bIf_true {c t : Bool} (h : bIf(c, t, true) = true) (hc : c = true) : t = true := by
  subst hc
  exact h

private theorem allBelow_spec {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; exact absurd hl (Nat.not_lt_zero l)
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := andB_true hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with hl | rfl
      · exact ih h2 l hl hlm
      · exact bIf_true h1 (Nat.blt_eq.mpr hlm)
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; exact absurd hhh (Nat.not_lt_zero hh)
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := andB_true hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hhh) with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by decide)) (by rw [e]; exact him)
  rwa [e] at this

private theorem nIf_true {c : Bool} (t e : Nat) (hc : c = true) : nIf(c, t, e) = t := by
  subst hc
  rfl

private theorem nIf_false {c : Bool} (t e : Nat) (hc : c = false) : nIf(c, t, e) = e := by
  subst hc
  rfl

private theorem testBit_blk (P c : Nat) {r : Nat} (hr : r < 512) :
    (CFSG.KC.Fi24Net.blk P c).testBit r = P.testBit (512 * c + r) := by
  unfold CFSG.KC.Fi24Net.blk
  rw [nland, Nat.testBit_and, nshr, Nat.testBit_shiftRight, nmul, testBit_ones, decide_eq_true hr,
    Bool.and_true, Nat.mul_comm c 512]

private theorem testBit_eq_of_blk {P G c r : Nat} (hr : r < 512)
    (e : CFSG.KC.Fi24Net.blk P c = G) : P.testBit (512 * c + r) = G.testBit r := by
  rw [← testBit_blk P c hr, e]

private theorem testBit_genBlk (OT : Nat → Nat) (b k Q c : Nat) {r : Nat} (hr : r < 512) :
    (genBlk OT b k Q c).testBit r =
      ((decide (512 * c + r < 306936) && (OT c).testBit (64 * r + (b + k))) ||
        Q.testBit (512 * c + r)) := by
  have hraw : (rawPlane (OT c) 64 512 9 0 (b + k)).testBit r =
      (OT c).testBit (64 * r + (b + k)) := by
    rw [testBit_rawPlane (rec := 64) (n := 512) (h := 9) (by decide) (by decide) r,
      decide_eq_true hr, Bool.true_and]
  unfold genBlk
  rw [nlor, Nat.testBit_or, testBit_blk Q c hr, nadd]
  by_cases h599 : c < 599
  · rw [nIf_true _ _ (Nat.blt_eq.mpr (by omega : c < 600)), nIf_true _ _ (Nat.blt_eq.mpr h599),
      nland, Nat.testBit_and, hraw, testBit_ones, decide_eq_true hr, Bool.and_true,
      decide_eq_true (by omega : 512 * c + r < 306936), Bool.true_and]
  · by_cases h600 : c = 599
    · subst h600
      rw [nIf_true _ _ (Nat.blt_eq.mpr (by decide : 599 < 600)),
        nIf_false _ _ (by decide : Nat.blt 599 599 = false), nland, Nat.testBit_and, hraw,
        testBit_ones]
      by_cases hr2 : r < 248
      · rw [decide_eq_true hr2, decide_eq_true (by omega : 512 * 599 + r < 306936), Bool.and_true,
          Bool.true_and]
      · rw [decide_eq_false hr2, decide_eq_false (by omega : ¬ 512 * 599 + r < 306936),
          Bool.and_false, Bool.false_and]
    · have hb : Nat.blt c 600 = false :=
        Bool.eq_false_iff.mpr fun h => (by omega : ¬ c < 600) (Nat.blt_eq.mp h)
      rw [nIf_false _ _ hb, Nat.zero_testBit, decide_eq_false (by omega : ¬ 512 * c + r < 306936),
        Bool.false_and]

theorem genOK_spec {OT M : Nat → Nat} {b k : Nat} (h : genOK OT M b k = true) {x : Nat}
    (hx : x < 524288) :
    (nIf(Nat.beq k (nat_lit 0), netF M (tpl k), Nat.xor (netF M (tpl k)) (netF M (idPl (nat_lit 0))))).testBit x =
      if x < 306936 then (OT (x / 512)).testBit (64 * (x % 512) + (b + k)) else (idPl k).testBit x := by
  unfold genOK at h
  rw [letB_eq', letB_eq', letB_eq'] at h
  have hr : x % 512 < 512 := Nat.mod_lt _ (by decide)
  have hx' : 512 * (x / 512) + x % 512 = x := Nat.div_add_mod x 512
  have e := Nat.eq_of_beq_eq_true
    (allBelow_spec h (x / 512) (by omega : x / 512 < 1024) (by omega : x / 512 < 64 * 16))
  have e2 := testBit_eq_of_blk hr e
  rw [testBit_genBlk _ _ _ _ _ hr, hx'] at e2
  have hpad : padM.testBit x = !decide (x < 306936) := by
    unfold padM
    rw [nxor, Nat.testBit_xor, testBit_ones, testBit_ones, decide_eq_true hx]
    cases decide (x < 306936) <;> rfl
  rw [e2, nland, Nat.testBit_and, hpad]
  by_cases hp : x < 306936
  · rw [if_pos hp, decide_eq_true hp]
    simp
  · rw [if_neg hp, decide_eq_false hp]
    simp

theorem gen_spec {OT M : Nat → Nat} {b k : Nat} (hv : NV M) (hk : k < 19) (h : genOK OT M b k = true)
    {x : Nat} (hx : x < 524288) :
    (pF M x).testBit k = if x < 306936 then (OT (x / 512)).testBit (64 * (x % 512) + (b + k))
      else x.testBit k := by
  have e := genOK_spec h hx
  have hp := pF_lt hv hx
  have lhs : (nIf(Nat.beq k (nat_lit 0), netF M (tpl k),
      Nat.xor (netF M (tpl k)) (netF M (idPl (nat_lit 0))))).testBit x = (pF M x).testBit k := by
    by_cases k0 : k = 0
    · subst k0
      change (netF M (tpl 0)).testBit x = _
      rw [testBit_netF hv, tpl_testBit (by decide) hp, if_pos rfl]
    · have e' : nIf(Nat.beq k (nat_lit 0), netF M (tpl k),
          Nat.xor (netF M (tpl k)) (netF M (idPl (nat_lit 0)))) =
          Nat.xor (netF M (tpl k)) (netF M (idPl 0)) := by
        rw [beq_false k0]
      rw [e', nxor, Nat.testBit_xor, testBit_netF hv, testBit_netF hv, tpl_testBit hk hp, if_neg k0,
        testBit_idPl (by decide), decide_eq_true hp, Bool.true_and, Bool.xor_assoc, Bool.xor_self,
        Bool.xor_false]
  rw [← lhs, e]
  by_cases hn : x < 306936
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn, testBit_idPl hk, decide_eq_true hx, Bool.true_and]

@[expose] noncomputable def OLf (OT : Nat → Nat) (x : Nat) : Nat :=
  fld(OT (Nat.shiftRight x (nat_lit 9)), Nat.mul (Nat.land x (nat_lit 511)) (nat_lit 64),
    nat_lit 18446744073709551615)

theorem OLf_testBit (OT : Nat → Nat) (x : Nat) {i : Nat} (hi : i < 64) :
    (OLf OT x).testBit i = (OT (x / 512)).testBit (64 * (x % 512) + i) := by
  have e1 : Nat.shiftRight x 9 = x / 2 ^ 9 := Nat.shiftRight_eq_div_pow x 9
  have e2 : Nat.land x 511 = x % 2 ^ 9 := Nat.and_two_pow_sub_one_eq_mod x 9
  have e3 : ∀ y, Nat.land y (nat_lit 18446744073709551615) = y % 2 ^ 64 :=
    fun y => Nat.and_two_pow_sub_one_eq_mod y 64
  unfold OLf
  rw [e1, e2, e3, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, nshr,
    Nat.testBit_shiftRight, nmul, Nat.mul_comm (x % 2 ^ 9) 64]
  rfl

theorem gen_alpha {OT M : Nat → Nat} (hv : NV M) (h : ∀ k < 19, genOK OT M 0 k = true) {x : Nat}
    (hx : x < 306936) : pF M x = CFSG.KC.Fi24Orb.oA (OLf OT x) := by
  have hx' : x < 524288 := by omega
  have hlt : CFSG.KC.Fi24Orb.oA (OLf OT x) < 524288 := land_ones_lt (OLf OT x) 19
  refine eq_of_planes (pF_lt hv hx') hlt fun k hk => ?_
  rw [gen_spec hv hk (h k hk) hx', if_pos hx, Nat.zero_add]
  have e3 : ∀ y, Nat.land y (nat_lit 524287) = y % 2 ^ 19 := fun y => Nat.and_two_pow_sub_one_eq_mod y 19
  unfold CFSG.KC.Fi24Orb.oA
  rw [e3, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, OLf_testBit OT x (by omega)]

theorem gen_beta {OT M : Nat → Nat} (hv : NV M) (h : ∀ k < 19, genOK OT M 19 k = true) {x : Nat}
    (hx : x < 306936) : pF M x = CFSG.KC.Fi24Orb.oB (OLf OT x) := by
  have hx' : x < 524288 := by omega
  have hlt : CFSG.KC.Fi24Orb.oB (OLf OT x) < 524288 := land_ones_lt _ 19
  refine eq_of_planes (pF_lt hv hx') hlt fun k hk => ?_
  rw [gen_spec hv hk (h k hk) hx', if_pos hx]
  have e3 : ∀ y, Nat.land y (nat_lit 524287) = y % 2 ^ 19 := fun y => Nat.and_two_pow_sub_one_eq_mod y 19
  unfold CFSG.KC.Fi24Orb.oB
  rw [e3, Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, nshr, Nat.testBit_shiftRight,
    OLf_testBit OT x (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) (by decide))]

theorem nets_facts {NW : Nat → Nat → Nat} (hn : ∀ j < 13, netOK (NW j) = true) {j : Nat} (hj : j < 13)
    {x : Nat} (hx : x < 306936) :
    pF (NW j) x < 306936 ∧ pR (NW j) x < 306936 ∧ pR (NW j) (pF (NW j) x) = x ∧
      pF (NW j) (pR (NW j) x) = x := by
  obtain ⟨hv, hpt⟩ := net_spec (hn j hj)
  refine ⟨(hpt x (by omega)).2 hx, ?_, pR_pF hv x, pF_pR hv x⟩
  have := (hpt _ (pR_lt hv (by omega : x < 524288))).1
  rw [pF_pR hv] at this
  exact this hx

theorem gens_spec {NW : Nat → Nat → Nat} {OT : Nat → Nat} (hn : ∀ j < 13, netOK (NW j) = true)
    (hg : ∀ g < 38, genOK OT (NW (g / 19)) (19 * (g / 19)) (g % 19) = true) {x : Nat}
    (hx : x < 306936) :
    pF (NW 0) x = CFSG.KC.Fi24Orb.oA (OLf OT x) ∧ pF (NW 1) x = CFSG.KC.Fi24Orb.oB (OLf OT x) := by
  refine ⟨gen_alpha (net_spec (hn 0 (by decide))).1 (fun k hk => ?_) hx,
    gen_beta (net_spec (hn 1 (by decide))).1 (fun k hk => ?_) hx⟩
  · have := hg k (by omega)
    rwa [Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk] at this
  · have := hg (19 + k) (by omega)
    have e1 : (19 + k) / 19 = 1 := by omega
    have e2 : (19 + k) % 19 = k := by omega
    rwa [e1, e2] at this

theorem letters_spec {NW : Nat → Nat → Nat} {words : Array (List Int)} {gens : Int → Table}
    (hn : ∀ j < 13, netOK (NW j) = true)
    (hw : ∀ g < 209, wordOK NW (words[2 + g / 19]!) (2 + g / 19) (g % 19) = true)
    (hs : words.size = 13) (h0 : words[0]! = [1]) (h1 : words[1]! = [2])
    (hok : ∀ j < 13, ∀ z ∈ words[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3))
    (hgen : ∀ z, ∀ x < 306936, ap (gens z) x = GN NW z x ∧ GN NW z x < 306936) :
    (CFSG.Sporadic.Fi23.Native.slpLetters 306936 gens words).size = 26 ∧
      ∀ l < 26, ∀ x < 306936, ap (CFSG.Sporadic.Fi23.Native.slpLetters 306936 gens words)[l]! x =
        LN NW l x := by
  have hv : ∀ j < 13, NV (NW j) := fun j hj => (net_spec (hn j hj)).1
  have hlz : ∀ j < 13, ∀ z ∈ words[j]!, lidx z.natAbs < 13 := by
    intro j hj z hz
    obtain ⟨-, hz1⟩ := hok j hj z hz
    rw [lidx_eq]
    split_ifs <;> omega
  have hwd : ∀ j, 2 ≤ j → j < 13 → ∀ q < 524288, pF (NW j) q = (words[j]!).foldr (lP NW) q := by
    intro j hj1 hj2
    refine word_spec (hv j hj2) (fun z hz => hv _ (hlz j hj2 z hz)) fun k hk => ?_
    have := hw (19 * (j - 2) + k) (by omega)
    have e1 : 2 + (19 * (j - 2) + k) / 19 = j := by omega
    have e2 : (19 * (j - 2) + k) % 19 = k := by omega
    rwa [e1, e2] at this
  have hlP : lP NW = slpG (GN NW) (LN NW) := funext (lP_eq NW)
  obtain ⟨s1, s2⟩ := slpLetters_get (n := 306936) (gens := gens) (words := words) (G := GN NW)
    (L := LN NW) (by decide) hgen (fun j hj => hok j (hs ▸ hj))
    (fun j hj x hx => by
      rw [hs] at hj
      rw [LN_even]
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with e | e | e
      · subst e
        rw [h0]
        rfl
      · subst e
        rw [h1]
        rfl
      · rw [hwd j e hj x (by omega), hlP])
    (fun j hj x hx => by
      rw [hs] at hj
      rw [LN_even, LN_odd]
      exact ⟨(nets_facts hn hj hx).1, (nets_facts hn hj hx).2.1, (nets_facts hn hj hx).2.2.1⟩)
  rw [hs] at s1 s2
  exact ⟨s1, s2⟩

end CFSG.KS.Fi24Net

end
