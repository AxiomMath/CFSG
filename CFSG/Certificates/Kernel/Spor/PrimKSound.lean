module

public import Certificates.Data.Kernel.Spor.PrimK
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import Certificates.Data.CFSGNative.J1.Prim
public import CFSG.Certificates.Kernel.Spor.VOrbReplay
import CFSG.Certificates.Kernel.Spor.DerSearch
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.PR

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.TBfs CFSG.Perm.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.J1.Native

@[expose] def subStep (n : Nat) (letters : Array Table) (lv : Array Nat)
    (s : Array Nat × Array Nat × Array Tree) (p : Nat) : Array Nat × Array Nat × Array Tree :=
  if (s.1[p]! == n) = true then
    ((treeBFS n p letters lv).pts.foldl (fun lab q => lab.set! q.toNat s.2.1.size) s.1,
      s.2.1.push p, s.2.2.push (treeBFS n p letters lv))
  else s

theorem suborbits_fold (n : Nat) (letters : Array Table) (lv : Array Nat) :
    suborbits n letters lv = (List.range n).foldl (subStep n letters lv)
      (Array.replicate n n, #[], #[]) := by
  unfold suborbits
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', CFSG.KS.DS.ite_pure_yieldD,
    List.forIn_pure_yield_eq_foldl, Array.forIn_pure_yield_eq_foldl, pure_bind]
  have h1 : ∀ a b : Nat, [a:b].size = b - a := fun a b => by simp [Std.Legacy.Range.size]
  simp only [h1, Nat.sub_zero, ← List.range_eq_range']
  rfl

theorem fold_set (v : Nat) : ∀ (xs : List UInt32) (lab : Array Nat),
    (xs.foldl (fun lab q => lab.set! q.toNat v) lab).size = lab.size ∧
      ∀ z < lab.size, (xs.foldl (fun lab q => lab.set! q.toNat v) lab)[z]! =
        if ∃ x ∈ xs, x.toNat = z then v else lab[z]!
  | [], lab => ⟨rfl, fun z _ => by simp⟩
  | x :: xs, lab => by
    obtain ⟨h1, h2⟩ := fold_set v xs (lab.set! x.toNat v)
    rw [CFSG.KS.SporSch.LyM.size_setR] at h1 h2
    refine ⟨h1, fun z hz => ?_⟩
    rw [List.foldl_cons, h2 z hz, CFSG.KS.SporSch.LyM.get_setR _ _ _ hz]
    by_cases e : z = x.toNat
    · simp [e]
    · by_cases hx : ∃ y ∈ xs, y.toNat = z
      · simp [hx]
      · have : ¬ ∃ y ∈ x :: xs, y.toNat = z := by
          rintro ⟨y, hy, rfl⟩
          rcases List.mem_cons.1 hy with rfl | hy
          · exact e rfl
          · exact hx ⟨y, hy, rfl⟩
        simp only [hx, this, e, ↓reduceIte]

theorem walkF_mono (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) (q : List Nat) :
    ∀ k f, k ≤ f → walkF L PAR LAB f k q = walkF L PAR LAB k k q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f hf
    rcases k with _ | k
    · rcases f with _ | f
      · rfl
      · rw [walkF_succ, ite_eq_right (by omega)]
        rfl
    · obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [walkF_succ, walkF_succ]
      split
      · next hc =>
        rw [ih _ hc.2 f (by omega), ih _ hc.2 k (by omega)]
      · rfl

theorem walkF_map (L : Nat → Nat → Nat) (PAR LAB : Nat → Nat) : ∀ f k (q : List Nat),
    walkF L PAR LAB f k q = q.map fun x => (walkF L PAR LAB f k [x]).getD 0 0
  | 0, k, q => by simp [walkF]
  | f + 1, k, q => by
    simp only [walkF_succ]
    by_cases hc : 0 < k ∧ r32 PAR k < k
    · simp only [hc, and_self, ↓reduceIte, mapK_eq]
      rw [walkF_map L PAR LAB f _ q, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      rw [walkF_map L PAR LAB f _ [x]]
      simp
    · simp only [hc, ↓reduceIte]
      simp

theorem walk_val {n cnt0 NL : Nat} {letters : Array Table} {L : Nat → Nat → Nat}
    {PTS0 POS0 PAR0 LAB0 : Nat → Nat}
    (hL : ∀ l < NL, ∀ x < n, ap letters[l]! x = L l x ∧ L l x < n)
    (hlab0 : ∀ q < cnt0, 0 < q → r32 PAR0 q < q → r32 LAB0 q < NL) :
    ∀ k < cnt0, ∀ q : Array Nat, (∀ x ∈ q, x < n) →
      walk (tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0) letters k q =
        q.map (fun x => (walkK L PAR0 LAB0 k [x]).getD 0 0) ∧
      ∀ x ∈ q, (walkK L PAR0 LAB0 k [x]).getD 0 0 < n := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    have hpar : ap (tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0).par k = r32 PAR0 k := ap_ofFn hk
    have hlab : ap (tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0).lab k = r32 LAB0 k := ap_ofFn hk
    have hW : ∀ x, (walkK L PAR0 LAB0 k [x]).getD 0 0 = if 0 < k ∧ r32 PAR0 k < k then
        L (r32 LAB0 k) ((walkK L PAR0 LAB0 (r32 PAR0 k) [x]).getD 0 0) else x := by
      intro x
      unfold walkK
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0]
        simp [walkF]
      · obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hj, walkF_succ]
        by_cases hc : 0 < j + 1 ∧ r32 PAR0 (j + 1) < j + 1
        · rw [ite_eq_left hc, ite_eq_left hc, walkF_mono _ _ _ _ _ j (by omega), mapK_eq,
            walkF_map L PAR0 LAB0 _ _ [x]]
          simp
        · rw [ite_eq_right hc, ite_eq_right hc]
          rfl
    rw [walk, hpar, hlab]
    by_cases hc : 0 < k ∧ r32 PAR0 k < k
    · rw [dite_eq_left hc]
      obtain ⟨e1, e2⟩ := ih _ hc.2 (by omega) q hq
      have hl := hlab0 k hk hc.1 hc.2
      rw [CFSG.KS.TW.apT_map, e1, Array.map_map]
      refine ⟨Array.map_eq_map_iff.2 fun x hx => ?_, fun x hx => ?_⟩
      · simp only [Function.comp_apply]
        rw [hW, ite_eq_left hc, (hL _ hl _ (e2 x hx)).1]
      · rw [hW, ite_eq_left hc]
        exact (hL _ hl _ (e2 x hx)).2
    · rw [dite_eq_right hc]
      refine ⟨?_, fun x hx => by rw [hW, ite_eq_right hc]; exact hq x hx⟩
      conv_lhs => rw [← Array.map_id q]
      exact Array.map_eq_map_iff.2 fun x _ => by rw [hW, ite_eq_right hc]; rfl

theorem bitK_iff (x j : Nat) : bitK x j = true ↔ x.testBit j = true := by
  unfold bitK
  rw [Nat.beq_eq, Nat.testBit, Nat.one_and_eq_mod_two]
  change (x >>> j) &&& 1 = 1 ↔ _
  rw [Nat.and_one_is_mod]
  constructor
  · intro h
    simp [h]
  · intro h
    have := Nat.mod_two_eq_zero_or_one (x >>> j)
    rcases this with h' | h'
    · simp [h'] at h
    · exact h'

theorem prim_sound {n NL k cnt0 : Nat} {letters : Array Table} {lv : Array Nat}
    {L : Nat → Nat → Nat} {B : Nat → Nat} {PTS0 POS0 PAR0 LAB0 LBL REP IM DS DOFF DLEN : Nat → Nat}
    {SPTS SPOS SPAR SLAB STI : Nat → Nat → Nat} {SCNT : Nat → Nat}
    (hL : letters.size = NL ∧ ∀ l < NL, ∀ x < n, ap letters[l]! x = L l x ∧ L l x < n)
    (hlv : lv = (lvK L B NL 1).toArray)
    (hn : 0 < n ∧ n < 2 ^ 16)
    (hlab0 : ∀ q < cnt0, 0 < q → r32 PAR0 q < q → r32 LAB0 q < NL)
    (hz : ∀ z < n, subPtK k LBL REP SPTS SPOS SCNT z = true)
    (hr : ∀ l < k, subRepK n k cnt0 LBL REP PTS0 POS0 l = true)
    (hs : ∀ l < k, tbfsHdK n (r32 REP l) (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l) = true ∧
      ∀ q < SCNT l, tbfsPtK n (SCNT l) (lvK L B NL 1).length L (lvAt L B NL 1) (SPTS l) (SPOS l)
        (SPAR l) (SLAB l) (STI l) q = true)
    (hq : ∀ l < k, ∀ q < SCNT l, subLblK LBL SPTS l q = true)
    (him : ∀ l < k, ∀ x < n, imAtK L PAR0 LAB0 POS0 REP IM n l x = true)
    (hd : ∀ i < k, i ≠ r32 LBL 0 → derK n k LBL IM DS DOFF DLEN i = true) :
    primOK n letters lv (tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0)
      (primData n letters lv (tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0)) = true := by
  have hZ : ∀ z < n, r32 LBL z < k ∧ r32 REP (r32 LBL z) ≤ z ∧
      r32 (SPOS (r32 LBL z)) z < SCNT (r32 LBL z) ∧
      r32 (SPTS (r32 LBL z)) (r32 (SPOS (r32 LBL z)) z) = z := by
    intro z hz'
    have h := hz z hz'
    unfold subPtK at h
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq,
      Nat.beq_eq] at h
    exact h
  have hR : ∀ l < k, r32 REP l < n ∧ r32 LBL (r32 REP l) = l ∧ r32 POS0 (r32 REP l) < cnt0 ∧
      r32 PTS0 (r32 POS0 (r32 REP l)) = r32 REP l ∧ (l + 1 < k → r32 REP l < r32 REP (l + 1)) := by
    intro l hl
    have h := hr l hl
    unfold subRepK at h
    rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h⟩ := h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h2, h⟩ := h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h3, h⟩ := h
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h4, h5⟩ := h
    rw [Raw.Orb.bIf_eq] at h5
    rw [Nat.blt_eq] at h1 h3
    rw [Nat.beq_eq] at h2 h4
    refine ⟨h1, h2, h3, h4, fun hl1 => ?_⟩
    have e : Nat.blt (Nat.succ l) k = true := by rw [Nat.blt_eq]; exact hl1
    rw [ite_eq_left e] at h5
    rwa [Nat.blt_eq] at h5
  have hmono : ∀ l l', l < l' → l' < k → r32 REP l < r32 REP l' := by
    intro l l' hll'
    induction l' with
    | zero => omega
    | succ l' ih =>
      intro hl'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hll' with h | rfl
      · exact Nat.lt_trans (ih h (by omega)) ((hR l' (by omega)).2.2.2.2 hl')
      · exact (hR l (by omega)).2.2.2.2 hl'
  have hinj : ∀ l < k, ∀ l' < k, r32 REP l = r32 REP l' → l = l' := by
    intro l hl l' hl' e
    rcases Nat.lt_trichotomy l l' with h | h | h
    · have := hmono l l' h hl'
      omega
    · exact h
    · have := hmono l' l h hl
      omega
  have hQ : ∀ l < k, ∀ q < SCNT l, r32 LBL (r32 (SPTS l) q) = l := fun l hl q hq' => by
    have := hq l hl q hq'
    unfold subLblK at this
    rwa [Nat.beq_eq] at this
  have hlv' : lv.size = (lvK L B NL 1).length ∧ ∀ t < (lvK L B NL 1).length,
      lv[t]! = lvAt L B NL 1 t ∧ lvAt L B NL 1 t < letters.size ∧
        ∀ x < n, ap letters[lvAt L B NL 1 t]! x = L (lvAt L B NL 1 t) x := by
    subst hlv
    refine ⟨by simp, fun t ht => ?_⟩
    have hm := (PC.mem_lvK.1 (PC.lvAt_mem ht)).1
    refine ⟨?_, by rw [hL.1]; exact hm, fun x hx => (hL.2 _ hm x hx).1⟩
    unfold lvAt
    rw [getElem!_pos _ t (by simpa using ht), List.getD_eq_getElem _ _ ht]
    simp
  have hT : ∀ l < k, treeBFS n (r32 REP l) letters lv =
      tbfsRec n (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l) ∧
      treeOK n (r32 REP l) (tbfsRec n (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l)) letters lv =
        true := fun l hl => tbfsK_sound hlv' (hs l hl).1 (hs l hl).2
  have hPt : ∀ l < k, ∀ q < SCNT l, r32 (SPTS l) q < n := fun l hl q hq' =>
    (pt_spec ((hs l hl).2 q hq')).lt
  have hkn : k ≤ n := by
    have : ∀ l < k, l ≤ r32 REP l := by
      intro l
      induction l with
      | zero => intro _; omega
      | succ l ih =>
        intro hl
        have := ih (by omega)
        have := (hR l (by omega)).2.2.2.2 hl
        omega
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · omega
    · have := this (k - 1) (by omega)
      have := (hR (k - 1) (by omega)).1
      omega
  let tr : Nat → Tree := fun l => tbfsRec n (SCNT l) (SPTS l) (SPOS l) (SPAR l) (SLAB l)
  have hsub : suborbits n letters lv = (Array.ofFn (n := n) fun z => r32 LBL z.val,
      Array.ofFn (n := k) fun l => r32 REP l.val, Array.ofFn (n := k) fun l => tr l.val) := by
    let SI : Nat → Array Nat × Array Nat × Array Tree → Prop := fun m s =>
      s.1.size = n ∧ (∀ z < n, s.1[z]! = if r32 REP (r32 LBL z) < m then r32 LBL z else n) ∧
        ∃ c ≤ k, VOR.ArrEq s.2.1 c (r32 REP) ∧ VOR.ArrEq s.2.2 c tr ∧
          ∀ l < k, (l < c ↔ r32 REP l < m)
    have step : ∀ m < n, ∀ s, SI m s → SI (m + 1) (subStep n letters lv s m) := by
      intro m hm s ⟨hs1, hs2, c, hck, hrep, htr, hc⟩
      obtain ⟨hl0, hle, -, -⟩ := hZ m hm
      have noeq : ∀ l < k, r32 REP l = m → l = r32 LBL m := fun l hl e => by
        have := (hR l hl).2.1
        rw [e] at this
        exact this.symm
      unfold subStep
      rcases Nat.lt_or_ge (r32 REP (r32 LBL m)) m with hlt | hge
      ·
        have hne : ¬ (s.1[m]! == n) = true := by
          rw [hs2 m hm, ite_eq_left hlt]
          simp
          omega
        rw [ite_eq_right hne]
        have hnm : ∀ l < k, r32 REP l ≠ m := fun l hl e => by
          have := noeq l hl e
          subst this
          omega
        refine ⟨hs1, fun z hz' => ?_, c, hck, hrep, htr, fun l hl => ?_⟩
        · rw [hs2 z hz']
          have := hnm _ (hZ z hz').1
          by_cases h : r32 REP (r32 LBL z) < m
          · rw [ite_eq_left h, ite_eq_left (by omega)]
          · rw [ite_eq_right h, ite_eq_right (by omega)]
        · rw [hc l hl]
          have := hnm l hl
          omega
      ·
        have heq : r32 REP (r32 LBL m) = m := by omega
        have hcl : c = r32 LBL m := by
          rcases Nat.lt_trichotomy c (r32 LBL m) with h | h | h
          · have := hmono c _ h hl0
            have := (hc c (by omega)).2 (by omega)
            omega
          · exact h
          · have := (hc _ hl0).1 h
            omega
        have hcond : (s.1[m]! == n) = true := by
          rw [hs2 m hm, ite_eq_right (by omega)]
          simp
        rw [ite_eq_left hcond]
        have hTm : treeBFS n m letters lv = tr c := by
          have := (hT _ hl0).1
          rw [heq] at this
          rw [hcl]
          exact this
        rw [hTm, hrep.1]
        obtain ⟨f1, f2⟩ := fold_set c (tr c).pts.toList s.1
        rw [Array.foldl_toList] at f1 f2
        refine ⟨by rw [f1, hs1], fun z hz' => ?_, c + 1, by omega, hrep.push (by rw [hcl, heq]),
          htr.push rfl, fun l hl => ?_⟩
        · rw [f2 z (by rw [hs1]; exact hz')]
          have hmem : (∃ x ∈ (tr c).pts.toList, x.toNat = z) ↔ r32 LBL z = c := by
            constructor
            · rintro ⟨x, hx, rfl⟩
              obtain ⟨q, hq', rfl⟩ := List.mem_iff_getElem.1 hx
              have hq2 : q < SCNT c := by simpa [tr, tbfsRec] using hq'
              simp only [tr, tbfsRec, Array.getElem_toList, Array.getElem_ofFn]
              rw [toNat_r32]
              exact hQ c (by omega) q hq2
            · intro e
              obtain ⟨-, -, a3, a4⟩ := hZ z hz'
              rw [e] at a3 a4
              refine ⟨UInt32.ofNat (r32 (SPTS c) (r32 (SPOS c) z)), ?_, by rw [toNat_r32, a4]⟩
              rw [List.mem_iff_getElem]
              exact ⟨r32 (SPOS c) z, by simpa [tr, tbfsRec] using a3, by simp [tr, tbfsRec]⟩
          by_cases e : r32 LBL z = c
          · rw [ite_eq_left (hmem.2 e), ite_eq_left (by rw [e, hcl, heq]; omega), e]
          · rw [ite_eq_right (fun h => e (hmem.1 h)), hs2 z hz']
            have hne : r32 REP (r32 LBL z) ≠ m := fun h => e (by rw [hcl]; exact noeq _ (hZ z hz').1 h)
            by_cases h : r32 REP (r32 LBL z) < m
            · rw [ite_eq_left h, ite_eq_left (by omega)]
            · rw [ite_eq_right h, ite_eq_right (by omega)]
        · have h1 := hc l hl
          have h2 : r32 REP l = m ↔ l = c := ⟨fun h => by rw [hcl]; exact noeq l hl h,
            fun h => by rw [h, hcl, heq]⟩
          omega
    have hfin : SI n ((List.range n).foldl (subStep n letters lv)
        (Array.replicate n n, #[], #[])) := by
      have : ∀ m ≤ n, SI m ((List.range m).foldl (subStep n letters lv)
          (Array.replicate n n, #[], #[])) := by
        intro m
        induction m with
        | zero =>
          intro _
          refine ⟨by simp, fun z hz' => ?_, 0, Nat.zero_le _, VOR.arrEq_nil _, VOR.arrEq_nil _,
            fun l hl => by omega⟩
          rw [ite_eq_right (by omega), getElem!_pos _ z (by simpa using hz')]
          simp
        | succ m ih =>
          intro hm
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact step m (by omega) _ (ih (by omega))
      exact this n (Nat.le_refl _)
    rw [suborbits_fold]
    obtain ⟨h1, h2, c, hck, hrep, htr, hc⟩ := hfin
    have hck' : c = k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · omega
      · have := (hc (k - 1) (by omega)).2 (hR (k - 1) (by omega)).1
        omega
    subst hck'
    refine Prod.ext ?_ (Prod.ext hrep.eq_ofFn htr.eq_ofFn)
    refine VOR.ArrEq.eq_ofFn ⟨h1, fun z hz' => ?_⟩
    rw [h2 z hz', ite_eq_left (by
      have := (hR _ (hZ z hz').1).1
      omega)]
  have hlabA : ∀ z < n, (Array.ofFn (n := n) fun z => r32 LBL z.val)[z]! = r32 LBL z :=
    fun z hz' => TBfs.ofFn_get hz'
  have hrepA : ∀ l < k, (Array.ofFn (n := k) fun l => r32 REP l.val)[l]! = r32 REP l :=
    fun l hl => TBfs.ofFn_get hl
  have hTr : ∀ l < k, (Array.ofFn (n := k) fun l => tr l.val)[l]! = tr l :=
    fun l hl => TBfs.ofFn_get (f := tr) hl
  let T0 := tbfsRec n cnt0 PTS0 POS0 PAR0 LAB0
  have hpos0 : ∀ l < k, ap T0.pos (r32 REP l) = r32 POS0 (r32 REP l) :=
    fun l hl => TBfs.ap_ofFn (hR l hl).1
  have himg : ∀ j < k, ∀ w < n,
      (treeImg n T0 letters (r32 REP j))[w]! = r32 IM (j * n + w) ∧ r32 IM (j * n + w) < n := by
    intro j hj w hw
    unfold treeImg
    rw [hpos0 j hj]
    have hrange : ∀ x ∈ Array.range n, x < n := fun x hx => by simpa using hx
    obtain ⟨e1, e2⟩ := walk_val hL.2 hlab0 _ (hR j hj).2.2.1 _ hrange
    have hi := him j hj w hw
    unfold imAtK at hi
    rw [Nat.beq_eq] at hi
    rw [e1, getElem!_pos _ w (by simpa using hw), Array.getElem_map, Array.getElem_range]
    rw [List.getD_eq_getElem?_getD] at hi
    have hw' : (walkK L PAR0 LAB0 (r32 POS0 (r32 REP j)) [w]).getD 0 0 = r32 IM (j * n + w) := by
      rw [List.getD_eq_getElem?_getD]
      exact hi
    exact ⟨hw', hw' ▸ e2 w (by simpa using hw)⟩
  unfold primData
  rw [hsub]
  simp only
  unfold primOK
  simp only [Array.size_ofFn, Array.size_map, Array.size_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  have hl0 : r32 LBL 0 < k := (hZ 0 hn.1).1
  refine ⟨⟨by simpa using hn.1, TBfs.allIn_iff.2 fun l hl => ?_⟩,
    TBfs.allIn_iff.2 fun z hz' => ?_⟩
  · obtain ⟨a1, a2, a3, a4, -⟩ := hR l hl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
    rw [hrepA l hl, hlabA _ a1, hTr l hl, hlabA 0 hn.1]
    refine ⟨⟨⟨⟨⟨a1, a2⟩, ?_⟩, (hT l hl).2⟩, ?_⟩, ?_⟩
    · unfold inTree
      rw [hpos0 l hl]
      simp only [tbfsRec, Array.size_ofFn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rw [TBfs.ap_ofFn a3]
      exact ⟨a3, a4⟩
    · rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, ← getElem!_pos _ l
        (by simpa using hl), hrepA l hl]
    · by_cases hl' : l = r32 LBL 0
      · exact Or.inl hl'
      · right
        rw [getElem!_pos _ l (by simpa using hl), Array.getElem_map, Array.getElem_range]
        simp only [hl', ↓reduceIte]
        have himgs : ∀ j < k, ∀ w < n, (((Array.ofFn (n := k) fun l => r32 REP l.val).map
            fun r => treeImg n T0 letters r)[j]!)[w]! = r32 IM (j * n + w) := by
          intro j hj w hw
          rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map, ← getElem!_pos _ j
            (by simpa using hj), hrepA j hj]
          exact (himg j hj w hw).1
        refine CFSG.KS.DS.derSearch_ok (fun w hw => by rw [hlabA w hw]; exact (hZ w hw).1)
          (fun j hj w hw => by rw [himgs j hj w hw]; exact (himg j hj w hw).2)
          hl0 hl (fun S hS0 hSi hcl => ?_)
        try rw [hlabA 0 hn.1] at hS0
        have hder := hd l hl hl'
        unfold derK at hder
        rw [Raw.Orb.strictB_eq, Nat.beq_eq] at hder
        have inv : ∀ t, ∀ b, (Nat.rec (motive := fun _ => Nat)
            (Nat.lor (Nat.shiftLeft 1 (r32 LBL 0)) (Nat.shiftLeft 1 l))
            (fun t D => strictN D fun D' => derStepK n k LBL IM D' (r32 DS (Nat.add (r32 DOFF l) t)))
            t).testBit b = true → b < k ∧ S b := by
          intro t
          induction t with
          | zero =>
            intro b hb
            change ((1 <<< r32 LBL 0) ||| (1 <<< l)).testBit b = true at hb
            rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.one_shiftLeft,
              Nat.testBit_two_pow, Nat.testBit_two_pow] at hb
            rcases hb with hb | hb
            · have := of_decide_eq_true hb
              subst this
              exact ⟨hl0, hS0⟩
            · have := of_decide_eq_true hb
              subst this
              exact ⟨hl, hSi⟩
          | succ t ih =>
            intro b hb
            change (strictN _ fun D' => derStepK n k LBL IM D' (r32 DS (Nat.add (r32 DOFF l) t))).testBit b
              = true at hb
            rw [Raw.Orb.strictN_eq] at hb
            generalize Nat.rec (motive := fun _ => Nat) _ _ t = D at ih hb
            unfold derStepK at hb
            rw [Raw.Orb.strictN_eq, Raw.Orb.strictN_eq, Raw.Orb.nIf_eq, Raw.Orb.bAnd_eq,
              Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq] at hb
            generalize (r32 DS (Nat.add (r32 DOFF l) t)).shiftRight 16 = j at hb
            generalize (r32 DS (Nat.add (r32 DOFF l) t)).land 65535 = w at hb
            split at hb
            · next hc =>
              simp only [Bool.and_eq_true, Nat.blt_eq, bitK_iff] at hc
              obtain ⟨hj, hw, hbj, hbw⟩ := hc
              change (D ||| (1 <<< r32 LBL (r32 IM (j * n + w)))).testBit b = true at hb
              rw [Nat.testBit_or, Bool.or_eq_true, Nat.one_shiftLeft, Nat.testBit_two_pow] at hb
              rcases hb with hb | hb
              · exact ih b hb
              · have := of_decide_eq_true hb
                subst this
                have hIM := himg j hj w hw
                refine ⟨(hZ _ hIM.2).1, ?_⟩
                have := hcl j hj w hw (ih j hbj).2 (by rw [hlabA w hw]; exact (ih _ hbw).2)
                rwa [himgs j hj w hw, hlabA _ hIM.2] at this
            · exact ih b hb
        intro l' hl'k
        have h2 := inv (r32 DLEN l) l' (by
          rw [hder]
          have e2 : (Nat.shiftLeft 1 k).sub 1 = 2 ^ k - 1 := by
            change 1 <<< k - 1 = _
            rw [Nat.one_shiftLeft]
          rw [e2, Nat.testBit_two_pow_sub_one]
          exact decide_eq_true hl'k)
        exact h2.2
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨a1, -, a3, a4⟩ := hZ z hz'
    rw [hlabA z hz', hTr _ a1]
    refine ⟨a1, ?_⟩
    unfold inTree
    simp only [tr, tbfsRec, Array.size_ofFn, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [TBfs.ap_ofFn hz', TBfs.ap_ofFn a3]
    exact ⟨a3, a4⟩

example : subLblK (fun _ => 1) (fun _ _ => 0) 0 0 = false := by
  decide +kernel

end CFSG.KS.PR

end
