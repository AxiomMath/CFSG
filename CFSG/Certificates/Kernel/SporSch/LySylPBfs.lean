module

public import CFSG.Certificates.Kernel.SporSch.LySylDefs
import CFSG.Certificates.Kernel.SporSch.LyRunB
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.LyCheckSylow

public section

namespace CFSG.KS.SporSch.LySylP.Bfs

open CFSG.KC.Enum CFSG.KC.Ord CFSG.KS CFSG.KS.SporSch.LyM CFSG.Sporadic.LySchreier.Native
open CFSG.KS.SporSch.LySyl CFSG.KS.SporSch.LyLoop CFSG.KS.SporSch.LyRB
open CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

private theorem plOK_spec {W PL : Nat → Nat} {n j : Nat} (h : plOK W PL n j = true) :
    (0 < j → LySyl.parK PL j < j ∧ LySyl.labK PL j < 6 ∧ lamK W (LySyl.labK PL j) (LySyl.parK PL j) = j ∧
      (j + 1 < n → 6 * LySyl.parK PL j + LySyl.labK PL j < 6 * LySyl.parK PL (j + 1) + LySyl.labK PL (j + 1))) ∧
    ∀ k < 6, lamK W k j < n ∧
      (lamK W k j = 0 ∨ 6 * LySyl.parK PL (lamK W k j) + LySyl.labK PL (lamK W k j) ≤ 6 * j + k) := by
  unfold plOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hj => ?_, fun k hk => ?_⟩
  · have hb : Nat.beq j 0 = false := by
      cases j with
      | zero => exact absurd hj (Nat.lt_irrefl 0)
      | succ _ => rfl
    rw [hb] at h1
    obtain ⟨a1, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨a2, h1⟩ := (bAnd_iff _ _).1 h1
    obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 h1
    refine ⟨Eq.mp Nat.blt_eq a1, Eq.mp Nat.blt_eq a2, Nat.eq_of_beq_eq_true a3, fun hn => ?_⟩
    have hb2 : Nat.blt (Nat.succ j) n = true := Eq.mpr Nat.blt_eq hn
    rw [hb2] at a4
    exact Eq.mp Nat.blt_eq a4
  · have h3 := allN_spec h2 k hk
    simp only [strictB_eqB] at h3
    obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 h3
    refine ⟨Eq.mp Nat.blt_eq b1, ?_⟩
    by_cases h0 : lamK W k j = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      have hb : Nat.beq (lamK W k j) 0 = false := Bool.eq_false_iff.2 fun e => h0 (Nat.eq_of_beq_eq_true e)
      rw [hb] at b2
      exact Eq.mp Nat.ble_eq b2

private theorem ofFn_set {α : Type} (F : Nat → α) {n k : Nat} (hk : k < n) (v : α) :
    (Array.ofFn (n := n) fun i => F i.val).set! k v =
      Array.ofFn (n := n) fun i => if i.val = k then v else F i.val := by
  rw [Array.set!_eq_setIfInBounds]
  apply Array.ext
  · simp
  · intro i h1 h2
    rw [Array.getElem_setIfInBounds, Array.getElem_ofFn, Array.getElem_ofFn]
    · by_cases e : k = i
      · simp [e]
      · simp [e, Ne.symm e]
    · simpa using h2

private theorem allIn_iff' {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ k, lo ≤ k → k < hi → p k = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h k hk1 hk2
    have := h ⟨k - lo, by omega⟩ (List.mem_finRange _)
    simp only at this
    rwa [Nat.add_sub_cancel' hk1] at this
  · intro h i _
    exact h _ (Nat.le_add_right _ _) (by have := i.isLt; omega)

private theorem index_fold {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α]
    (pts : Array α) : ∀ n, (∀ a < n, ∀ b < n, pts[a]! = pts[b]! → a = b) →
      ∀ k < n, ((List.range n).foldl (fun m k => m.insert pts[k]! k)
        (∅ : Std.HashMap α Nat))[pts[k]!]? = some k
  | 0, _ => fun k hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, hinj => by
    intro k hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    by_cases hkn : k = n
    · subst hkn
      rw [if_pos (beq_self_eq_true _)]
    · have hne : (pts[n]! == pts[k]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hkn (hinj k hk n (by omega) e.symm)
      rw [hne]
      exact index_fold pts n (fun a ha b hb e => hinj a (by omega) b (by omega) e) k (by omega)

private theorem index_getD {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [Inhabited α]
    (pts : Array α) {n : Nat} (hinj : ∀ a < n, ∀ b < n, pts[a]! = pts[b]! → a = b) {k : Nat}
    (hk : k < n) :
    ((List.range n).foldl (fun m k => m.insert pts[k]! k)
      (∅ : Std.HashMap α Nat)).getD pts[k]! n = k := by
  rw [Std.HashMap.getD_eq_getD_getElem?, index_fold pts n hinj k hk]
  rfl

private noncomputable def lamRow (W : Nat → Nat) (k m : Nat) : Array Nat :=
  Array.ofFn (n := m) fun i => lamK W k i.val

private noncomputable def lamRows (W : Nat → Nat) (h k : Nat) : Array (Array Nat) :=
  Array.ofFn (n := 6) fun k' => lamRow W k'.val (if k'.val < k then h + 1 else h)

private theorem lamRows_step (W : Nat → Nat) {h k : Nat} (hk : k < 6) :
    (lamRows W h k).set! k ((lamRows W h k)[k]!.push (lamK W k h)) = lamRows W h (k + 1) := by
  unfold lamRows
  rw [ofFn_getP (fun k' => lamRow W k' (if k' < k then h + 1 else h)) hk, if_neg (Nat.lt_irrefl k)]
  have e : (lamRow W k h).push (lamK W k h) = lamRow W k (h + 1) :=
    ofFn_push (fun i => lamK W k i) h
  rw [e, ofFn_set (fun k' => lamRow W k' (if k' < k then h + 1 else h)) hk]
  congr 1
  funext i
  by_cases hi : i.val = k
  · rw [if_pos hi, hi, if_pos (Nat.lt_succ_self k)]
  · rw [if_neg hi]
    by_cases hlt : i.val < k
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

private theorem lamRows_next (W : Nat → Nat) (h : Nat) : lamRows W h 6 = lamRows W (h + 1) 0 := by
  unfold lamRows
  congr 1
  funext i
  rw [if_pos i.isLt, if_neg (Nat.not_lt_zero _)]

private theorem lamRows_end (W : Nat → Nat) (c : Nat) :
    lamRows W c 0 = Array.ofFn (n := 6) fun k => Array.ofFn (n := c) fun h => lamK W k.val h.val := by
  unfold lamRows
  congr 1

theorem bfs_sound {w S T L H CM RM ONE LV HV kg c cap nS Hh : Nat} {UG E W PL SO SOI C : Nat → Nat}
    (hc : constsOK 5 w S 111 T L H CM RM ONE LV HV = true)
    (hU : ∀ k < kg, validM 5 (111 * S) L H (UG k) = true)
    (hE : ∀ i < c, validM 5 (111 * S) L H (E i) = true) (h0 : E 0 = ONE) (hc512 : c ≤ 512)
    (hsort : ∀ i < c, sortB E SO SOI c i = true)
    (hcap : nS * Hh = cap) (hcc : c = cap) (hkg : kg = 6) (hC0 : C 0 = 1) (hCn : C nS = c)
    (hrun : ∀ q < nS, Nat.beq (runB 5 w S 111 T L H CM RM UG E W kg c Hh (Nat.mul q Hh) (C q))
      (C (Nat.succ q)) = true)
    (hpl : ∀ j < c, plOK W PL c j = true) (hPL0 : PL 0 = 0) {us : Array (Array (Array Nat))}
    (hus : us.size = kg ∧ ∀ k < kg, us[k]! = unpackL 111 w S (UG k)) :
    sylowBFS us cap = recOf w S E PL W c kg ∧ sylowEnumOK us cap (recOf w S E PL W c kg) = true := by
  subst hcc
  subst kg
  let sH := fun h s => stH 5 w S 111 T L H CM RM UG E W 6 c h s
  let stG := fun t => (List.range t).foldl (fun s h => sH h s) 1
  have hCq : ∀ q ≤ nS, C q = stG (q * Hh) := by
    intro q
    induction q with
    | zero => intro _; rw [hC0, Nat.zero_mul]; rfl
    | succ q ih =>
      intro hq
      have hr := Nat.eq_of_beq_eq_true (hrun q (by omega))
      rw [runB_eq, ih (by omega)] at hr
      rw [← hr]
      have e := range_split (fun h s => sH h s) 1 (a := q * Hh) (b := (q + 1) * Hh)
        (Nat.mul_le_mul_right Hh (Nat.le_succ q))
      have e2 : (q + 1) * Hh - q * Hh = Hh := by rw [Nat.succ_mul]; omega
      rw [e2] at e
      exact e.symm
  have hG : stG c = c := by
    have := hCq nS le_rfl
    rw [hcap, hCn] at this
    exact this.symm
  have hF : c < failC := by rw [failC_val]; omega
  have habs := fun l s hs => fold_absorb (fun h s => sH h s) failC
    (fun h => (stH_absorb hc512 h).1) (fun h => (stH_absorb hc512 h).2) l s hs
  have h1F : (1 : Nat) ≤ failC := by rw [failC_val]; omega
  have hGt : ∀ t ≤ c, stG t ≤ c ∧ stG t ≠ failC := by
    intro t ht
    have e := range_split (fun h s => sH h s) 1 ht
    have hb := habs (List.range t) 1 h1F
    have ha := habs (List.range' t (c - t)) (stG t) hb.2.1
    change stG c = _ at e
    rw [← e, hG] at ha
    exact ⟨ha.1, fun h => absurd (ha.2.2 h) (Nat.ne_of_lt hF)⟩
  have hGs : ∀ t, stG (t + 1) = sH t (stG t) := by
    intro t
    change (List.range (t + 1)).foldl _ 1 = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  let stI := fun h k => (List.range k).foldl
    (fun s k => stepB 5 w S 111 T L H CM RM UG E W c h k s) (stG h)
  have hI : ∀ h < c, ∀ k ≤ 6, stI h k ≤ c ∧ stI h k ≠ failC ∧ stG h ≤ stI h k := by
    intro h hh k hk
    have hgh := hGt h (by omega)
    have hgh1 := hGt (h + 1) (by omega)
    have habsI := fun l s hs => fold_absorb (fun k s => stepB 5 w S 111 T L H CM RM UG E W c h k s)
      failC (fun k => (stepB_absorb hc512 h k).1) (fun k => (stepB_absorb hc512 h k).2) l s hs
    have e := range_split (fun k s => stepB 5 w S 111 T L H CM RM UG E W c h k s) (stG h) hk
    have hb := habsI (List.range k) (stG h) (Nat.le_trans hgh.1 (Nat.le_of_lt hF))
    have ha := habsI (List.range' k (6 - k)) (stI h k) hb.2.1
    have e1 : stG (h + 1) = (List.range' k (6 - k)).foldl
        (fun s x => stepB 5 w S 111 T L H CM RM UG E W c h x s) (stI h k) := by
      rw [hGs]
      exact e
    rw [← e1] at ha
    exact ⟨Nat.le_trans ha.1 hgh1.1, fun hh' => hgh1.2 (ha.2.2 hh'), hb.1⟩
  have hIs : ∀ h k, stI h (k + 1) = stepB 5 w S 111 T L H CM RM UG E W c h k (stI h k) := by
    intro h k
    change (List.range (k + 1)).foldl _ _ = _
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hIk : ∀ h, stI h 6 = stG (h + 1) := fun h => (hGs h).symm
  let P := fun i => unpackL 111 w S (E i)
  have hinj := sortB_inj hsort
  have hP : ∀ i < c, ∀ j < c, P i = P j → i = j := fun i hi j hj e =>
    hinj i hi j hj (unpack_inj hc (hE i hi) (hE j hj) e)
  have hidE : idM 111 = P 0 := by
    change idM 111 = unpackL 111 w S (E 0)
    rw [h0]
    exact (idM_eqL hc).1
  have hproc : ∀ t < c, t < stG t := by
    intro t ht
    by_contra hle
    have hstay : ∀ u, stG (t + u) = stG t := by
      intro u
      induction u with
      | zero => rfl
      | succ u ih =>
        rw [← Nat.add_assoc, hGs, ih]
        exact stH_skip (by omega)
    have := hstay (c - t)
    rw [Nat.add_sub_cancel' (by omega), hG] at this
    omega
  have hstep : ∀ h < c, ∀ k < 6,
      (stI h (k + 1) = stI h k ∧ lamK W k h < stI h k ∧
        mulR 5 w S 111 T L H CM RM (UG k) (E h) = E (lamK W k h)) ∨
      (stI h (k + 1) = stI h k + 1 ∧ lamK W k h = stI h k ∧ stI h k < c ∧
        mulR 5 w S 111 T L H CM RM (UG k) (E h) = E (stI h k)) := by
    intro h hh k hk
    have hcur : h < stI h k := Nat.lt_of_lt_of_le (hproc h hh) (hI h hh k (by omega)).2.2
    have hnf := (hI h hh (k + 1) (by omega)).2.1
    have e := hIs h k
    have hl : fld(W h, Nat.mul (nat_lit 9) k, nat_lit 511) = lamK W k h := rfl
    rw [stepB_eq, if_pos hcur, hl] at e
    split_ifs at e with hA hB
    · exact Or.inl ⟨e, hA.1, hA.2⟩
    · exact Or.inr ⟨e, hB.1, hB.2.1, hB.2.2⟩
    · exact absurd e hnf
  let C' := fun e => stI (e / 6) (e % 6)
  have hC'e : ∀ h k, k < 6 → C' (6 * h + k) = stI h k := by
    intro h k hk
    have e1 : (6 * h + k) / 6 = h := by omega
    have e2 : (6 * h + k) % 6 = k := by omega
    change stI ((6 * h + k) / 6) ((6 * h + k) % 6) = _
    rw [e1, e2]
  have hC's : ∀ e, C' (e + 1) = stI (e / 6) (e % 6 + 1) := by
    intro e
    change stI ((e + 1) / 6) ((e + 1) % 6) = _
    by_cases h5 : e % 6 = 5
    · have e1 : (e + 1) / 6 = e / 6 + 1 := by omega
      have e2 : (e + 1) % 6 = 0 := by omega
      rw [e1, e2, h5]
      exact (hIk (e / 6)).symm
    · have e1 : (e + 1) / 6 = e / 6 := by omega
      have e2 : (e + 1) % 6 = e % 6 + 1 := by omega
      rw [e1, e2]
  have hC'1 : ∀ e < 6 * c, C' e ≤ C' (e + 1) := by
    intro e he
    rw [hC's]
    change stI (e / 6) (e % 6) ≤ _
    rcases hstep (e / 6) (by omega) (e % 6) (by omega) with h | h <;> omega
  have hC'mono : ∀ a b, a ≤ b → b ≤ 6 * c → C' a ≤ C' b := by
    intro a b hab hb
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hab ih => exact le_trans (ih (by omega)) (hC'1 b (by omega))
  have hdisc : ∀ h < c, ∀ k < 6, lamK W k h = stI h k → stI h (k + 1) = stI h k + 1 →
      LySyl.parK PL (stI h k) = h ∧ LySyl.labK PL (stI h k) = k := by
    intro h hh k hk hj hnew
    have hhj : h < stI h k := Nat.lt_of_lt_of_le (hproc h hh) (hI h hh k (by omega)).2.2
    have hjc : stI h k < c := by have := (hI h hh (k + 1) (by omega)).1; omega
    have hCj : C' (6 * h + k) = stI h k := hC'e h k hk
    generalize stI h k = j at hj hnew hhj hjc hCj
    have hpos := ((plOK_spec (hpl h hh)).2 k hk).2
    rw [hj] at hpos
    obtain ⟨hp, hl, hlam, -⟩ := (plOK_spec (hpl j hjc)).1 (by omega)
    rcases hpos with hpos | hpos
    · omega
    rcases hstep (LySyl.parK PL j) (by omega) (LySyl.labK PL j) hl with ⟨-, h2, -⟩ | ⟨h1, h2, -⟩
    · rw [hlam] at h2
      have := hC'mono _ _ hpos (by omega)
      rw [hC'e _ _ hl, hCj] at this
      omega
    · rw [hlam] at h2
      by_contra hne
      have hlt : 6 * LySyl.parK PL j + LySyl.labK PL j + 1 ≤ 6 * h + k := by omega
      have := hC'mono _ _ hlt (by omega)
      rw [hC's, hCj] at this
      have e1 : (6 * LySyl.parK PL j + LySyl.labK PL j) / 6 = LySyl.parK PL j := by omega
      have e2 : (6 * LySyl.parK PL j + LySyl.labK PL j) % 6 = LySyl.labK PL j := by omega
      rw [e1, e2, h1, ← h2] at this
      omega
  let R := fun (h k cur : Nat)
      (s : Std.HashMap Mat Nat × Array Mat × Array Nat × Array Nat × Array (Array Nat)) =>
    s.2.1 = (Array.ofFn (n := cur) fun i => P i.val) ∧ (∀ i < cur, s.1[P i]? = some i) ∧
    (∀ z, (s.1[z]?).isSome = true → ∃ i < cur, P i = z) ∧
    s.2.2.1 = (Array.ofFn (n := cur) fun i => LySyl.parK PL i.val) ∧
    s.2.2.2.1 = (Array.ofFn (n := cur) fun i => LySyl.labK PL i.val) ∧
    s.2.2.2.2 = lamRows W h k
  have hex : ∃ s, sylowBFS us c = (s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2) ∧ R c 0 (stG c) s := by
    unfold sylowBFS
    refine ⟨_, rfl, forIn_range_spec (fun h s => R h 0 (stG h) s) c _ _ ?_ ?_⟩
    ·
      have hp0 : LySyl.parK PL 0 = 0 := by unfold LySyl.parK; rw [hPL0]; rfl
      have hl0 : LySyl.labK PL 0 = 0 := by unfold LySyl.labK; rw [hPL0]; rfl
      refine ⟨?_, fun i hi => ?_, fun z hz => ?_, ?_, ?_, ?_⟩
      · change #[idM 111] = Array.ofFn (n := 1) fun i => P i.val
        rw [hidE]
        rfl
      · have : i = 0 := by change i < 1 at hi; omega
        subst this
        change ((∅ : Std.HashMap Mat Nat).insert (idM 111) 0)[P 0]? = some 0
        rw [← hidE, Std.HashMap.getElem?_insert_self]
      · change (((∅ : Std.HashMap Mat Nat).insert (idM 111) 0)[z]?).isSome = true at hz
        rw [Std.HashMap.getElem?_insert] at hz
        by_cases e : (idM 111 == z) = true
        · exact ⟨0, Nat.zero_lt_one, by rw [← hidE]; exact eq_of_beq e⟩
        · rw [if_neg e, Std.HashMap.getElem?_empty] at hz
          exact absurd hz (by decide)
      · change #[0] = Array.ofFn (n := 1) fun i => LySyl.parK PL i.val
        apply Array.ext
        · simp
        · intro i h1 _
          have : i = 0 := by simpa using h1
          subst this
          simp [hp0]
      · change #[0] = Array.ofFn (n := 1) fun i => LySyl.labK PL i.val
        apply Array.ext
        · simp
        · intro i h1 _
          have : i = 0 := by simpa using h1
          subst this
          simp [hl0]
      · change Array.replicate us.size #[] = lamRows W 0 0
        rw [hus.1]
        unfold lamRows lamRow
        apply Array.ext
        · simp
        · intro i h1 h2
          rw [Array.getElem_replicate, Array.getElem_ofFn]
          simp
    ·
      intro h b hh hb
      obtain ⟨hpts, hidx, hsome, hpar, hlab, hlam⟩ := hb
      have hlt' : h < stG h := hproc h hh
      dsimp only
      rw [if_pos (by rw [hpts]; simpa using hlt')]
      refine ⟨_, rfl, ?_⟩
      have hx : b.2.1[h]! = P h := by rw [hpts]; exact ofFn_getP P hlt'
      have hfin : ∀ s, R h us.size (stI h us.size) s →
          R (h + 1) 0 (stG (h + 1)) (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2) := by
        intro s hs
        rw [hus.1, hIk h] at hs
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hs
        exact ⟨a1, a2, a3, a4, a5, by rw [a6, lamRows_next]⟩
      refine hfin _ (forIn_range_spec (fun k s => R h k (stI h k) s) us.size _ _
        ⟨hpts, hidx, hsome, hpar, hlab, hlam⟩ ?_)
      intro k s hk hs
      rw [hus.1] at hk
      obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hs
      have hvh : validM 5 (111 * S) L H (E h) = true := hE h hh
      have hy : mulM 5 111 us[k]! b.2.1[h]! =
          unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) := by
        rw [hx, hus.2 k (by omega)]
        exact mulR_unpack hc (hU k (by omega)) hvh
      rw [hy]
      have hcur : h < stI h k := Nat.lt_of_lt_of_le hlt' (hI h hh k (by omega)).2.2
      have hcurc : stI h k ≤ c := (hI h hh k (by omega)).1
      have hlamk : s.2.2.2.2[k]! = lamRow W k h := by
        rw [hs6]
        unfold lamRows
        rw [ofFn_getP (fun k' => lamRow W k' (if k' < k then h + 1 else h)) hk,
          if_neg (Nat.lt_irrefl k)]
      split
      ·
        rename_i j hj
        refine ⟨_, rfl, ?_⟩
        obtain ⟨i, hi, hiz⟩ := hs3 _ (by rw [hj]; rfl)
        have hji : j = i := by
          have := hs2 i hi
          rw [hiz, hj] at this
          exact Option.some.inj this
        subst hji
        rcases hstep h hh k hk with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩
        · have hjl : j = lamK W k h := by
            refine hP j (by omega) _ (by omega) ?_
            rw [hiz, e3]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try rw [e1])
          · exact hs1
          · exact hs2
          · exact hs3
          · exact hs4
          · exact hs5
          · change s.2.2.2.2.set! k (s.2.2.2.2[k]!.push j) = _
            rw [hjl, hs6]
            exact lamRows_step W hk
        · exfalso
          have := hP j (by omega) (stI h k) e3 (by rw [hiz, e4])
          omega
      ·
        rename_i hj
        refine ⟨_, rfl, ?_⟩
        have hnot : ∀ i < stI h k,
            P i ≠ unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) := by
          intro i hi e
          have := hs2 i hi
          rw [e, hj] at this
          exact absurd this (by simp)
        rcases hstep h hh k hk with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩
        · exact absurd (by rw [e3]) (hnot _ e2)
        · obtain ⟨hpj, hlj⟩ := hdisc h hh k hk e2 e1
          have hsz : s.2.1.size = stI h k := by rw [hs1]; simp
          have hyP : unpackL 111 w S (mulR 5 w S 111 T L H CM RM (UG k) (E h)) = P (stI h k) := by
            rw [e4]
          rw [hsz, hyP, e1]
          refine ⟨?_, fun i hi => ?_, fun z hz => ?_, ?_, ?_, ?_⟩
          · change s.2.1.push _ = _
            rw [hs1]
            exact ofFn_push P _
          · change ((s.1.insert (P (stI h k)) (stI h k))[P i]?) = some i
            rw [Std.HashMap.getElem?_insert]
            by_cases e : (P (stI h k) == P i) = true
            · rw [if_pos e]
              have := hP _ (by omega) _ (by omega) (eq_of_beq e)
              rw [this]
            · rw [if_neg e]
              have hik : i ≠ stI h k := fun h' => e (by rw [h']; exact beq_self_eq_true _)
              exact hs2 i (by omega)
          · change ((s.1.insert (P (stI h k)) (stI h k))[z]?).isSome = true at hz
            rw [Std.HashMap.getElem?_insert] at hz
            by_cases e : (P (stI h k) == z) = true
            · exact ⟨stI h k, Nat.lt_succ_self _, eq_of_beq e⟩
            · rw [if_neg e] at hz
              obtain ⟨i, hi, hiz⟩ := hs3 z hz
              exact ⟨i, by omega, hiz⟩
          · change s.2.2.1.push h = _
            rw [hs4]
            have := ofFn_push (fun i => LySyl.parK PL i) (stI h k)
            rw [hpj] at this
            exact this
          · change s.2.2.2.1.push k = _
            rw [hs5]
            have := ofFn_push (fun i => LySyl.labK PL i) (stI h k)
            rw [hlj] at this
            exact this
          · change s.2.2.2.2.set! k (s.2.2.2.2[k]!.push (stI h k)) = _
            rw [← e2, hs6]
            exact lamRows_step W hk
  obtain ⟨s, hs, hs1, -, -, hs4, hs5, hs6⟩ := hex
  rw [hG] at hs1 hs4 hs5
  have hrec : sylowBFS us c = recOf w S E PL W c 6 := by
    rw [hs, hs1, hs4, hs5, hs6, lamRows_end]
    rfl
  refine ⟨hrec, ?_⟩
  have hmul : ∀ i < c, ∀ k < 6,
      mulR 5 w S 111 T L H CM RM (UG k) (E i) = E (lamK W k i) := by
    intro i hi k hk
    rcases hstep i hi k hk with ⟨-, -, e⟩ | ⟨-, e1, -, e⟩
    · exact e
    · rw [e1]; exact e
  unfold sylowEnumOK recOf
  dsimp only
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  have gP : ∀ i < c, (Array.ofFn (n := c) fun i => unpackL 111 w S (E i.val))[i]! = P i :=
    fun i hi => ofFn_getP P hi
  have gPar : ∀ i < c, (Array.ofFn (n := c) fun i => LySyl.parK PL i.val)[i]! = LySyl.parK PL i :=
    fun i hi => ofFn_getP (fun i => LySyl.parK PL i) hi
  have gLab : ∀ i < c, (Array.ofFn (n := c) fun i => LySyl.labK PL i.val)[i]! = LySyl.labK PL i :=
    fun i hi => ofFn_getP (fun i => LySyl.labK PL i) hi
  have gLam : ∀ k < 6, ∀ i < c,
      ((Array.ofFn (n := 6) fun k => Array.ofFn (n := c) fun h => lamK W k.val h.val)[k]!)[i]! =
        lamK W k i := by
    intro k hk i hi
    rw [ofFn_getP (fun k => Array.ofFn (n := c) fun h => lamK W k h.val) hk,
      ofFn_getP (fun h => lamK W k h) hi]
  have hpl1 := fun j hj => (plOK_spec (hpl j hj)).1
  have hpl2 := fun j hj => (plOK_spec (hpl j hj)).2
  refine ⟨hus.1, by simp, by simp, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro k hk
    rw [Array.size_ofFn] at hk
    rw [Array.getElem_ofFn]
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨by simp, ?_⟩
    rw [Array.all_eq_true]
    intro i hi
    rw [Array.getElem_ofFn]
    simp only [Array.size_ofFn] at hi
    exact decide_eq_true (hpl2 i hi k hk).1
  · have hc0 : 0 < c := by
      have := (hGt 0 (Nat.zero_le _)).1
      change 1 ≤ c at this
      omega
    rw [gP 0 hc0, hidE]
  · rw [allIn_iff']
    intro k _ hk
    rw [beq_iff_eq, Array.size_ofFn]
    refine index_getD _ (fun a ha b hb e => ?_) hk
    rw [gP a ha, gP b hb] at e
    exact hP a ha b hb e
  · rw [allIn_iff']
    intro i _ hi
    rw [allIn_iff']
    intro k _ hk
    have hl := (hpl2 i hi k hk).1
    rw [beq_iff_eq, gLam k hk i hi, gP i hi, gP _ hl, hus.2 k hk]
    change mulM 5 111 (unpackL 111 w S (UG k)) (unpackL 111 w S (E i)) = unpackL 111 w S (E _)
    rw [mulR_unpack hc (hU k hk) (hE i hi), hmul i hi k hk]
  · rw [allIn_iff']
    intro j hj1 hj
    obtain ⟨t1, t2, t3, -⟩ := hpl1 j hj (by omega)
    rw [gPar j hj, gLab j hj, gLam _ t2 _ (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨⟨t1, t2⟩, t3⟩
  · rw [allIn_iff']
    intro j hj1 hj
    obtain ⟨-, -, -, t4⟩ := hpl1 j (by omega) (by omega)
    unfold sylowPos
    rw [gPar j (by omega), gLab j (by omega), gPar (j + 1) (by omega), gLab (j + 1) (by omega),
      decide_eq_true_eq]
    exact t4 (by omega)
  · rw [allIn_iff']
    intro i _ hi
    rw [allIn_iff']
    intro k _ hk
    obtain ⟨t1, t2⟩ := hpl2 i hi k hk
    rw [gLam k hk i hi, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    unfold sylowPos
    rw [gPar _ t1, gLab _ t1]
    exact t2

end CFSG.KS.SporSch.LySylP.Bfs

end
