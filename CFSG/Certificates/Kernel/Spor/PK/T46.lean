module

public import CFSG.Certificates.Kernel.Spor.PK.T46Pk
public import CFSG.Certificates.Kernel.Spor.PK.OrbitSet
public import CFSG.Certificates.Kernel.Spor.PK.NatLetters
public import CFSG.Certificates.Kernel.Misc.T46Defs
public import CFSG.Certificates.Kernel.Misc.O73Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KC.Misc.T46 CFSG.F4.Native
  CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi22.Native CFSG.KS.TW

set_option exponentiation.threshold 7000

private theorem t46_inc_lt {UL : List Nat} (hinc : ∀ i < 692, UL.getD i 0 < UL.getD (i + 1) 0) :
    ∀ j i, i < j → j < 693 → UL.getD i 0 < UL.getD j 0 := by
  intro j
  induction j with
  | zero => intro i hi; omega
  | succ j ih =>
    intro i hij hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact Nat.lt_trans (ih i h (by omega)) (hinc j (by omega))
    · subst h; exact hinc i (by omega)

private theorem t46_nodup {UL : List Nat} (hlen : UL.length = 693)
    (hinc : ∀ i < 692, UL.getD i 0 < UL.getD (i + 1) 0) : UL.Nodup := by
  have : UL.Pairwise (· < ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    have := t46_inc_lt hinc j i hij (by omega)
    simpa [List.getD_eq_getElem?_getD, hi, hj] using this
  exact this.nodup

private theorem t46_getElem!_toArray (l : List Nat) (i : Nat) : l.toArray[i]! = l.getD i 0 := by
  simp [List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]

private theorem t46_uPos {UL : List Nat} (hnd : UL.Nodup) (hlen : UL.length = 693)
    (hlt : ∀ i < 693, UL.getD i 0 < 4096) {k : Nat} (hk : k < 693) :
    (uPosG UL.toArray)[UL.getD k 0]! = k := by
  have hc : UL.getD k 0 < 4096 := hlt k hk
  unfold uPosG
  rw [getElem!_pos _ _ (by simpa using hc), Array.getElem_ofFn]
  show UL.toArray.toList.idxOf (UL.getD k 0) = k
  rw [List.toList_toArray]
  have h := hnd.idxOf_getElem k (by omega)
  rwa [List.getElem_eq_getD 0] at h

private theorem t46_ap_tvTable (U : Array Nat) (v : Nat) {i : Nat} (hi : i < 693) :
    ap (tvTableG U v) i = (UInt32.ofNat ((uPosG U)[normC (tvC v U[i]!)]!)).toNat := by
  have h1 : (tvTableG U v)[i]! = UInt32.ofNat ((uPosG U)[normC (tvC v U[i]!)]!) := by
    unfold tvTableG
    rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  unfold ap
  rw [h1]

private theorem t46_tvTable_TR {UL : List Nat} {UP v G : Nat} (hnd : UL.Nodup)
    (hlen : UL.length = 693) (hlt : ∀ i < 693, UL.getD i 0 < 4096)
    (hfd : ∀ i < 693, fd 12 UP i = UL.getD i 0) (hperm : IsPermN 693 (fd 10 G))
    (hG : ∀ x < 693, fd 12 UP (fd 10 G x) = normC (tvC v (fd 12 UP x))) :
    TR 693 (tvTableG UL.toArray v) (fd 10 G) := by
  refine ⟨by simp [tvTableG], fun i hi => ⟨?_, hperm.1 i hi⟩⟩
  have hj : fd 10 G i < 693 := hperm.1 i hi
  have h2 : normC (tvC v UL.toArray[i]!) = UL.getD (fd 10 G i) 0 := by
    rw [t46_getElem!_toArray UL i, ← hfd i hi, ← hG i hi, hfd _ hj]
  rw [t46_ap_tvTable _ _ hi, h2, t46_uPos hnd hlen hlt hj, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

private theorem t46_fixAll_iff {T : Table} : t46FixAll T = true ↔ ∀ x < 693, ap T x = x := by
  unfold t46FixAll
  rw [allIn_iff]
  simp only [beq_iff_eq]

private theorem t46_tvTable_zero {UL : List Nat} (hnd : UL.Nodup) (hlen : UL.length = 693)
    (hlt : ∀ i < 693, UL.getD i 0 < 4096)
    (hfix : ∀ x < 693, normC (tvC 0 (UL.getD x 0)) = UL.getD x 0) :
    t46FixAll (tvTableG UL.toArray 0) = true := by
  rw [t46_fixAll_iff]
  intro i hi
  rw [t46_ap_tvTable _ _ hi, t46_getElem!_toArray UL i, hfix i hi, t46_uPos hnd hlen hlt hi,
    UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

private theorem t46_tvGensG (UL : List Nat) : tvGensG UL.toArray = (gensK UL).toArray := by
  unfold tvGensG
  rw [List.filter_toArray, List.push_toArray, gensK_eq]

private theorem t46_gens_getElem (UL : List Nat) (k : Nat) :
    (tvGensG UL.toArray)[k]! = (gensK UL).getD k 0 := by
  rw [t46_tvGensG, t46_getElem!_toArray]

private structure T46Ctx (UL : List Nat) (UP : Nat) (GP : List Nat) : Prop where
  nodup : UL.Nodup
  len : UL.length = 693
  lt : ∀ i < 693, UL.getD i 0 < 4096
  fd12 : ∀ i < 693, fd 12 UP i = UL.getD i 0
  gen : ∀ k < 46, genK UP ((gensK UL).getD k 0) (GP.getD k 0) = true

private theorem T46Ctx.tvTable_TR {UL : List Nat} {UP : Nat} {GP : List Nat} (hc : T46Ctx UL UP GP)
    {k : Nat} (hk : k < 46) :
    TR 693 (tvTableG UL.toArray (tvGensG UL.toArray)[k]!) (fd 10 (GP.getD k 0)) := by
  rw [t46_gens_getElem]
  obtain ⟨-, hperm, hG⟩ := genK_spec (hc.gen k hk)
  exact t46_tvTable_TR hc.nodup hc.len hc.lt hc.fd12 hperm hG

private theorem T46Ctx.genG_TR {UL : List Nat} {UP : Nat} {GP : List Nat} (hc : T46Ctx UL UP GP)
    {z : Int} (hz : 1 ≤ z.natAbs ∧ z.natAbs ≤ 46) :
    TR 693 (genG UL.toArray z) (fd 10 (GP.getD (z.natAbs - 1) 0)) :=
  hc.tvTable_TR (by omega)


private def T46TP (T : Table) (P : Nat) : Prop := TR 693 T (fd 10 P) ∧ P < 2 ^ (10 * 693)

private theorem t46_fd_idP {i : Nat} (hi : i < 693) : fd 10 (idP 693 10) i = i := by
  rw [idP_eq (by norm_num)]
  exact fd_enc (fun j hj => by
    have : (693 : Nat) ≤ 2 ^ 10 := by norm_num
    omega) hi

private theorem t46_fd_compP (A B : Nat) {i : Nat} (hi : i < 693) :
    fd 10 (compP 693 10 A B) i = fd 10 A (fd 10 B i) := by
  rw [compP_eq]
  exact fd_enc (fun x _ => fd_lt _ _ _) hi

private theorem t46_tp_id : T46TP (idT 693) (idP 693 10) := by
  refine ⟨?_, ?_⟩
  · have h := idT_TR (n := 693) (by norm_num)
    refine ⟨h.1, fun i hi => ?_⟩
    rw [t46_fd_idP hi]
    exact h.2 i hi
  · rw [idP_eq (by norm_num)]
    exact enc_lt (fun j hj => by
      have : (693 : Nat) ≤ 2 ^ 10 := by norm_num
      omega)

private theorem t46_tp_comp {T T' : Table} {P P' : Nat} (h : T46TP T P) (h' : T46TP T' P') :
    T46TP (compT 693 T T') (compP 693 10 P P') := by
  obtain ⟨hT, hP⟩ := h
  obtain ⟨hT', hP'⟩ := h'
  have hc := compT_TR (n := 693) (by norm_num) hT hT'
  refine ⟨⟨hc.1, fun i hi => ?_⟩, ?_⟩
  · rw [t46_fd_compP _ _ hi]
    exact hc.2 i hi
  · rw [compP_eq]
    exact enc_lt (fun x _ => fd_lt _ _ _)

private theorem t46_tp_pow {T : Table} {P : Nat} (h : T46TP T P) (e : Nat) :
    T46TP (powT 693 e T) (powP e P) := by
  obtain ⟨hT, hP⟩ := h
  have hc := powT_TR (n := 693) (by norm_num) hT e
  have hv : ∀ x < 693, itr (fd 10 P) e x < 2 ^ 10 := fun x hx => by
    have := (hc.2 x hx).2
    omega
  refine ⟨⟨hc.1, fun i hi => ?_⟩, ?_⟩
  · have : fd 10 (powP e P) i = itr (fd 10 P) e i := by
      rw [powP_eq]
      exact fd_enc hv hi
    rw [this]
    exact hc.2 i hi
  · rw [powP_eq]
    exact enc_lt hv

private theorem t46_tp_fix_iff {T : Table} {P : Nat} (h : T46TP T P) :
    t46FixAll T = true ↔ P = idP 693 10 := by
  rw [t46_fixAll_iff]
  constructor
  · intro hfix
    refine eq_of_fd_eq h.2 t46_tp_id.2 fun i hi => ?_
    rw [← (h.1.2 i hi).1, hfix i hi, t46_fd_idP hi]
  · intro hP x hx
    rw [(h.1.2 x hx).1, hP, t46_fd_idP hx]

private theorem T46Ctx.tp_word {UL : List Nat} {UP : Nat} {GP : List Nat} (hc : T46Ctx UL UP GP)
    {w : List Int} (hw : lettersOK 46 w = true) :
    T46TP (wordT 693 (genG UL.toArray) w) (wordG GP w) := by
  have hw' := (lettersOK_iff 46 w).1 hw
  have hT := wordT_TR (n := 693) (by norm_num) (gens := genG UL.toArray)
    (G := fun z => fd 10 (GP.getD (z.natAbs - 1) 0)) w fun z hz => hc.genG_TR (hw' z hz)
  refine ⟨?_, ?_⟩
  · have hv : ∀ x < 693, wordGF GP w x < 2 ^ 10 := fun x hx => by
      have h1 : wordGF GP w x < 693 := (hT.2 x hx).2
      omega
    refine ⟨hT.1, fun i hi => ?_⟩
    have : fd 10 (wordG GP w) i = wordGF GP w i := by
      rw [wordG_eq]
      exact fd_enc hv hi
    rw [this]
    exact hT.2 i hi
  · rw [wordG_eq]
    refine enc_lt fun x hx => ?_
    have h1 : wordGF GP w x < 693 := (hT.2 x hx).2
    omega


private theorem t46_words_map {WC : List (List Nat)} (hfmt : ∀ w ∈ WC, fmtW w = true) :
    (WC.map strOf).map wordOfInts = WC.map intsK := by
  rw [List.map_map]
  exact List.map_congr_left fun cs hcs => intsK_eq (hfmt cs hcs)

private theorem t46_lettersG_eq {UL : List Nat} {WC : List (List Nat)}
    (hfmt : ∀ w ∈ WC, fmtW w = true) :
    lettersG UL.toArray (WC.map strOf) =
      buildLetters 693 (genG UL.toArray) (WC.map intsK).toArray := by
  unfold lettersG
  rw [t46_words_map hfmt]

private theorem t46_wd_get {WC : List (List Nat)} {j : Nat} (hj : j < WC.length) :
    (WC.map intsK).toArray[j]! = intsK (WC.getD j []) := by
  rw [getElem!_pos _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

private theorem t46_buildLetters_size (n : Nat) (gens : Int → Table) (words : Array (List Int)) :
    (buildLetters n gens words).size = 2 * words.size := by
  simp [buildLetters]

private theorem t46_buildLetters_get (n : Nat) (gens : Int → Table) (words : Array (List Int))
    {l : Nat} (hl : l < 2 * words.size) :
    (buildLetters n gens words)[l]! =
      if l % 2 = 0 then wordT n gens words[l / 2]! else invT n (wordT n gens words[l / 2]!) := by
  unfold buildLetters
  rw [getElem!_pos _ _ (by simpa using hl), Array.getElem_ofFn]

private theorem t46_inv_pair {f g : Nat → Nat} (hg : IsPermN 693 g)
    (hfg : ∀ i < 693, f (g i) = i) : ∀ i < 693, g (f i) = i := by
  intro i hi
  obtain ⟨x, hx, hgx⟩ := hg.surj hi
  have : f i = x := by rw [← hgx]; exact hfg x hx
  rw [this, hgx]

private theorem T46Ctx.letters_TP {UL : List Nat} {UP : Nat} {GP LP : List Nat}
    {WC : List (List Nat)} (hc : T46Ctx UL UP GP) (hfmt : ∀ w ∈ WC, fmtW w = true)
    (hWC : WC.length = 53)
    (hlet : ∀ j < 53, lettersOK 46 (intsK (WC.getD j [])) = true ∧
      LP.getD (2 * j) 0 = wordG GP (intsK (WC.getD j [])) ∧
      permK 693 10 (LP.getD (2 * j + 1) 0) = true ∧
      compP 693 10 (LP.getD (2 * j) 0) (LP.getD (2 * j + 1) 0) = idP 693 10) :
    (lettersG UL.toArray (WC.map strOf)).size = 106 ∧
      ∀ l < 106, T46TP (lettersG UL.toArray (WC.map strOf))[l]! (LP.getD l 0) := by
  rw [t46_lettersG_eq hfmt]
  refine ⟨by simp [t46_buildLetters_size, hWC], fun l hl => ?_⟩
  have hsz : l < 2 * (WC.map intsK).toArray.size := by simp [hWC]; omega
  rw [t46_buildLetters_get _ _ _ hsz]
  obtain ⟨j, rfl | rfl⟩ : ∃ j, l = 2 * j ∨ l = 2 * j + 1 := ⟨l / 2, by omega⟩
  · have hj : j < 53 := by omega
    have e1 : 2 * j / 2 = j := by omega
    have e2 : 2 * j % 2 = 0 := by omega
    rw [if_pos e2, e1, t46_wd_get (by omega)]
    obtain ⟨hw, hA, -, -⟩ := hlet j hj
    rw [hA]
    exact hc.tp_word hw
  · have hj : j < 53 := by omega
    have e1 : (2 * j + 1) / 2 = j := by omega
    have e2 : ¬ (2 * j + 1) % 2 = 0 := by omega
    rw [if_neg e2, e1, t46_wd_get (by omega)]
    obtain ⟨hw, hA, hB, hAB⟩ := hlet j hj
    have hTP := hc.tp_word hw
    rw [← hA] at hTP
    obtain ⟨hBlt, hBperm⟩ := permK_iff.1 hB
    refine ⟨invT_TR (n := 693) (by norm_num) hTP.1 (g := fd 10 (LP.getD (2 * j + 1) 0))
      fun i hi => ?_, hBlt⟩
    have h1 : ∀ i < 693, fd 10 (LP.getD (2 * j) 0) (fd 10 (LP.getD (2 * j + 1) 0) i) = i :=
      fun i hi => by rw [← t46_fd_compP _ _ hi, hAB, t46_fd_idP hi]
    exact ⟨hBperm.1 i hi, h1 i hi, t46_inv_pair hBperm h1 i hi⟩


private theorem t46_mem_lvAt1 {F : Nat → Nat → Nat} {NL : Nat} {bs : List Nat} {l : Nat} :
    l ∈ lvAt F NL bs 1 ↔ l < NL ∧ F l (bs.getD 0 0) = bs.getD 0 0 := by
  simp [lvAt]

private theorem t46_getD_mem {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem t46_orbit_perm {letters : Array Table} {LP lv : List Nat} {b0 r m : Nat}
    {O Pa La : List Nat}
    (hF : ∀ l < 106, ∀ x < 693,
      tabF letters l x = fd 10 (LP.getD l 0) x ∧ fd 10 (LP.getD l 0) x < 693)
    (hLP : LP.length = 106) (hlv : ∀ l, l ∈ lv ↔ l ∈ lvK LP b0) (hm : 0 < m)
    (hO : orbK LP (lvK LP b0) r m O Pa La = true) :
    r < 693 ∧ (BS.run (tabF letters) lv 693 r).pts.Perm O := by
  obtain ⟨hlen, hlt, hnd, hhead, hreach, hcl⟩ := orbK_spec hm hO
  have hlv106 : ∀ l ∈ lv, l < 106 := fun l hl => by
    have := (mem_lvK.1 ((hlv l).1 hl)).1
    omega
  have hFlv : ∀ l ∈ lv, ∀ x < 693, tabF letters l x < 693 := fun l hl x hx => by
    rw [(hF l (hlv106 l hl) x hx).1]
    exact (hF l (hlv106 l hl) x hx).2
  have hr : r < 693 := by
    cases O with
    | nil => simp at hhead
    | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact hlt _ List.mem_cons_self
  refine ⟨hr, run_perm_of_closed hFlv hr hnd hlt hhead (fun i hi hi0 => ?_) (fun p hp l hl => ?_)⟩
  · obtain ⟨a, ha, l, hl, e⟩ := hreach i (by omega) hi0
    have hl106 : l < 106 := by
      have := (mem_lvK.1 hl).1
      omega
    refine ⟨a, ha, l, (hlv l).2 hl, ?_⟩
    rw [(hF l hl106 _ (hlt _ (t46_getD_mem (by omega)))).1]
    exact e
  · have hl106 := hlv106 l hl
    rw [(hF l hl106 p (hlt p hp)).1]
    exact hcl l ((hlv l).1 hl) p hp

private theorem t46_inTree_run {letters : Array Table} {lv : List Nat} {root : Nat} {O : List Nat}
    (hF : ∀ l ∈ lv, ∀ x < 693, tabF letters l x < 693) (hr : root < 693)
    (hperm : (BS.run (tabF letters) lv 693 root).pts.Perm O) {p : Nat} (hp : p < 693) :
    t46InTree (treeOf 693 (BS.run (tabF letters) lv 693 root)) p = decide (p ∈ O) := by
  have hok := run_ok hF hr
  show CFSG.Sporadic.Mathieu.Native.inTreeB _ p = _
  rw [inTreeB_treeOf (by norm_num) hok.lt hok.nodup hp]
  exact decide_eq_decide.2 hperm.mem_iff

private theorem t46_chainTrees_one {letters : Array Table} {B : Array Nat} (hB : 1 < B.size) :
    (chainTrees 693 letters B)[1]! = treeBFS 693 B[1]! letters (levelLetters letters B 1) := by
  unfold chainTrees
  rw [getElem!_pos _ _ (by simpa using hB), Array.getElem_ofFn]

private theorem t46_fd_ge {P x : Nat} (hP : P < 2 ^ (10 * 693)) (hx : 693 ≤ x) : fd 10 P x = 0 := by
  unfold fd
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) (by omega))),
    Nat.zero_mod]

private theorem t46_trees {letters : Array Table} {LP BL O1 Pa1 La1 O2 Pa2 La2 : List Nat} {r : Nat}
    (hsz : letters.size = 106) (hLP : LP.length = 106)
    (hF : ∀ l < 106, ∀ x < 693,
      tabF letters l x = fd 10 (LP.getD l 0) x ∧ fd 10 (LP.getD l 0) x < 693)
    (hLPlt : ∀ l < 106, LP.getD l 0 < 2 ^ (10 * 693))
    (ht : treesK LP BL r O1 Pa1 La1 O2 Pa2 La2 = true) :
    treeOK 693 r (treeBFS 693 r letters (levelLetters letters BL.toArray 1)) letters
        (levelLetters letters BL.toArray 1) = true ∧
      (treeBFS 693 r letters (levelLetters letters BL.toArray 1)).pts.size = 180 ∧
      allIn 0 693 (fun p => p == 0 ||
        t46InTree (chainTrees 693 letters BL.toArray)[1]! p ||
        t46InTree (treeBFS 693 r letters (levelLetters letters BL.toArray 1)) p) = true := by
  obtain ⟨hBL, hO1, hO2, hcov⟩ := treesK_spec ht
  have hb0 : BL.getD 0 0 < 693 := by
    by_contra hcon
    obtain ⟨-, -, -, -, hreach, -⟩ := orbK_spec (by norm_num : 0 < 512) hO1
    obtain ⟨a, ha, l, hl, e⟩ := hreach 1 (by norm_num) (by norm_num)
    obtain ⟨hl106, hfix⟩ := mem_lvK.1 hl
    rw [t46_fd_ge (hLPlt l (by omega)) (by omega)] at hfix
    omega
  have hlvT : (levelLetters letters BL.toArray 1).toList = lvAt (tabF letters) 106 BL 1 := by
    rw [levelLetters_eq, hsz, List.toList_toArray]
  have hlv : ∀ l, l ∈ (levelLetters letters BL.toArray 1).toList ↔ l ∈ lvK LP (BL.getD 0 0) := by
    intro l
    rw [hlvT, t46_mem_lvAt1, mem_lvK, hLP]
    constructor
    · rintro ⟨hl, h⟩
      exact ⟨hl, by rw [← (hF l hl _ hb0).1]; exact h⟩
    · rintro ⟨hl, h⟩
      exact ⟨hl, by rw [(hF l hl _ hb0).1]; exact h⟩
  have hFlv : ∀ l ∈ (levelLetters letters BL.toArray 1).toList, ∀ x < 693,
      tabF letters l x < 693 := fun l hl x hx => by
    have hl106 : l < 106 := by
      have := (mem_lvK.1 ((hlv l).1 hl)).1
      omega
    rw [(hF l hl106 x hx).1]
    exact (hF l hl106 x hx).2
  obtain ⟨hr, hperm2⟩ := t46_orbit_perm hF hLP hlv (by norm_num : 0 < 180) hO2
  obtain ⟨hr1, hperm1⟩ := t46_orbit_perm hF hLP hlv (by norm_num : 0 < 512) hO1
  have hBsz : 1 < BL.toArray.size := by simp [hBL]
  have hlen2 := (orbK_spec (by norm_num : 0 < 180) hO2).1
  have hb1 : BL.toArray[1]! = BL.getD 1 0 := t46_getElem!_toArray BL 1
  have e2 : treeBFS 693 r letters (levelLetters letters BL.toArray 1) =
      treeOf 693 (BS.run (tabF letters) (levelLetters letters BL.toArray 1).toList 693 r) :=
    treeBFS_eq (by norm_num) hr hFlv
  refine ⟨?_, ?_, ?_⟩
  · rw [e2]
    have h := treeOK_treeOf (n := 693) (letters := letters) (root := r)
      (lv := (levelLetters letters BL.toArray 1).toList)
      (s := BS.run (tabF letters) (levelLetters letters BL.toArray 1).toList 693 r) (by norm_num)
      (run_ok hFlv hr) (run_closed hFlv hr) (fun l hl => by
        have := (mem_lvK.1 ((hlv l).1 hl)).1
        omega)
    rwa [Array.toArray_toList] at h
  · rw [e2]
    have : (treeOf 693 (BS.run (tabF letters) (levelLetters letters BL.toArray 1).toList 693 r)
        ).pts.size = (BS.run (tabF letters) (levelLetters letters BL.toArray 1).toList 693 r
        ).pts.length := by
      simp [treeOf]
    rw [this, hperm2.length_eq, hlen2]
  · rw [allIn_iff]
    intro p hp
    rw [t46_chainTrees_one hBsz, hb1, treeBFS_eq (by norm_num) hr1 hFlv, e2,
      t46_inTree_run hFlv hr1 hperm1 hp, t46_inTree_run hFlv hr hperm2 hp]
    rcases hcov p hp with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]


private theorem t46_tw_get {TW : List (List Nat)} {k : Nat} (hk : k < TW.length) :
    (TW.map (List.map Int.ofNat)).toArray[k]! = (TW.getD k []).map Int.ofNat := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp [List.getD_eq_getElem?_getD, hk]

private theorem t46_tp_xy {U : Array Nat} {xw yw : List Int} {X Y : Nat}
    (hX : T46TP (powG U 3 xw) X) (hY : T46TP (powG U 2 yw) Y) (w : List Nat) :
    T46TP (wordT 693 (xyGenG U xw yw) (w.map Int.ofNat)) (wordXY X Y w) := by
  have hT := wordT_TR (n := 693) (by norm_num) (gens := xyGenG U xw yw)
    (G := fun z => fd 10 (if z = 1 then X else Y)) (w.map Int.ofNat) fun z _ => by
      unfold xyGenG
      by_cases h : z = 1
      · simp only [h, if_true]
        exact hX.1
      · simp only [h, if_false]
        exact hY.1
  have hfold : ∀ (w : List Nat) (x : Nat),
      (w.map Int.ofNat).foldr (fun z => fd 10 (if z = 1 then X else Y)) x =
        w.foldr (fun z y => fd 10 (if z = 1 then X else Y) y) x := by
    intro w x
    induction w with
    | nil => rfl
    | cons z w ih =>
      simp only [List.map_cons, List.foldr_cons, ih]
      by_cases h : z = 1
      · simp [h]
      · have : ¬ (Int.ofNat z = 1) := fun hc => h (Int.ofNat.inj hc)
        simp [h, this]
  have hv : ∀ x < 693, w.foldr (fun z y => fd 10 (if z = 1 then X else Y) y) x < 693 :=
    fun x hx => by
      have h1 : (w.map Int.ofNat).foldr (fun z => fd 10 (if z = 1 then X else Y)) x < 693 :=
        (hT.2 x hx).2
      rwa [hfold] at h1
  refine ⟨⟨hT.1, fun i hi => ?_⟩, ?_⟩
  · have e : fd 10 (wordXY X Y w) i = w.foldr (fun z y => fd 10 (if z = 1 then X else Y) y) i := by
      rw [wordXY_eq]
      exact fd_enc (fun x hx => Nat.lt_of_lt_of_le (hv x hx) (by norm_num)) hi
    rw [e]
    have h1 : ap (wordT 693 (xyGenG U xw yw) (w.map Int.ofNat)) i =
        (w.map Int.ofNat).foldr (fun z => fd 10 (if z = 1 then X else Y)) i ∧
        (w.map Int.ofNat).foldr (fun z => fd 10 (if z = 1 then X else Y)) i < 693 := hT.2 i hi
    rwa [hfold] at h1
  · rw [wordXY_eq]
    exact enc_lt fun x hx => Nat.lt_of_lt_of_le (hv x hx) (by norm_num)

theorem t46_sound' {U : Array Nat} {WS : List String} {TWd : Array (List Int)} {xw yw : List Int}
    {B : Array Nat} {r : Nat} {UL BL : List Nat} {UP : Nat} {GP LP O1 Pa1 La1 O2 Pa2 La2 : List Nat}
    {WC TW : List (List Nat)} (hU : U = UL.toArray) (hWS : WS = WC.map CFSG.KC.Misc.O73.strOf)
    (hTW : TWd = (TW.map (List.map Int.ofNat)).toArray) (hB : B = BL.toArray)
    (hp : ptsK UL UP = true) (hg : ∀ k < 46, gensOK UL UP GP k 1 = true)
    (hl : lettersK GP WC LP = true) (ht : treesK LP BL r O1 Pa1 La1 O2 Pa2 La2 = true)
    (hxy : xyK GP xw yw = true) (htv : ∀ k < 46, tvWordsK GP xw yw TW k 1 = true) :
    t46G U WS TWd xw yw B r = true := by
  subst hU hWS hTW hB
  obtain ⟨hUL, -, hfd, hinc, hfix⟩ := ptsK_spec hp
  obtain ⟨-, -, hgen⟩ := gensOK_spec hg
  obtain ⟨hWCl, hLPl, hfmt, hk46, hlet⟩ := lettersK_spec hl
  obtain ⟨hxl, hyl, hx2, hx1, hy3, hy1, hz11, hz1⟩ := xyK_spec hxy
  obtain ⟨hTWl, htw⟩ := tvWordsK_spec htv
  have hnd : UL.Nodup := t46_nodup hUL hinc
  have hlt : ∀ i < 693, UL.getD i 0 < 4096 := fun i hi => by
    have := fd_lt 12 UP i
    rw [hfd i hi] at this
    norm_num at this
    exact this
  have hc : T46Ctx UL UP GP := ⟨hnd, hUL, hlt, hfd, hgen⟩
  have hX : T46TP (powG UL.toArray 3 xw) (powP 3 (wordG GP xw)) := t46_tp_pow (hc.tp_word hxl) 3
  have hY : T46TP (powG UL.toArray 2 yw) (powP 2 (wordG GP yw)) := t46_tp_pow (hc.tp_word hyl) 2
  obtain ⟨hLsz, hLTP⟩ := hc.letters_TP hfmt hWCl hlet
  have hF : ∀ l < 106, ∀ x < 693,
      tabF (lettersG UL.toArray (WC.map strOf)) l x = fd 10 (LP.getD l 0) x ∧
        fd 10 (LP.getD l 0) x < 693 := fun l hl x hx => (hLTP l hl).1.2 x hx
  have hLPlt : ∀ l < 106, LP.getD l 0 < 2 ^ (10 * 693) := fun l hl => (hLTP l hl).2
  obtain ⟨h11, h12, h13⟩ := t46_trees hLsz hLPl hF hLPlt ht
  have hW : (WC.map strOf).map wordOfInts = WC.map intsK := t46_words_map hfmt
  unfold t46G
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hW]
    simp [hWCl]
  · rw [hW, allIn_iff]
    intro k hk
    rw [t46_wd_get (by omega), hk46 k hk]
    simp
  · exact t46_tvTable_zero hnd hUL hlt hfix
  · exact (t46_tp_fix_iff (t46_tp_pow hX 2)).2 hx2
  · exact Bool.eq_false_iff.2 fun h => hx1 ((t46_tp_fix_iff hX).1 h)
  · exact (t46_tp_fix_iff (t46_tp_pow hY 3)).2 hy3
  · exact Bool.eq_false_iff.2 fun h => hy1 ((t46_tp_fix_iff hY).1 h)
  · exact (t46_tp_fix_iff (t46_tp_pow (t46_tp_comp hX hY) 11)).2 hz11
  · exact Bool.eq_false_iff.2 fun h => hz1 ((t46_tp_fix_iff (t46_tp_comp hX hY)).1 h)
  · rw [allIn_iff]
    intro k hk
    rw [t46_tw_get (by omega)]
    have hxyk := t46_tp_xy hX hY (TW.getD k [])
    have hgk := hc.tvTable_TR hk
    unfold t46TblEq
    rw [allIn_iff]
    intro i hi
    rw [(hxyk.1.2 i hi).1, (hgk.2 i hi).1, htw k hk]
    exact beq_self_eq_true _
  · exact h11
  · exact h12
  · exact h13


end CFSG.KS.PK

end
