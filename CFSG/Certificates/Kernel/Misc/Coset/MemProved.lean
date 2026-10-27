module

public import CFSG.Certificates.Kernel.Misc.Coset.MemDefs
import all CFSG.Certificates.Kernel.CosetBounds
import all CFSG.Certificates.Kernel.CosetBoundsLemmas
import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.MiscCoset.Mem.Pf

open CFSG.Certificates CFSG.Certificates.KB CFSG.Certificates.KB.Sound

theorem table_facts {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    (hrels : ∀ r ∈ rels, (∀ x ∈ r, inAlpha amap x.1) → sword gen r = 1)
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) :
    ∃ cnt, L = 2 * cnt ∧ AlphaStruct amap cnt ∧ ∀ f < nF,
      Holds (wordSub gen words) (letterVal gen amap L) (rep (letterVal gen amap L) F D nT) (F f) ∧
        rY (F f) ≠ bad := by
  obtain ⟨hlr, hlw⟩ := tableOk_lens h
  unfold tableOk at h
  simp only [andB_true_iff] at h
  obtain ⟨hL128, hN1, hNl, hlab, hlabbad, hFbad, hnRb, hnSb, -, -, hhdr, hrel, hsub, hwords, hw2,
    htree, hwalk, -⟩ := h
  have hL128' : L + 1 ≤ 128 := Nat.le_of_ble_eq_true hL128
  have hlab' : nLab = nT + 1 := Nat.eq_of_beq_eq_true hlab
  have hlabbad' : nLab + 1 ≤ bad := Nat.le_of_ble_eq_true hlabbad
  have hFbad' : nF + 1 ≤ bad := Nat.le_of_ble_eq_true hFbad
  have hnRb' : nR + 1 ≤ bad := Nat.le_of_ble_eq_true hnRb
  have hnSb' : nS + 1 ≤ bad := Nat.le_of_ble_eq_true hnSb
  have hwalk' := Nat.eq_of_beq_eq_true hwalk
  obtain ⟨heps, hinvOk, halpha⟩ := hdrOk_spec hhdr
  obtain ⟨cnt, hL, hcard, hsurj⟩ := alphaOk_spec halpha
  obtain ⟨hle, hinj⟩ := alpha_struct hcard hsurj
  have hA : AlphaStruct amap cnt := ⟨hle, hinj, hsurj⟩
  obtain ⟨hinvL, hinvc⟩ := invOk_spec hinvOk
  have hLe : L % 2 = 0 := by omega
  have hxor : ∀ c < L, letterVal gen amap L (Nat.xor c 1) = (letterVal gen amap L c)⁻¹ :=
    fun c hc => (letterVal_xor gen hLe hc).2
  have hvL : letterVal gen amap L L = 1 := by
    unfold letterVal
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.lt_irrefl L))]
  have hinvv : ∀ c ≤ L, letterVal gen amap L (byte inv c) = (letterVal gen amap L c)⁻¹ := by
    intro c hc
    rcases Nat.lt_or_eq_of_le hc with hc | rfl
    · rw [hinvc c hc]
      exact hxor c hc
    · rw [hinvL, hvL, inv_one]
  have hR : ∀ i < nR, wLetters (R i) = pkb 256 (wbytes (R i)) ∧
      lv (letterVal gen amap L) (wbytes (R i)) = 1 := by
    unfold relsOk at hrel
    have hfold := Nat.eq_of_beq_eq_true hrel
    have hg := (relsOk_run R amap rels 0).good (by rw [hfold]; omega)
    rw [hfold] at hg
    intro i hi
    obtain ⟨r, hr, hok, hRi⟩ := hg i (Nat.zero_le _) hi
    have hrlen := hlr r hr
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap r (by omega)
    have hin : ∀ x ∈ r, inAlpha amap x.1 := fun x hx => sCode_lt (hs1.1 hok x hx)
    have hcodes : ∀ d ∈ r.map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes (r.length + 2 ^ 24 * pkb 256 (r.map (sCode amap))) = r.map (sCode amap) := by
      rw [wbytes, entry_wN _ _ hrlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hRi, hs2 hok, hwb, entry_wLetters _ _ (by omega), lv_codes gen hA hL r hin]
    exact ⟨rfl, hrels r hr hin⟩
  obtain ⟨hnS, hS⟩ := subsOk_spec hsub (by omega)
  have hwords_in : ∀ w ∈ words, ∀ x ∈ w, inAlpha amap x.1 := by
    intro w hw x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
    have hwlen := hlw _ hw
    exact sCode_lt ((sEnc_spec amap _ (by omega)).1.1 (hS i hi).1 x hx)
  have hSv : ∀ i < nS, lv (letterVal gen amap L) (wbytes (S i)) ∈ wordSub gen words := by
    intro i hi
    rw [hnS] at hi
    obtain ⟨hok, hSi⟩ := hS i hi
    have hwmem : words[i] ∈ words := List.getElem_mem hi
    have hwlen := hlw _ hwmem
    obtain ⟨hs1, hs2⟩ := sEnc_spec amap words[i] (by omega)
    have hcodes : ∀ d ∈ words[i].map (sCode amap), d < 256 := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
      exact hs1.1 hok x hx
    have hwb : wbytes ((words[i].length + 256) + 2 ^ 24 * pkb 256 (words[i].map (sCode amap))) =
        words[i].map (sCode amap) := by
      rw [wbytes, entry_wN_lor _ _ hwlen, entry_wLetters _ _ (by omega)]
      have := bytes_pkb _ hcodes
      rwa [List.length_map] at this
    rw [hSi, hs2 hok, entry_lor _ _ hwlen, hwb, lv_codes gen hA hL _ (hwords_in _ hwmem)]
    exact Subgroup.subset_closure ⟨_, hwmem, rfl⟩
  have hW : ∀ j < nW, (∀ q < wN (Wd j), letter (Wd j) q ≤ L) ∧
      (wKind (Wd j) = 0 → lv (letterVal gen amap L) (wbytes (Wd j)) = 1) ∧
      (wKind (Wd j) = 1 → lv (letterVal gen amap L) (wbytes (Wd j)) ∈ wordSub gen words) := by
    intro j hj
    unfold wordsOkB at hwords
    obtain ⟨h1, h2⟩ := natrec_all2 (fun i => wordOkB R S inv eps nR nS (Wd i))
      (fun i => lettersLe eps (Wd i)) nW hwords j hj
    have := word_sem (wordSub gen words) (letterVal gen amap L) (by omega : eps < 128)
      (by rw [heps]; exact hvL) (fun c hc => hinvv c (by omega)) hR hSv h1 h2
    rwa [heps] at this
  refine ⟨cnt, hL, hA, ?_⟩
  set H := wordSub gen words
  set val := letterVal gen amap L
  have hpairs : ∀ j < nW, Wd2 j = pairs inv (Wd j) := by
    intro j hj
    unfold words2Ok at hw2
    exact Nat.eq_of_beq_eq_true
      (natrec_all (fun j => Nat.beq (Wd2 j) (pairs inv (Wd j))) nW hw2 j hj)
  intro f
  induction f using Nat.strong_induction_on with
  | _ f ih =>
  intro hf
  rcases lt_or_ge f nT with hfT | hfT
  · obtain ⟨h1, -, -, h4⟩ := treeRange_spec htree f hfT
    refine ⟨?_, ?_⟩
    · unfold Holds
      rw [h1, rep_tree val F D nT (f + 1) (by omega) (by omega)
        (by rw [Nat.add_sub_cancel]; exact h4)]
      simp only [Nat.add_sub_cancel]
      exact rel_refl H _
    · rw [h1]
      omega
  · have hgood := (wWalkList_run F Wd2 RW RM nLab nW walk nT).good (by rw [hwalk']; omega)
    rw [hwalk'] at hgood
    obtain ⟨s, t, j, refs, hj, hv⟩ := hgood f hfT hf
    obtain ⟨hs, ht, hkind, hend⟩ := vWalkOk_spec hv
    obtain ⟨hle, hk0, hk1⟩ := hW j hj
    have hwd := hpairs j hj
    have hn : Nat.land (Wd2 j) (nat_lit 255) = wN (Wd j) := by
      rw [hwd, wN_eq]
      change pairs inv (Wd j) &&& (2 ^ 8 - 1) = _
      rw [land_mask]
      exact pairs_low inv (Wd j)
    have hk : Nat.land (Nat.shiftRight (Wd2 j) (nat_lit 8)) (nat_lit 1) = wKind (Wd j) := by
      rw [hwd, wKind_eq]
      change (pairs inv (Wd j) >>> 8) &&& (2 ^ 1 - 1) = _
      rw [land_mask, Nat.shiftRight_eq_div_pow]
      exact pairs_kind inv (Wd j)
    have hpr : ∀ q < Nat.land (Wd2 j) (nat_lit 255),
        pairs inv (Wd j) / 2 ^ (24 + 16 * q) % 65536 = pr inv (Wd j) q := by
      intro q hq
      rw [hn] at hq
      exact pairs_pair inv (Wd j) q hq
    have hlet : ∀ q, letter (Wd j) q < 256 := by
      intro q
      rw [letter_eq]
      exact byte_lt _ _
    have ha : ∀ q < Nat.land (Wd2 j) (nat_lit 255), Nat.land (Nat.shiftRight (Wd2 j)
        (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 255) = letter (Wd j) q := by
      intro q hq
      change (Wd2 j >>> (24 + (q <<< 4))) &&& (2 ^ 8 - 1) = _
      rw [land_mask, Nat.shiftRight_eq_div_pow, shiftLeft_four, hwd,
        ← Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 8 ∣ 65536), hpr q hq, pr,
        (by norm_num : (2 : ℕ) ^ 8 = 256), Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (hlet q)
    have hai : ∀ q < Nat.land (Wd2 j) (nat_lit 255), Nat.shiftRight (Nat.land (Nat.shiftRight
        (Wd2 j) (Nat.add (nat_lit 24) (Nat.shiftLeft q (nat_lit 4)))) (nat_lit 65535))
        (nat_lit 8) = byte inv (letter (Wd j) q) := by
      intro q hq
      change ((Wd2 j >>> (24 + (q <<< 4))) &&& (2 ^ 16 - 1)) >>> 8 = _
      rw [land_mask, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, shiftLeft_four, hwd]
      norm_num only
      rw [hpr q hq, pr, Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (hlet q),
        zero_add]
    have hinv : ∀ q < Nat.land (Wd2 j) (nat_lit 255),
        val (byte inv (letter (Wd j) q)) = (val (letter (Wd j) q))⁻¹ := by
      intro q hq
      rw [hn] at hq
      exact hinvv _ (hle q hq)
    have hW' : lv val ((List.range (Nat.land (Wd2 j) (nat_lit 255))).map (letter (Wd j))) =
        lv val (wbytes (Wd j)) := by
      rw [hn, wbytes, bytes]
      congr 2
      funext q
      exact letter_eq _ _
    have hword : rel H (rep val F D nT s *
        lv val ((List.range (Nat.land (Wd2 j) (nat_lit 255))).map (letter (Wd j))))
        (rep val F D nT s) := by
      rw [hW']
      have hk01 : wKind (Wd j) = 0 ∨ wKind (Wd j) = 1 := by
        rw [wKind_eq]
        omega
      rcases hk01 with h0 | h1
      · rw [hk0 h0, mul_one]
        exact rel_refl H _
      · have hs0 : s = 0 := by
          rcases hkind with hkind | hkind
          · rw [hk, h1] at hkind
            exact absurd hkind one_ne_zero
          · exact hkind
        rw [hs0, rep_zero, one_mul]
        unfold rel
        rw [inv_one, mul_one]
        exact hk1 h1
    exact walk_sound H val (rep val F D nT) F RW RM f (F f) t (Wd2 j) refs s
      (Nat.land (Wd2 j) (nat_lit 255)) (letter (Wd j)) (fun q => byte inv (letter (Wd j) q))
      ha hai hinv (fun g hg => ih g hg (by omega)) hword (by omega) ht hend

theorem invC_eq (a : ℕ) : invC a = Nat.xor a 1 := by
  have hx : Nat.xor a 1 = a ^^^ 1 := rfl
  rw [hx]
  unfold invC
  cases h : Nat.beq (Nat.mod a 2) 0
  · have h2 : a % 2 ≠ 0 := Nat.ne_of_beq_eq_false h
    rw [Nat.xor_one_of_odd (Nat.odd_iff.2 (by omega))]
    rfl
  · have h2 : a % 2 = 0 := Nat.eq_of_beq_eq_true h
    rw [Nat.xor_one_of_even (Nat.even_iff.2 h2)]

theorem memWalk_nil (F : ℕ → ℕ) (f : ℕ) (refs : List ℕ) (cur : ℕ) :
    memWalk F f [] refs cur = cur := rfl

theorem memWalk_cons (F : ℕ → ℕ) (f a : ℕ) (w : List ℕ) (r : ℕ) (refs : List ℕ) (cur : ℕ) :
    memWalk F f (a :: w) (r :: refs) cur = memWalk F f w refs (refStep F f r a (invC a) cur) := rfl

theorem memWalk_none (F : ℕ → ℕ) (f a : ℕ) (w : List ℕ) (cur : ℕ) :
    memWalk F f (a :: w) [] cur = bad := rfl

theorem refStep_bad {F : ℕ → ℕ} {f : ℕ} (hF : ∀ g < f, rY (F g) ≠ bad) (r a ai : ℕ) :
    refStep F f r a ai bad = bad := by
  unfold refStep
  cases hg : Nat.ble f (Nat.shiftRight r (nat_lit 1))
  · have hlt : Nat.shiftRight r (nat_lit 1) < f := ble_false hg
    dsimp only
    cases Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)
    · exact fwd_bad _ _
    · exact bwd_bad _ (hF _ hlt)
  · rfl

theorem memWalk_bad {F : ℕ → ℕ} {f : ℕ} (hF : ∀ g < f, rY (F g) ≠ bad) :
    ∀ (w refs : List ℕ), memWalk F f w refs bad = bad
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: w, r :: refs => by
    rw [memWalk_cons, refStep_bad hF]
    exact memWalk_bad hF w refs

theorem memWalk_rel {G : Type*} [Group G] (H : Subgroup G) (val rep : ℕ → G) {F : ℕ → ℕ}
    {f : ℕ} (hfacts : ∀ g < f, Holds H val rep (F g) ∧ rY (F g) ≠ bad) :
    ∀ (w refs : List ℕ) (cur : ℕ), (∀ a ∈ w, val (invC a) = (val a)⁻¹) →
      memWalk F f w refs cur ≠ bad → rel H (rep cur * lv val w) (rep (memWalk F f w refs cur))
  | [], _, cur, _, _ => by
    rw [lv_nil, mul_one, memWalk_nil]
    exact rel_refl H _
  | _ :: _, [], _, _, h => absurd (memWalk_none _ _ _ _ _) h
  | a :: w, r :: refs, cur, hinv, h => by
    rw [memWalk_cons] at h ⊢
    have hstep : refStep F f r a (invC a) cur ≠ bad := by
      intro e
      rw [e, memWalk_bad (fun g hg => (hfacts g hg).2)] at h
      exact h rfl
    have ih := memWalk_rel H val rep hfacts w refs _ (fun b hb => hinv b (List.mem_cons_of_mem _ hb))
      h
    have hone : rel H (rep cur * val a) (rep (refStep F f r a (invC a) cur)) := by
      unfold refStep at hstep ⊢
      cases hg : Nat.ble f (Nat.shiftRight r (nat_lit 1))
      · rw [hg] at hstep
        dsimp only at hstep ⊢
        have hlt : Nat.shiftRight r (nat_lit 1) < f := ble_false hg
        have hH := (hfacts _ hlt).1
        unfold Holds at hH
        cases hd : Nat.beq (Nat.land r (nat_lit 1)) (nat_lit 1)
        · rw [hd] at hstep
          dsimp only at hstep ⊢
          obtain ⟨h1, h2, h3⟩ := fwd_spec hstep
          rw [h3]
          rw [h1, h2] at hH
          exact hH
        · rw [hd] at hstep
          dsimp only at hstep ⊢
          obtain ⟨h1, h2, h3⟩ := bwd_spec hstep
          rw [h3]
          rw [h1, h2, hinv a (List.mem_cons_self ..)] at hH
          have := rel_mul_right (val a) (rel_symm hH)
          rwa [inv_mul_cancel_right] at this
      · rw [hg] at hstep
        exact absurd rfl hstep
    rw [lv_cons, ← mul_assoc]
    exact rel_trans (rel_mul_right _ hone) ih

end CFSG.KC.MiscCoset.Mem.Pf

end

public section

namespace CFSG.KC.MiscCoset.Mem

open CFSG.Certificates CFSG.Certificates.KB CFSG.Certificates.KB.Sound CFSG.KC.MiscCoset.Mem.Pf

theorem memOK_sound_proved {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    (hrels : ∀ r ∈ rels, KB.sword gen r = 1)
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap m : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hm : m < 128) (htop : KB.topOk amap m = true) {u : List (ℕ × Bool)}
    (hu : ∀ l ∈ u, l.1 < m) {refs : List ℕ} (hw : memOK F nF (u.map codeN) refs = true) :
    KB.sword gen u ∈ KB.wordSub gen words := by
  obtain ⟨cnt, hL, hA, hfacts⟩ := table_facts gen (fun r hr _ => hrels r hr) h
  have hin : ∀ l ∈ u, inAlpha amap l.1 := fun l hl => (topOk_sound (by omega) htop l.1).2 (hu l hl)
  have hcode : ∀ l ∈ u, sCode amap l = codeN l := by
    intro l hl
    obtain ⟨g, b⟩ := l
    have hg := hin (g, b) hl
    have hgm : g < m := hu (g, b) hl
    have hg' : g < 256 ∧ byte amap g ≠ 0 := hg
    rw [sCode_eq, ite_eq_left_of_eq_true _ _ (eq_true hg')]
    unfold topOk at htop
    rw [Nat.eq_of_beq_eq_true htop, (idAmap_spec m (by omega)).2 g, ite_eq_left_of_eq_true _ _
      (eq_true hgm), codeN]
    simp
  have hmap : u.map codeN = u.map (sCode amap) :=
    List.map_congr_left fun l hl => (hcode l hl).symm
  have hlv : lv (letterVal gen amap L) (u.map codeN) = KB.sword gen u := by
    rw [hmap]
    exact lv_codes gen hA hL u hin
  have hinv : ∀ a ∈ u.map codeN, letterVal gen amap L (invC a) = (letterVal gen amap L a)⁻¹ := by
    intro a ha
    rw [hmap, List.mem_map] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    rw [invC_eq]
    exact (letterVal_xor gen (by omega) (sCode_val gen hA hL l.2 (hin l hl)).1).2
  have hend := Nat.eq_of_beq_eq_true hw
  have hrel := memWalk_rel (wordSub gen words) (letterVal gen amap L)
    (rep (letterVal gen amap L) F D nT) hfacts (u.map codeN) refs 0 hinv (by
      rw [hend]
      decide)
  rw [hend, rep_zero, one_mul, hlv] at hrel
  unfold rel at hrel
  rwa [inv_one, mul_one] at hrel

end CFSG.KC.MiscCoset.Mem

end
