module

public import CFSG.Certificates.Kernel.Misc.Coset.MemDefs
public import Certificates.Data.Kernel.Bounds.Facts
import all CFSG.Certificates.Kernel.CosetBounds
import all CFSG.Certificates.Kernel.CosetBoundsLemmas
import CFSG.Certificates.Kernel.Misc.Coset.MemProved
import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.MiscCoset.Partial

open CFSG.Certificates CFSG.Certificates.KB CFSG.Certificates.KB.Sound CFSG.KC.MiscCoset.Mem
  CFSG.KC.MiscCoset.Mem.Pf

theorem factsOk_facts {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    (hrels : ∀ r ∈ rels, (∀ x ∈ r, inAlpha amap x.1) → sword gen r = 1)
    {words : List (List (ℕ × Bool))} {walk : List ℕ}
    (h : factsOk inv L eps nLab nT RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk =
      true) :
    ∃ cnt, L = 2 * cnt ∧ AlphaStruct amap cnt ∧ ∀ f < nF,
      Holds (wordSub gen words) (letterVal gen amap L) (rep (letterVal gen amap L) F D nT) (F f) ∧
        rY (F f) ≠ bad := by
  unfold factsOk at h
  simp only [andB_true_iff] at h
  obtain ⟨hL128, hlab, hlabbad, hFbad, hnRb, hnSb, hlr0, hlw0, hhdr, hrel, hsub, hwords, hw2,
    htree, hwalk⟩ := h
  have hlr := (lensLt_iff _ _).mp hlr0
  have hlw := (lensLt_iff _ _).mp hlw0
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

theorem codes_spec {G : Type*} [Group G] (gen : ℕ → G) {amap L cnt m : ℕ} (hL : L = 2 * cnt)
    (hA : AlphaStruct amap cnt) (hm : m < 128) (htop : topOk amap m = true) {u : List (ℕ × Bool)}
    (hu : ∀ l ∈ u, l.1 < m) :
    lv (letterVal gen amap L) (u.map codeN) = sword gen u ∧
      ∀ a ∈ u.map codeN, letterVal gen amap L (invC a) = (letterVal gen amap L a)⁻¹ := by
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
  refine ⟨by rw [hmap]; exact lv_codes gen hA hL u hin, ?_⟩
  intro a ha
  rw [hmap, List.mem_map] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  rw [invC_eq]
  exact (letterVal_xor gen (by omega) (sCode_val gen hA hL l.2 (hin l hl)).1).2

theorem factsOk_mem {G : Type*} [Group G] (gen : ℕ → G) {rels : List (List (ℕ × Bool))}
    (hrels : ∀ r ∈ rels, KB.sword gen r = 1)
    {inv L eps nLab nT RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap m : ℕ}
    {words : List (List (ℕ × Bool))} {walk : List ℕ}
    (h : KB.factsOk inv L eps nLab nT RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk =
      true) (hm : m < 128) (htop : KB.topOk amap m = true) {u : List (ℕ × Bool)}
    (hu : ∀ l ∈ u, l.1 < m) {refs : List ℕ} (hw : memOK F nF (u.map codeN) refs = true) :
    KB.sword gen u ∈ KB.wordSub gen words := by
  obtain ⟨cnt, hL, hA, hfacts⟩ := factsOk_facts gen (fun r hr _ => hrels r hr) h
  obtain ⟨hlv, hinv⟩ := codes_spec gen hL hA hm htop hu
  have hend := Nat.eq_of_beq_eq_true hw
  have hrel := memWalk_rel (wordSub gen words) (letterVal gen amap L)
    (rep (letterVal gen amap L) F D nT) hfacts (u.map codeN) refs 0 hinv (by
      rw [hend]
      decide)
  rw [hend, rep_zero, one_mul, hlv] at hrel
  unfold rel at hrel
  rwa [inv_one, mul_one] at hrel

@[expose] noncomputable def rowF (r j : Nat) : Nat :=
  fld r (Nat.shiftLeft j (nat_lit 5)) (nat_lit 4294967295)

@[expose] noncomputable def lenN {α : Type} (w : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ n => Nat.succ n) w

@[expose] noncomputable def unpackRefs (r o n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil (fun i acc => List.cons (rowF r (Nat.add o i)) acc) n

@[expose] noncomputable def rowMem (rows : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => orB (Nat.beq (rowF r (nat_lit 0)) y) ih)
    rows

@[expose] noncomputable def rowWalks (F : Nat → Nat) (f : Nat) (rows : List Nat) (r : Nat)
    (ws : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun w _ ih k o => andB
      (andB (Nat.beq (memWalk F f w (unpackRefs r o (lenN w)) (rowF r (nat_lit 0))) (rowF r k))
        (rowMem rows (rowF r k)))
      (ih (Nat.succ k) (Nat.add o (lenN w)))) ws

@[expose] noncomputable def orbAll (F : Nat → Nat) (f : Nat) (rows : List Nat)
    (ws : List (List Nat)) (qs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (rowWalks F f rows r ws (nat_lit 1) (Nat.succ (lenN ws))) ih) qs

@[expose] noncomputable def orbOk (F : Nat → Nat) (f : Nat) (rows : List Nat)
    (ws : List (List Nat)) : Bool :=
  andB (rowMem rows (nat_lit 0)) (orbAll F f rows ws rows)

theorem lenN_eq {α : Type} : ∀ w : List α, lenN w = w.length
  | [] => rfl
  | _ :: w => congrArg Nat.succ (lenN_eq w)

theorem rowMem_spec {rows : List Nat} {y : Nat} (h : rowMem rows y = true) :
    ∃ r ∈ rows, rowF r 0 = y := by
  induction rows with
  | nil =>
    change false = true at h
    exact absurd h Bool.false_ne_true
  | cons r rows ih =>
    change orB (Nat.beq (rowF r 0) y) (rowMem rows y) = true at h
    rcases orB_true_iff.1 h with h | h
    · exact ⟨r, List.mem_cons_self .., Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨r', hr', e⟩ := ih h
      exact ⟨r', List.mem_cons_of_mem _ hr', e⟩

theorem rowF_lt (r j : Nat) : rowF r j < bad := by
  have : rowF r j ≤ 4294967295 := Nat.and_le_right
  change rowF r j < 4611686018427387904
  omega

theorem rowWalks_spec {G : Type*} [Group G] (H : Subgroup G) (val rep : ℕ → G) {F : ℕ → ℕ}
    {f : ℕ} (hfacts : ∀ g < f, Holds H val rep (F g) ∧ rY (F g) ≠ bad) (rows : List Nat)
    (r : Nat) : ∀ (ws : List (List Nat)) (k o : Nat), (∀ w ∈ ws, ∀ a ∈ w, val (invC a) = (val a)⁻¹) →
      rowWalks F f rows r ws k o = true →
      ∀ w ∈ ws, ∃ r' ∈ rows, rel H (rep (rowF r 0) * lv val w) (rep (rowF r' 0))
  | [], _, _, _, _ => fun _ hw => absurd hw List.not_mem_nil
  | w :: ws, k, o, hinv, h => by
    change andB (andB _ _) (rowWalks F f rows r ws (Nat.succ k) (Nat.add o (lenN w))) = true at h
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h
    obtain ⟨he, hm⟩ := andB_true_iff.1 h1
    intro w' hw'
    rcases List.mem_cons.1 hw' with rfl | hw'
    · obtain ⟨r', hr', e⟩ := rowMem_spec hm
      have he' := Nat.eq_of_beq_eq_true he
      refine ⟨r', hr', ?_⟩
      have := memWalk_rel H val rep hfacts w' _ (rowF r 0) (hinv w' (List.mem_cons_self ..))
        (by rw [he']; exact (rowF_lt r k).ne)
      rwa [he', ← e] at this
    · exact rowWalks_spec H val rep hfacts rows r ws _ _
        (fun v hv => hinv v (List.mem_cons_of_mem _ hv)) h2 w' hw'

theorem orbOk_spec {G : Type*} [Group G] (H : Subgroup G) (val rep : ℕ → G) {F : ℕ → ℕ}
    {f : ℕ} (hfacts : ∀ g < f, Holds H val rep (F g) ∧ rY (F g) ≠ bad) {rows : List Nat}
    {ws : List (List Nat)} (hinv : ∀ w ∈ ws, ∀ a ∈ w, val (invC a) = (val a)⁻¹)
    (h : orbOk F f rows ws = true) :
    (∃ r ∈ rows, rowF r 0 = 0) ∧
      ∀ r ∈ rows, ∀ w ∈ ws, ∃ r' ∈ rows, rel H (rep (rowF r 0) * lv val w) (rep (rowF r' 0)) := by
  obtain ⟨h0, hall⟩ := andB_true_iff.1 h
  refine ⟨rowMem_spec h0, ?_⟩
  suffices ∀ qs : List Nat, orbAll F f rows ws qs = true → ∀ r ∈ qs, ∀ w ∈ ws,
      ∃ r' ∈ rows, rel H (rep (rowF r 0) * lv val w) (rep (rowF r' 0)) from this rows hall
  intro qs
  induction qs with
  | nil => exact fun _ _ hr => absurd hr List.not_mem_nil
  | cons q qs ih =>
    intro hq r hr
    change andB (rowWalks F f rows q ws 1 (Nat.succ (lenN ws))) (orbAll F f rows ws qs) = true
      at hq
    obtain ⟨h1, h2⟩ := andB_true_iff.1 hq
    rcases List.mem_cons.1 hr with rfl | hr
    · exact rowWalks_spec H val rep hfacts rows r ws _ _ hinv h1
    · exact ih h2 r hr

theorem lv_rev_invC {G : Type*} [Group G] (val : ℕ → G) :
    ∀ W : List ℕ, (∀ a ∈ W, val (invC a) = (val a)⁻¹) →
      lv val ((W.map invC).reverse) = (lv val W)⁻¹
  | [], _ => by rw [List.map_nil, List.reverse_nil, lv_nil, inv_one]
  | a :: W, h => by
    rw [List.map_cons, List.reverse_cons, lv_append, lv_singleton,
      lv_rev_invC val W fun b hb => h b (List.mem_cons_of_mem _ hb), lv_cons,
      h a List.mem_cons_self, mul_inv_rev]

theorem invC_invC (a : ℕ) : invC (invC a) = a := by
  rw [invC_eq, invC_eq]
  change (a ^^^ 1) ^^^ 1 = a
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem closure_orbit {G : Type*} [Group G] (H : Subgroup G) (rep : ℕ → G) (X : Set ℕ)
    (s : Set G) (hstep : ∀ x ∈ X, ∀ g ∈ s, (∃ y ∈ X, rel H (rep x * g) (rep y)) ∧
      ∃ y ∈ X, rel H (rep x * g⁻¹) (rep y)) :
    ∀ g ∈ Subgroup.closure s, ∀ x ∈ X, ∃ y ∈ X, rel H (rep x * g) (rep y) := by
  intro g hg
  induction hg using Subgroup.closure_induction'' with
  | mem g hg => exact fun x hx => (hstep x hx g hg).1
  | inv_mem g hg => exact fun x hx => (hstep x hx g hg).2
  | one => exact fun x hx => ⟨x, hx, by rw [mul_one]; exact rel_refl H _⟩
  | mul g g' _ _ ih ih' =>
    intro x hx
    obtain ⟨y, hy, h1⟩ := ih x hx
    obtain ⟨z, hz, h2⟩ := ih' y hy
    refine ⟨z, hz, ?_⟩
    rw [← mul_assoc]
    exact rel_trans (rel_mul_right g' h1) h2

theorem card_le_of_reps {G : Type*} [Group G] (H K : Subgroup G) [Finite H] (rep : ℕ → G)
    (X : List ℕ) (h : ∀ g ∈ K, ∃ y ∈ X, rel H g (rep y)) :
    Finite K ∧ Nat.card K ≤ Nat.card H * X.length := by
  classical
  have hc : ∀ g : K, ∃ i : Fin X.length, (g : G) * (rep (X.get i))⁻¹ ∈ H := by
    intro g
    obtain ⟨y, hy, hr⟩ := h g g.2
    obtain ⟨i, rfl⟩ := List.get_of_mem hy
    exact ⟨i, hr⟩
  choose ι hι using hc
  let φ : K → H × Fin X.length := fun g => (⟨g * (rep (X.get (ι g)))⁻¹, hι g⟩, ι g)
  have hφ : Function.Injective φ := by
    intro g g' e
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    rw [e2] at e1
    exact Subtype.ext (mul_right_cancel e1)
  have := Finite.of_injective φ hφ
  refine ⟨this, ?_⟩
  have hle := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at hle

theorem eq_one_of_mem_zpowers {G : Type*} [Group G] {c x : G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hc : c ^ p = 1) (hx : x ∈ Subgroup.zpowers c) (hx2 : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ orderOf c := orderOf_dvd_of_mem_zpowers hx
  have h2 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hc
  have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have h4 : orderOf x ∣ Nat.gcd p 2 := Nat.dvd_gcd (h1.trans h2) h3
  rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact h4

end CFSG.KC.MiscCoset.Partial

end
