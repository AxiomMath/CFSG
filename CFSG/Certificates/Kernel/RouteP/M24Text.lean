module

public import Certificates.Data.Kernel.RouteP.M24Text
public import Certificates.Data.RouteP.M24Defect
public import CFSG.Certificates.Kernel.RouteP.TextSlp
public import CFSG.Certificates.Kernel.RouteP.TextSplit

public section

namespace CFSG.KS.RouteP

open String CFSG.KC.Str CFSG.KC.RouteP Certificates.RouteP.M24Defect

theorem take_drop_succ {cs : List Char} {b k : Nat} (h : b + k < cs.length) :
    (cs.drop b).take (k + 1) = (cs.drop b).take k ++ [cs.getD (b + k) 'a'] := by
  rw [List.take_succ, List.getElem?_drop, List.getElem?_eq_getElem h, List.getD_eq_getElem _ _ h]
  rfl

theorem drop_getD {cs : List Char} {i : Nat} (h : i < cs.length) :
    cs.drop i = cs.getD i 'a' :: cs.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem _ _ h]

theorem splitSL_two {a c : Char} {cs : List Char} : ∀ (f b i j : Nat) (r : List (List Char)),
    i ≤ cs.length → j ≤ 1 → b + j ≤ i → (j = 1 → cs.getD (i - 1) 'a' = a) →
    3 * (cs.length - i) + 2 * j < f →
    splitSL cs [a, c] cs.length f b i j r =
      r.reverse ++ split2K a c (cs.drop i) ((cs.drop b).take (i - j - b)).reverse (j == 1)
  | 0, _, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, b, i, j, r, hi, hj, hb, ha, hf => by
    rw [splitSL]
    by_cases hn : cs.length ≤ i
    · rw [if_pos hn, show i = cs.length by omega, List.drop_length]
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp [split2K]
      · have ha' := ha rfl
        have e := take_drop_succ (cs := cs) (b := b) (k := cs.length - 1 - b) (by omega)
        rw [show b + (cs.length - 1 - b) = cs.length - 1 by omega,
          show cs.length - 1 - b + 1 = cs.length - b by omega,
          show cs.length = i by omega, ha'] at e
        rw [show cs.length = i by omega, e]
        simp [split2K]
    · rw [if_neg hn]
      have hd := drop_getD (cs := cs) (i := i) (by omega)
      have hii : cs.getD (i + 1 - 1) 'a' = cs.getD i 'a' := by rw [Nat.add_sub_cancel]
      generalize hch : cs.getD i 'a' = ch at hd hii
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · have e := take_drop_succ (cs := cs) (b := b) (k := i - b) (by omega)
        rw [show b + (i - b) = i by omega, hch] at e
        by_cases hc : (ch == a) = true
        · have hc' : ch = a := by simpa using hc
          rw [if_pos (by simpa using hc), if_neg (by simp),
            splitSL_two f b (i + 1) 1 r (by omega) le_rfl (by omega) (fun _ => by rw [hii, hc'])
              (by omega), hd, show i + 1 - 1 - b = i - b by omega, Nat.sub_zero]
          simp [split2K, hc'] <;> rfl
        · rw [if_neg (by simpa using hc), Nat.sub_zero,
            splitSL_two f b (i + 1) 0 r (by omega) (Nat.zero_le _) (by omega) (by simp) (by omega),
            hd, show i + 1 - 0 - b = i - b + 1 by omega, e]
          simp [split2K, hc] <;> rfl
      · have ha' := ha rfl
        have e := take_drop_succ (cs := cs) (b := b) (k := i - 1 - b) (by omega)
        rw [show b + (i - 1 - b) = i - 1 by omega, show i - 1 - b + 1 = i - b by omega, ha'] at e
        by_cases hc : (ch == c) = true
        · rw [if_pos (by simpa using hc), if_pos (by simp),
            splitSL_two f (i + 1) (i + 1) 0 _ (by omega) (Nat.zero_le _) (by omega) (by simp)
              (by omega), hd]
          simp [split2K, hc] <;> rfl
        · rw [if_neg (by simpa using hc), show i - 1 + 1 = i by omega,
            splitSL_two f b i 0 r (by omega) (Nat.zero_le _) (by omega) (by simp) (by omega), hd,
            show i - 0 - b = i - b by omega, e]
          by_cases hca : ch = a
          · have hac : a ≠ c := fun h => hc (by simp [hca, h])
            simp [split2K, hc, hca, hac] <;> rfl
          · simp [split2K, hc, hca] <;> rfl

theorem splitSepL_two (a c : Char) (cs : List Char) :
    splitSepL cs [a, c] = split2K a c cs [] false := by
  unfold splitSepL
  rw [splitSL_two _ 0 0 0 [] (Nat.zero_le _) (Nat.zero_le _) le_rfl (by simp)
    (by simp only [List.length_cons, List.length_nil]; omega)]
  simp

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (y : β), (∀ x ∈ l, ∀ y, f y x = g y x) → l.foldl f y = l.foldl g y
  | [], _, _ => rfl
  | x :: l, y, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) y,
      foldl_congr_mem f g l _ fun z hz => h z (by simp [hz])]

theorem foldl_toArray {α β : Type} (F : Array β → α → Array β) (G : List β → α → List β) :
    ∀ (l : List α) (y : List β), (∀ x ∈ l, ∀ y : List β, F y.toArray x = (G y x).toArray) →
      l.foldl F y.toArray = (l.foldl G y).toArray
  | [], _, _ => rfl
  | x :: l, y, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp) y,
      foldl_toArray F G l _ fun z hz => h z (by simp [hz])]

theorem toNat!_digits {t : List Char} (h : digitsL t = true) :
    (String.ofList t).toNat! = decVal t := by
  obtain ⟨hne, hd⟩ := digitsL_iff h
  exact toNat!_ofList hne hd

theorem ofList_bne (x y : List Char) : (String.ofList x != String.ofList y) = (x != y) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  exact Iff.not ⟨fun e => by simpa using congrArg String.toList e, congrArg _⟩

theorem tok_eq {t : List Char} (h : (t.isEmpty || digitsL t) = true) :
    (if String.ofList t = "" then none else some (String.ofList t).toNat!) = tokNat t := by
  cases t with
  | nil => rfl
  | cons c ds =>
    simp only [List.isEmpty_cons, Bool.false_or] at h
    have hne : String.ofList (c :: ds) ≠ "" := fun e => by
      simpa using congrArg String.toList e
    rw [if_neg hne, toNat!_digits h]
    simp [tokNat]

theorem parseNats_ofList {l : List Char} (h : natsOKL l = true) :
    parseNats (String.ofList l) = natsL l := by
  unfold parseNats natsL
  rw [sp_eq, splitOn_ofList, ← splitK_eq]
  exact filterMap_congr' _ _ _ _ fun t ht => tok_eq (List.all_eq_true.1 h t ht)

theorem parseWord_ofList (b : List Char) : parseWord (String.ofList b) = m24WordL b := by
  unfold parseWord m24WordL
  rw [toList_ofList]

theorem treeTab_ofList {cs : List Char} (e : treeText = String.ofList cs)
    (h : treeOKL cs = true) : treeTab () = (treeTabL cs).toArray := by
  unfold treeTab treeTabL
  rw [e, nl_eq, splitOn_ofList, ← splitK_eq, List.foldl_map, ← List.toArray_replicate]
  apply foldl_toArray
  intro l hl y
  unfold treeOKL at h
  have hl' := List.all_eq_true.1 h l hl
  unfold treeStepL
  rw [sp_eq, splitOn_ofList, ← splitK_eq]
  generalize splitK ' ' l = ts at hl' ⊢
  rcases ts with _ | ⟨u, _ | ⟨v, _ | ⟨b, _ | ⟨w, ts⟩⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · simp only [Bool.and_eq_true] at hl'
    simp only [List.map_cons, List.map_nil]
    rw [toNat!_digits hl'.1, toNat!_digits hl'.2, parseWord_ofList, Array.set!_eq_setIfInBounds,
      List.setIfInBounds_toArray]
  · rfl

theorem comboData_ofList {cs : List Char} (e : comboText = String.ofList cs)
    (hc : ∀ c ∈ cs, c.toNat < 128) (h : comboOKL cs = true) : comboData () = comboDataL cs := by
  unfold comboData comboDataL
  have es : ("C\n" : String) = String.ofList ['C', '\n'] := by
    rw [← String.toList_inj, String.toList_ofList]
  have hs : ∀ c ∈ ['C', '\n'], c.toNat < 128 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> decide
  rw [e, es, splitOn_ofList_sep hc hs (by decide), splitSepL_two, ← List.map_drop,
    List.map_map]
  apply List.map_congr_left
  intro blk hblk
  unfold comboOKL at h
  have hb := List.all_eq_true.1 h blk hblk
  simp only [Function.comp]
  rw [nl_eq, splitOn_ofList, ← splitK_eq]
  exact filterMap_congr' _ _ _ _ fun l hl => by
    unfold comboEntL
    rw [parseNats_ofList (List.all_eq_true.1 hb l hl)]
    rcases natsL l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

theorem bezLines_ofList (cs : List Char) :
    ((String.ofList cs).splitOn "\n").filter (· != "") = (bezLinesL cs).map String.ofList := by
  unfold bezLinesL
  rw [nl_eq, splitOn_ofList, ← splitK_eq, List.filter_map]
  congr 2
  funext x
  exact ofList_bne x []

theorem bneT : ((· != "T") ∘ String.ofList) = (· != ['T']) := by
  funext x
  exact ofList_bne x ['T']

theorem sData_ofList {cs : List Char} (e : bezoutText = String.ofList cs)
    (h : bezOKL cs = true) : sData () = sDataL cs := by
  unfold sData sDataL
  dsimp only
  rw [e, bezLines_ofList, ← List.map_drop, List.takeWhile_map, bneT]
  unfold bezOKL at h
  rw [Bool.and_eq_true] at h
  exact filterMap_congr' _ _ _ _ fun l hl => by
    unfold sEntL
    rw [parseNats_ofList (List.all_eq_true.1 h.1 l hl)]
    rcases natsL l with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl

theorem tData_ofList {cs : List Char} (e : bezoutText = String.ofList cs)
    (h : bezOKL cs = true) : tData () = tDataL cs := by
  unfold tData tDataL
  dsimp only
  rw [e, bezLines_ofList, List.dropWhile_map, bneT, ← List.map_drop, List.map_map]
  unfold bezOKL at h
  rw [Bool.and_eq_true] at h
  apply List.map_congr_left
  intro l hl
  exact parseNats_ofList (List.all_eq_true.1 h.2 l hl)

end CFSG.KS.RouteP
