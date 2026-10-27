module

public import Certificates.Data.Kernel.B3SixK

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

theorem pAux_eq : ∀ (f : ℕ) (ts is : List ℕ),
    (ts.length + is.length) ^ 2 + ts.length < f → pAux f ts is = List.permutationsAux ts is
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, [], is, _ => by simp [pAux, List.permutationsAux_nil]
  | f + 1, t :: ts, is, h => by
      have h1 : (ts.length + (t :: is).length) ^ 2 + ts.length < f := by
        simp only [List.length_cons] at h ⊢
        have : ts.length + 1 + is.length = ts.length + (is.length + 1) := by omega
        rw [← this]
        omega
      have h2 : (is.length + ([] : List ℕ).length) ^ 2 + is.length < f := by
        simp only [List.length_cons, List.length_nil, Nat.add_zero] at h ⊢
        nlinarith
      rw [List.permutationsAux_cons, List.permutations, ← pAux_eq f ts (t :: is) h1,
        ← pAux_eq f is [] h2]
      rfl

theorem permsK_eq (l : List ℕ) : permsK l = l.permutations := by
  unfold permsK List.permutations
  rw [pAux_eq _ l [] (by simp)]

theorem sym6K_eq : sym6K = allTabs 6 := permsK_eq _

theorem mem_dedupF : ∀ (seen l : List Tab) (x : Tab), x ∈ dedupF seen l ↔ x ∈ l ∧ x ∉ seen
  | seen, [], x => by simp [dedupF]
  | seen, y :: ys, x => by
    by_cases hy : seen.contains y = true
    · have hy' : y ∈ seen := List.contains_iff_mem.1 hy
      simp only [dedupF, hy, ↓reduceIte, mem_dedupF seen ys x, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (h1 ▸ hy') h2
        · exact ⟨h1, h2⟩
    · have hy' : y ∉ seen := fun h => hy (List.contains_iff_mem.2 h)
      simp only [dedupF, hy, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        mem_dedupF (y :: seen) ys x, not_or]
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · exact ⟨Or.inl h, h ▸ hy'⟩
        · exact ⟨Or.inr h1, h3⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases hxy : x = y
          · exact Or.inl hxy
          · exact Or.inr ⟨h1, hxy, h2⟩

theorem mem_dedupF_nil (l : List Tab) (x : Tab) : x ∈ dedupF [] l ↔ x ∈ l := by
  simp [mem_dedupF]

theorem any_dedupF (l : List Tab) (p : Tab → Bool) : (dedupF [] l).any p = l.any p := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, mem_dedupF_nil]

theorem all_dedupF (l : List Tab) (p : Tab → Bool) : (dedupF [] l).all p = l.all p := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, mem_dedupF_nil]

theorem chainOK_dedupF (gens : List Tab) (idt : Tab) : ∀ (done S : List Tab),
    chainOK (dedupF [] gens) idt done S = chainOK gens idt done S
  | _, [] => rfl
  | done, x :: rest => by
    simp only [chainOK, any_dedupF, chainOK_dedupF gens idt (x :: done) rest]

@[expose] def stp (x : Tab) (acc : List Tab × List Tab) (g : Tab) : List Tab × List Tab :=
  if acc.1.contains (mulT g x) then acc else (mulT g x :: acc.1, mulT g x :: acc.2)

theorem stp_self (x g : Tab) (acc : List Tab × List Tab) : mulT g x ∈ (stp x acc g).1 := by
  by_cases h : acc.1.contains (mulT g x) = true
  · simp only [stp, h, ↓reduceIte]
    exact List.contains_iff_mem.1 h
  · simp only [stp, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons, true_or]

theorem stp_mono (x g : Tab) (acc : List Tab × List Tab) {y : Tab} (hy : y ∈ acc.1) :
    y ∈ (stp x acc g).1 := by
  by_cases h : acc.1.contains (mulT g x) = true
  · simp only [stp, h, ↓reduceIte]
    exact hy
  · simp only [stp, h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
    exact Or.inr hy

theorem stp_of_mem (x g : Tab) (acc : List Tab × List Tab) (h : mulT g x ∈ acc.1) :
    stp x acc g = acc := by
  simp only [stp, List.contains_iff_mem.2 h, ↓reduceIte]

theorem foldl_stp_dedupF (x : Tab) : ∀ (l seen : List Tab) (acc : List Tab × List Tab),
    (∀ g ∈ seen, mulT g x ∈ acc.1) →
      (dedupF seen l).foldl (stp x) acc = l.foldl (stp x) acc
  | [], _, _, _ => rfl
  | y :: ys, seen, acc, h => by
    by_cases hy : seen.contains y = true
    · simp only [dedupF, hy, ↓reduceIte, List.foldl_cons,
        stp_of_mem x y acc (h y (List.contains_iff_mem.1 hy))]
      exact foldl_stp_dedupF x ys seen acc h
    · simp only [dedupF, hy, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
      refine foldl_stp_dedupF x ys (y :: seen) (stp x acc y) ?_
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact stp_self x g acc
      · exact stp_mono x y acc (h g hg)

theorem bfsStep_eq (gens : List Tab) (st : List Tab × List Tab) (x : Tab) :
    bfsStep gens st x = gens.foldl (stp x) st := rfl

theorem bfsStep_dedupF (gens : List Tab) : bfsStep (dedupF [] gens) = bfsStep gens := by
  funext st x
  rw [bfsStep_eq, bfsStep_eq]
  exact foldl_stp_dedupF x gens [] st (by simp)

theorem bfs_dedupF (gens : List Tab) : ∀ (fuel : ℕ) (seen frontier : List Tab),
    bfs (dedupF [] gens) fuel seen frontier = bfs gens fuel seen frontier
  | 0, _, _ => rfl
  | f + 1, seen, frontier => by
    simp only [bfs, bfsStep_dedupF, bfs_dedupF gens f]

theorem closeT_dedupF (n : ℕ) (gens : List Tab) : closeT n (dedupF [] gens) = closeT n gens := by
  simp only [closeT, bfs_dedupF]

theorem chkGenTabs_dedupF (n : ℕ) (gens : List Tab) :
    chkGenTabs n (dedupF [] gens) = chkGenTabs n gens := by
  simp only [chkGenTabs, closeT_dedupF, all_dedupF, chainOK_dedupF]

theorem closeTK_eq (n : ℕ) (gens : List Tab) : closeTK n gens = closeT n gens :=
  closeT_dedupF n gens

theorem chkGenTabsK_eq (n : ℕ) (gens : List Tab) : chkGenTabsK n gens = chkGenTabs n gens :=
  chkGenTabs_dedupF n gens

theorem exists_subOfMask {α : Type} {S l : List α} (h : S.Sublist l) :
    ∃ m < 2 ^ l.length, subOfMask l m = S := by
  induction h with
  | slnil => exact ⟨0, by simp, rfl⟩
  | cons a _ ih =>
    obtain ⟨m, hm, hS⟩ := ih
    refine ⟨2 * m, ?_, ?_⟩
    · rw [List.length_cons, pow_succ]
      omega
    · have h1 : ¬ (2 * m % 2 = 1) := by omega
      have h2 : 2 * m / 2 = m := by omega
      simp only [subOfMask, h1, ↓reduceIte, h2, hS]
  | cons_cons a _ ih =>
    obtain ⟨m, hm, hS⟩ := ih
    refine ⟨2 * m + 1, ?_, ?_⟩
    · rw [List.length_cons, pow_succ]
      omega
    · have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      simp only [subOfMask, h1, ↓reduceIte, h2, hS]

theorem subOfMask_sub {α : Type} : ∀ (l : List α) (m : ℕ) {x : α}, x ∈ subOfMask l m → x ∈ l
  | [], _, _, h => by simp [subOfMask] at h
  | y :: ys, m, x, h => by
    by_cases hm : m % 2 = 1
    · simp only [subOfMask, hm, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (subOfMask_sub ys _ h)
    · simp only [subOfMask, hm, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (subOfMask_sub ys _ h)

theorem getElem_mem_subOfMask {α : Type} : ∀ (l : List α) (m j : ℕ) (hj : j < l.length),
    m.testBit j = true → l[j] ∈ subOfMask l m
  | [], _, _, hj, _ => absurd hj (by simp)
  | y :: ys, m, 0, _, hb => by
    have hm : m % 2 = 1 := by simpa [Nat.testBit_zero] using hb
    simp [subOfMask, hm]
  | y :: ys, m, j + 1, hj, hb => by
    rw [Nat.testBit_succ] at hb
    have h1 := getElem_mem_subOfMask ys (m / 2) j (by simpa using hj) hb
    by_cases hm : m % 2 = 1
    · simp only [subOfMask, hm, ↓reduceIte, List.getElem_cons_succ, List.mem_cons]
      exact Or.inr h1
    · simp only [subOfMask, hm, ↓reduceIte, List.getElem_cons_succ]
      exact h1

theorem testBit_of_mem_subOfMask {α : Type} : ∀ (l : List α) (m j : ℕ) (hj : j < l.length),
    l.Nodup → l[j] ∈ subOfMask l m → m.testBit j = true
  | [], _, _, hj, _, _ => absurd hj (by simp)
  | y :: ys, m, 0, _, hnd, h => by
    by_cases hm : m % 2 = 1
    · simpa [Nat.testBit_zero] using hm
    · simp only [subOfMask, hm, ↓reduceIte, List.getElem_cons_zero] at h
      exact absurd (subOfMask_sub ys _ h) (List.nodup_cons.1 hnd).1
  | y :: ys, m, j + 1, hj, hnd, h => by
    rw [Nat.testBit_succ]
    have hj' : j < ys.length := by simpa using hj
    apply testBit_of_mem_subOfMask ys (m / 2) j hj' (List.nodup_cons.1 hnd).2
    by_cases hm : m % 2 = 1
    · simp only [subOfMask, hm, ↓reduceIte, List.getElem_cons_succ, List.mem_cons] at h
      rcases h with h | h
      · have : y ∈ ys := by
          rw [← h]
          exact List.getElem_mem hj'
        exact absurd this (List.nodup_cons.1 hnd).1
      · exact h
    · simp only [subOfMask, hm, ↓reduceIte, List.getElem_cons_succ] at h
      exact h

theorem lookup_map_self (f : List Tab → List (List Tab)) : ∀ (l : List (List Tab)) (K : List Tab),
    K ∈ l → (l.map fun K => (K, f K)).lookup K = some (f K)
  | [], _, h => absurd h (by simp)
  | a :: as, K, h => by
    by_cases hK : K = a
    · subst hK
      simp [List.lookup]
    · have hb : (K == a) = false := by simpa using hK
      simp only [List.map_cons, List.lookup, hb]
      exact lookup_map_self f as K ((List.mem_cons.1 h).resolve_left hK)

theorem mem_nbIdxF {len : ℕ} {e : ℕ → ℕ → Bool} {i j : ℕ} (h : j ∈ (nbIdxF len e).getD i []) :
    i < len ∧ j < len ∧ e i j = true := by
  by_cases hi : i < len
  · have h1 : (nbIdxF len e).getD i [] = (List.range len).filter (e i) := by
      simp [nbIdxF, hi, List.getD_eq_getElem?_getD]
    rw [h1, List.mem_filter, List.mem_range] at h
    exact ⟨hi, h⟩
  · have h1 : (nbIdxF len e).getD i [] = [] := by
      simp [nbIdxF, hi, List.getD_eq_getElem?_getD]
    rw [h1] at h
    simp at h

theorem stableIdx_of_stableB (offs : List (List Tab)) (nb : List Tab → List (List Tab))
    (e : ℕ → ℕ → Bool)
    (he : ∀ i j (hi : i < offs.length) (hj : j < offs.length), e i j = true → offs[j] ∈ nb offs[i])
    (hnd : offs.Nodup) (m : ℕ)
    (h : stableB (offs.map fun K => (K, nb K)) (subOfMask offs m) = true) :
    stableIdx (nbIdxF offs.length e) m = true := by
  unfold stableIdx
  unfold stableB at h
  rw [List.all_eq_true] at h ⊢
  intro i _
  cases hb : m.testBit i
  · rfl
  · simp only [Bool.not_true, Bool.false_or, List.all_eq_true]
    intro j hj
    obtain ⟨hi', hj', hc⟩ := mem_nbIdxF hj
    have h1 := h _ (getElem_mem_subOfMask offs m i hi' hb)
    rw [lookup_map_self nb offs _ (List.getElem_mem hi'), Option.getD_some, List.all_eq_true] at h1
    exact testBit_of_mem_subOfMask offs m j hj' hnd
      (List.contains_iff_mem.1 (h1 _ (he i j hi' hj' hc)))

theorem edgeW_sound (X : List Tab) (n : ℕ) (k : Mod) (offs : List (List Tab))
    (W : List (ℕ × ℕ × Tab)) (i j : ℕ) (hi : i < offs.length) (hj : j < offs.length)
    (h : edgeW X n k offs W i j = true) : offs[j] ∈ nbrK n k X offs offs[i] := by
  unfold edgeW at h
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  unfold nbrK
  rw [List.mem_filter]
  refine ⟨List.getElem_mem hj, ?_⟩
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inr h
  · left
    obtain ⟨w, -, hw⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true] at hw
    obtain ⟨⟨-, hX⟩, hc⟩ := hw
    exact List.any_eq_true.2 ⟨w.2.2, List.contains_iff_mem.1 hX, hc⟩

theorem HlX_eq (n : ℕ) (b : Bool) : HlX (allTabs n) b = Hl n b := rfl

theorem flagOKX_eq (n : ℕ) (k : Mod) (b : Bool) : flagOKX (allTabs n) n k b = flagOK n k b := rfl

theorem H1tabX_eq (n : ℕ) (k : Mod) (b : Bool) : H1tabX (allTabs n) n k b = H1tab n k b := rfl

theorem H2tabX_eq (n : ℕ) (k : Mod) (b : Bool) : H2tabX (allTabs n) n k b = H2tab n k b := rfl

theorem fourDX_eq (k : Mod) (b : Bool) : fourDX (allTabs 6) k b = fourD k b := by
  simp only [fourDX, fourD, H1tabX_eq, H2tabX_eq, closeTK_eq, commSub]

theorem jOfK_eq (n : ℕ) (B : List Tab) (S : List (List Tab)) : jOfK n B S = jOf n B S :=
  closeTK_eq _ _

theorem jOKK_eq (n : ℕ) (B : List Tab) (S : List (List Tab)) : jOKK n B S = jOK n B S :=
  chkGenTabsK_eq _ _

theorem claimsGK_eq (k : Mod) (d : FourD) (S : List (List Tab)) : claimsGK k d S = claimsG k d S := by
  simp only [claimsGK, claimsG, jOfK_eq, jOKK_eq, chkGenTabsK_eq, closeTK_eq, commSub]

theorem claimsLK_eq (d : FourD) (S : List (List Tab)) : claimsLK d S = claimsL d S := by
  simp only [claimsLK, claimsL, jOfK_eq, jOKK_eq]

theorem chkStruct6X_eq (k : Mod) (b : Bool) (e : ℕ) :
    chkStruct6X (allTabs 6) k b e = chkStruct6 k b e := by
  simp only [chkStruct6X, chkStruct6, fourDX_eq, flagOKX_eq, HlX_eq]

theorem chkGenG6X_eq (k : Mod) : chkGenG6X (allTabs 6) k = chkGenG6 k := by
  simp only [chkGenG6X, chkGenG6, fourDX_eq, chkGenTabsK_eq]

theorem chkWitG6X_eq (k : Mod) : chkWitG6X (allTabs 6) k = chkWitG6 k := by
  simp only [chkWitG6X, chkWitG6, fourDX_eq, HlX_eq]

theorem chkRG6X_eq (k : Mod) : chkRG6X (allTabs 6) k = chkRG6 k := by
  simp only [chkRG6X, chkRG6, fourDX_eq]

theorem chkRL6X_eq (k : Mod) : chkRL6X (allTabs 6) k = chkRL6 k := by
  simp only [chkRL6X, chkRL6, fourDX_eq]

theorem chkSubG6_of_X (k : Mod) (W : List (ℕ × ℕ × Tab)) (h : chkSubG6X (allTabs 6) W k = true) :
    chkSubG6 k = true := by
  simp only [chkSubG6X, fourDX_eq, claimsGK_eq, HlX_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hnd, h⟩ := h
  simp only [chkSubG6, List.all_eq_true, List.mem_filter, List.mem_sublists]
  rintro S ⟨hS, hst⟩
  obtain ⟨m, hm, rfl⟩ := exists_subOfMask hS
  have hI := stableIdx_of_stableB _ (nbrK 6 k (Hl 6 true) (offsH 6 k true))
    (edgeW (Hl 6 true) 6 k (offsH 6 k true) W) (edgeW_sound _ _ _ _ _) hnd m hst
  have h1 := h m hm
  simp only [hI, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem chkSubL6_of_X (k : Mod) (h : chkSubL6X (allTabs 6) k = true) : chkSubL6 k = true := by
  simp only [chkSubL6X, fourDX_eq, claimsLK_eq, HlX_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨hnd, h⟩ := h
  simp only [chkSubL6, List.all_eq_true, List.mem_filter, List.mem_sublists]
  rintro S ⟨hS, hst⟩
  obtain ⟨m, hm, rfl⟩ := exists_subOfMask hS
  have he : ∀ i j (hi : i < (offsH 6 k false).length) (hj : j < (offsH 6 k false).length),
      (nbrK 6 k (Hl 6 false) (offsH 6 k false) ((offsH 6 k false).getD i [])).contains
        ((offsH 6 k false).getD j []) = true →
      (offsH 6 k false)[j] ∈ nbrK 6 k (Hl 6 false) (offsH 6 k false) (offsH 6 k false)[i] := by
    intro i j hi hj hc
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hc
    exact List.contains_iff_mem.1 hc
  have hI := stableIdx_of_stableB _ (nbrK 6 k (Hl 6 false) (offsH 6 k false)) _ he hnd m hst
  have h1 := h m hm
  simp only [hI, Bool.not_true, Bool.false_or] at h1
  exact h1

theorem chkG6_of_parts (k : Mod) (h1 : chkStruct6X sym6K k true 4 = true)
    (h2 : chkGenG6X sym6K k = true) (h3 : chkSubG6X sym6K wG6 k = true)
    (h4 : chkWitG6X sym6K k = true) (h5 : chkRG6X sym6K k = true) : chkG6 k = true := by
  rw [sym6K_eq] at h1 h2 h3 h4 h5
  rw [chkStruct6X_eq] at h1
  rw [chkGenG6X_eq] at h2
  rw [chkWitG6X_eq] at h4
  rw [chkRG6X_eq] at h5
  simp [chkG6, h1, h2, chkSubG6_of_X k wG6 h3, h4, h5]

theorem chkL6_of_parts (k : Mod) (h1 : chkStruct6X sym6K k false 3 = true)
    (h2 : chkSubL6X sym6K k = true) (h3 : chkRL6X sym6K k = true) : chkL6 k = true := by
  rw [sym6K_eq] at h1 h2 h3
  rw [chkStruct6X_eq] at h1
  rw [chkRL6X_eq] at h3
  simp [chkL6, h1, chkSubL6_of_X k h2, h3]

end CFSG.KC.B3Six
