module

public import Certificates.Data.CFSGNative.CosetTable.EnumC

public section

namespace CFSG.CosetTable

theorem get!_eq_getD (b : ByteArray) (p : Nat) : b.get! p = b.data.getD p 0 := by
  cases b with
  | mk d => simp only [ByteArray.get!, Array.getElem!_eq_getD]; rfl

theorem data_set! (b : ByteArray) (m : Nat) (x : UInt8) :
    (b.set! m x).data = b.data.set! m x := rfl

theorem get!_set! (b : ByteArray) (m p : Nat) (x : UInt8) :
    (b.set! m x).get! p = if m = p ∧ m < b.size then x else b.get! p := by
  rw [get!_eq_getD, get!_eq_getD, data_set!, Array.set!_eq_setIfInBounds,
    Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : m = p
  · subst h1
    by_cases h2 : m < b.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem get!_set!_ne (b : ByteArray) {m p : Nat} (x : UInt8) (h : m ≠ p) :
    (b.set! m x).get! p = b.get! p := by
  rw [get!_set!]
  simp [h]

theorem size_setWord (b : ByteArray) (i v : Nat) : (setWord b i v).size = b.size := by
  unfold setWord
  split <;> simp

theorem getWord_of_ge {b : ByteArray} {i : Nat} (h : b.size / 4 ≤ i) : getWord b i = 0 := by
  unfold getWord
  have : ¬ (i * 4 + 4 ≤ b.size) := by omega
  simp only [this, ↓reduceIte]

theorem getWord_lt (b : ByteArray) (i : Nat) : getWord b i < 2 ^ 32 := by
  unfold getWord
  split
  · have h0 := UInt8.toNat_lt (b.get! (i * 4))
    have h1 := UInt8.toNat_lt (b.get! (i * 4 + 1))
    have h2 := UInt8.toNat_lt (b.get! (i * 4 + 2))
    have h3 := UInt8.toNat_lt (b.get! (i * 4 + 3))
    omega
  · simp

theorem getWord_setWord (b : ByteArray) (i v j : Nat) :
    getWord (setWord b i v) j = if i = j ∧ i < b.size / 4 then v % 2 ^ 32 else getWord b j := by
  unfold setWord
  by_cases hi : i * 4 + 4 ≤ b.size
  · simp only [hi, ↓reduceIte]
    by_cases hij : i = j
    · subst hij
      have h0 : i * 4 < b.size := by omega
      have h1 : i * 4 + 1 < b.size := by omega
      have h2 : i * 4 + 2 < b.size := by omega
      have h3 : i * 4 + 3 < b.size := by omega
      have h4 : i < b.size / 4 := by omega
      simp only [getWord, ByteArray.size_set!, get!_set!]
      simp [h0, h1, h2, h3, h4, hi]
      omega
    · have h4 : ¬ (i = j ∧ i < b.size / 4) := fun h => hij h.1
      simp only [getWord, ByteArray.size_set!, h4, ↓reduceIte]
      simp (disch := omega) only [get!_set!_ne]
  · simp only [hi, ↓reduceIte]
    have h4 : ¬ (i = j ∧ i < b.size / 4) := fun h => hi (by omega)
    simp only [h4, ↓reduceIte]


@[expose] def wordsToArray (b : ByteArray) : Array Nat :=
  (Array.range (b.size / 4)).map (getWord b)

@[expose] def linksToArray (b : ByteArray) : Array Nat :=
  (Array.range (b.size / 4)).map (getLink b)

theorem size_wordsToArray (b : ByteArray) : (wordsToArray b).size = b.size / 4 := by
  simp [wordsToArray]

theorem size_linksToArray (b : ByteArray) : (linksToArray b).size = b.size / 4 := by
  simp [linksToArray]

theorem getD_wordsToArray (b : ByteArray) (i : Nat) :
    (wordsToArray b).getD i 0 = getWord b i := by
  rw [Array.getD_eq_getD_getElem?]
  simp only [wordsToArray, Array.getElem?_map, Array.getElem?_range]
  by_cases h : i < b.size / 4
  · simp [h]
  · simp [h, getWord_of_ge (by omega : b.size / 4 ≤ i)]

theorem getLink_of_ge {b : ByteArray} {c : Nat} (h : b.size / 4 ≤ c) : getLink b c = c := by
  simp [getLink, getWord_of_ge h]

theorem getD_linksToArray (b : ByteArray) (c : Nat) :
    (linksToArray b).getD c c = getLink b c := by
  rw [Array.getD_eq_getD_getElem?]
  simp only [linksToArray, Array.getElem?_map, Array.getElem?_range]
  by_cases h : c < b.size / 4
  · simp [h]
  · simp [h, getLink_of_ge (by omega : b.size / 4 ≤ c)]

theorem wordsToArray_setWord (b : ByteArray) {i v : Nat} (hv : v < 2 ^ 32) :
    wordsToArray (setWord b i v) = (wordsToArray b).set! i v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp only [wordsToArray, size_setWord, Array.getElem?_map, Array.getElem?_range,
    Array.size_map, Array.size_range]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < b.size / 4
    · simp [h2, getWord_setWord, Nat.mod_eq_of_lt hv]
    · simp [h2]
  · simp [h1, getWord_setWord]

theorem getLink_lt (b : ByteArray) {c : Nat} (hc : c < 2 ^ 32) : getLink b c < 2 ^ 32 :=
  Nat.xor_lt_two_pow (getWord_lt b c) hc

theorem getLink_setLink (b : ByteArray) {c v : Nat} (hc : c < 2 ^ 32) (hv : v < 2 ^ 32)
    (j : Nat) :
    getLink (setLink b c v) j = if c = j ∧ c < b.size / 4 then v else getLink b j := by
  unfold getLink setLink
  rw [getWord_setWord]
  by_cases h : c = j ∧ c < b.size / 4
  · have h' := h
    obtain ⟨rfl, -⟩ := h'
    simp only [h, and_self, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hv hc), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp [h]


theorem linksToArray_setLink (b : ByteArray) {c v : Nat} (hc : c < 2 ^ 32) (hv : v < 2 ^ 32) :
    linksToArray (setLink b c v) = (linksToArray b).set! c v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have hs : (setLink b c v).size = b.size := size_setWord _ _ _
  simp only [linksToArray, hs, Array.getElem?_map, Array.getElem?_range, Array.size_map,
    Array.size_range]
  by_cases h1 : c = j
  · subst h1
    by_cases h2 : c < b.size / 4
    · simp [h2, getLink_setLink b hc hv]
    · simp [h2]
  · simp [h1, getLink_setLink b hc hv]

theorem get!_of_ge {b : ByteArray} {p : Nat} (h : b.size ≤ p) : b.get! p = 0 := by
  rw [get!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using h)]
  rfl

theorem get!_push (b : ByteArray) (x : UInt8) (p : Nat) :
    (b.push x).get! p = if p = b.size then x else b.get! p := by
  rw [get!_eq_getD, get!_eq_getD, ByteArray.data_push, Array.getD_eq_getD_getElem?,
    Array.getD_eq_getD_getElem?, Array.getElem?_push]
  simp only [ByteArray.size_data]
  by_cases h : p = b.size <;> simp [h]

theorem size_zeroBytes (k : Nat) : ∀ b : ByteArray, (zeroBytes k b).size = b.size + k := by
  induction k with
  | zero => intro b; rfl
  | succ k ih => intro b; simp only [zeroBytes, ih, ByteArray.size_push]; omega

theorem get!_zeroBytes (k : Nat) :
    ∀ (b : ByteArray) (p : Nat), (zeroBytes k b).get! p = if p < b.size then b.get! p else 0 := by
  induction k with
  | zero =>
    intro b p
    by_cases h : p < b.size
    · simp [zeroBytes, h]
    · simp [zeroBytes, h, get!_of_ge (by omega : b.size ≤ p)]
  | succ k ih =>
    intro b p
    simp only [zeroBytes, ih, ByteArray.size_push, get!_push]
    by_cases h : p < b.size
    · simp [h, Nat.ne_of_lt h, show p < b.size + 1 by omega]
    · by_cases h' : p = b.size
      · simp [h']
      · simp [h, show ¬ p < b.size + 1 by omega]

theorem size_emptyWithCapacity (c : Nat) : (ByteArray.emptyWithCapacity c).size = 0 := rfl

theorem size_zeroWords (n : Nat) : (zeroWords n).size = 4 * n := by
  simp only [zeroWords, size_zeroBytes, size_emptyWithCapacity, Nat.zero_add]

theorem get!_zeroWords (n p : Nat) : (zeroWords n).get! p = 0 := by
  simp only [zeroWords, get!_zeroBytes, size_emptyWithCapacity]
  simp

theorem getWord_zeroWords (n i : Nat) : getWord (zeroWords n) i = 0 := by
  simp [getWord, get!_zeroWords]

theorem getLink_zeroWords (n c : Nat) : getLink (zeroWords n) c = c := by
  simp [getLink, getWord_zeroWords]

theorem wordsToArray_zeroWords (n : Nat) : wordsToArray (zeroWords n) = Array.replicate n 0 := by
  apply Array.ext_getElem?
  intro j
  simp [wordsToArray, size_zeroWords, getWord_zeroWords, Array.getElem?_replicate,
    Array.getElem?_range]

theorem linksToArray_zeroWords (n : Nat) : linksToArray (zeroWords n) = Array.range n := by
  apply Array.ext_getElem?
  intro j
  simp [linksToArray, size_zeroWords, getLink_zeroWords, Array.getElem?_range]

@[expose, reducible] def StC.toSt (s : StC) : St where
  tab := wordsToArray s.tab
  fwd := linksToArray s.fwd
  par := wordsToArray s.par
  next := s.next
  ded := s.ded
  queue := s.queue
  qi := s.qi
  overflow := s.overflow

structure Fits (L cap : Nat) (st : St) : Prop where
  size_le : (cap + 2) * (L + 1) ≤ 2 ^ 32
  next_le : st.next ≤ cap + 2
  par_size : st.par.size = cap + 1
  queue_lt : ∀ g ∈ st.queue, g < st.next

theorem Fits.of_fields {L cap : Nat} {st st' : St} (h : Fits L cap st) (hn : st'.next = st.next)
    (hp : st'.par.size = st.par.size) (hq : st'.queue = st.queue) : Fits L cap st' :=
  ⟨h.size_le, hn ▸ h.next_le, hp ▸ h.par_size, hq ▸ hn ▸ h.queue_lt⟩

theorem Fits.next_lt {L cap : Nat} {st : St} (h : Fits L cap st) : st.next ≤ 2 ^ 32 := by
  have := h.size_le
  have h1 := h.next_le
  have : cap + 2 ≤ (cap + 2) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem Fits.queue_lt32 {L cap : Nat} {st : St} (h : Fits L cap st) :
    ∀ g ∈ st.queue, g < 2 ^ 32 := by
  intro g hg
  have := h.queue_lt g hg
  have := h.next_lt
  omega

theorem merge_fits {L cap : Nat} {st : St} (h : Fits L cap st) (a b : Nat) :
    Fits L cap (merge st a b) := by
  unfold merge
  dsimp only
  split
  · exact h
  · rename_i hg
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hg
    obtain ⟨⟨hab, ha⟩, hb⟩ := hg
    split
    · refine ⟨h.size_le, h.next_le, h.par_size, ?_⟩
      intro g hg
      rcases Array.mem_push.mp hg with hg | rfl
      · exact h.queue_lt g hg
      · exact hb
    · refine ⟨h.size_le, h.next_le, h.par_size, ?_⟩
      intro g hg
      rcases Array.mem_push.mp hg with hg | rfl
      · exact h.queue_lt g hg
      · exact ha

theorem Fits.ite {L cap : Nat} {c : Bool} {a b : St} (ha : Fits L cap a) (hb : Fits L cap b) :
    Fits L cap (if c then a else b) := by
  split <;> assumption

@[expose] def coincTransfer (P : Params) (st : St) (g x d : Nat) : St :=
  let ix := P.inv.getD x 0
  let mu := find st.fwd st.next g
  let nu := find st.fwd st.next d
  let e := st.tab.getD (mu * P.L + x) 0
  if e != 0 then merge st nu e
  else
    let e' := st.tab.getD (nu * P.L + ix) 0
    if e' != 0 then merge st mu e'
    else { st with tab := (st.tab.set! (mu * P.L + x) nu).set! (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincClear (P : Params) (st : St) (g x d : Nat) : St :=
  coincTransfer P (if st.tab.getD (d * P.L + P.inv.getD x 0) 0 == g then
      { st with tab := st.tab.set! (d * P.L + P.inv.getD x 0) 0 } else st) g x d

theorem coincLetter_eq (P : Params) (st : St) (g x : Nat) :
    coincLetter P st g x =
      if st.tab.getD (g * P.L + x) 0 == 0 then st
      else coincClear P st g x (st.tab.getD (g * P.L + x) 0) := rfl

theorem coincTransfer_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params)
    (g x d : Nat) :
    Fits L cap (coincTransfer P st g x d) := by
  unfold coincTransfer
  dsimp only
  split
  · exact merge_fits h _ _
  · split
    · exact merge_fits h _ _
    · exact h.of_fields rfl rfl rfl

theorem coincClear_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params)
    (g x d : Nat) :
    Fits L cap (coincClear P st g x d) := by
  unfold coincClear
  apply coincTransfer_fits
  apply Fits.ite
  · exact h.of_fields rfl rfl rfl
  · exact h

theorem coincLetter_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params) (g x : Nat) :
    Fits L cap (coincLetter P st g x) := by
  rw [coincLetter_eq]
  split
  · exact h
  · exact coincClear_fits h P g x _

theorem coincRow_fits {L cap : Nat} (P : Params) (g : Nat) :
    ∀ (n : Nat) {st : St}, Fits L cap st → Fits L cap (coincRow P g n st) := by
  intro n
  induction n with
  | zero => intro st h; exact h
  | succ n ih => intro st h; exact ih (coincLetter_fits h P g _)

theorem coincQueue_fits {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {st : St}, Fits L cap st → Fits L cap (coincQueue P fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold coincQueue
    split
    · exact ih (coincRow_fits P _ _ (h.of_fields rfl rfl rfl))
    · exact ⟨h.size_le, h.next_le, h.par_size, by simp⟩

theorem coincidence_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params) (a b : Nat) :
    Fits L cap (coincidence P st a b) :=
  coincQueue_fits P _ (merge_fits h a b)

theorem deduce_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params) (f x b : Nat) :
    Fits L cap (deduce P st f x b) := by
  unfold deduce
  split
  · exact h.of_fields rfl rfl rfl
  · exact h

theorem define_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params) (a x : Nat) :
    Fits L cap (define P st a x) := by
  unfold define
  dsimp only
  split
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨-, -⟩, -⟩, hb⟩ := hg
    refine ⟨h.size_le, ?_, ?_, ?_⟩
    · show st.next + 1 ≤ cap + 2
      have := h.par_size
      omega
    · show (st.par.set! _ _).size = cap + 1
      rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      exact h.par_size
    · intro g hg
      have := h.queue_lt g hg
      show g < st.next + 1
      omega
  · exact h.of_fields rfl rfl rfl

theorem scan_fits {L cap : Nat} {st : St} (h : Fits L cap st) (P : Params) (a : Nat)
    (w w' : List Nat) :
    Fits L cap (scan P st a w w') := by
  unfold scan
  split
  · exact h
  · exact coincidence_fits h P _ _
  · exact deduce_fits h P _ _ _
  · exact h

theorem scanAll_fits {L cap : Nat} (P : Params) (a : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {st : St}, Fits L cap st →
      Fits L cap (scanAll P a ps st) := by
  intro ps
  induction ps with
  | nil => intro st h; exact h
  | cons p ps ih =>
    intro st h
    unfold scanAll
    split
    · exact ih (scan_fits h P _ _ _)
    · exact h

theorem processDed_fits {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {st : St}, Fits L cap st → Fits L cap (processDed P fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold processDed
    split
    · exact h
    · dsimp only
      split
      · exact ih (scanAll_fits P _ _ (h.of_fields rfl rfl rfl))
      · exact ih (h.of_fields rfl rfl rfl)

theorem fillWord_fits {L cap : Nat} (P : Params) (w w' : List Nat) :
    ∀ (fuel : Nat) {st : St}, Fits L cap st → Fits L cap (fillWord P w w' fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold fillWord
    split
    · exact h
    · exact coincidence_fits h P _ _
    · exact deduce_fits h P _ _ _
    · dsimp only
      split
      · exact define_fits h P _ _
      · exact ih (define_fits h P _ _)

theorem fillSubs_fits {L cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {st : St}, Fits L cap st →
      Fits L cap (fillSubs P fuel ps st) := by
  intro ps
  induction ps with
  | nil => intro st h; exact h
  | cons p ps ih =>
    intro st h
    exact ih (processDed_fits P fuel (fillWord_fits P _ _ _ h))

theorem fillRow_fits {L cap : Nat} (P : Params) (fuel c : Nat) :
    ∀ (n : Nat) {st : St}, Fits L cap st → Fits L cap (fillRow P fuel c n st) := by
  intro n
  induction n with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold fillRow
    split
    · exact h
    · dsimp only
      split
      · exact ih (processDed_fits P fuel (define_fits h P _ _))
      · exact ih h

theorem felsch_fits {L cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (n c : Nat) {st : St}, Fits L cap st → Fits L cap (felsch P fuel n c st) := by
  intro n
  induction n with
  | zero => intro c st h; exact h
  | succ n ih =>
    intro c st h
    unfold felsch
    split
    · exact ih _ (fillRow_fits P fuel c _ h)
    · exact h

theorem hltWord_fits {L cap : Nat} (P : Params) (c : Nat) (w w' : List Nat) :
    ∀ (fuel : Nat) {st : St}, Fits L cap st → Fits L cap (hltWord P c w w' fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ n ih =>
    intro st h
    unfold hltWord
    split
    · exact h
    · split
      · exact h
      · exact coincidence_fits h P _ _
      · exact deduce_fits h P _ _ _
      · dsimp only
        split
        · exact define_fits h P _ _
        · exact ih (define_fits h P _ _)

theorem hltRow_fits {L cap : Nat} (P : Params) (fuel c : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {st : St}, Fits L cap st →
      Fits L cap (hltRow P fuel c ps st) := by
  intro ps
  induction ps with
  | nil => intro st h; exact h
  | cons p ps ih =>
    intro st h
    unfold hltRow
    split
    · exact h
    · exact ih (processDed_fits P fuel (hltWord_fits P c p.1 p.2 _ h))

theorem hlt_fits {L cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (n c : Nat) {st : St}, Fits L cap st → Fits L cap (hlt P fuel n c st) := by
  intro n
  induction n with
  | zero => intro c st h; exact h
  | succ n ih =>
    intro c st h
    unfold hlt
    split
    · exact ih _ (hltRow_fits P fuel c _ h)
    · exact h

theorem init_fits (L cap : Nat) (h : (cap + 2) * (L + 1) ≤ 2 ^ 32) : Fits L cap (St.init L cap) :=
  ⟨h, by simp [St.init], by simp [St.init], by simp [St.init]⟩

theorem walkC_eq (L : Nat) (tab : ByteArray) :
    ∀ (w : List Nat) (lim k c : Nat),
      walkC L tab lim k c w = walk L (wordsToArray tab) lim k c w := by
  intro w
  induction w with
  | nil => intro lim k c; cases lim <;> rfl
  | cons x w ih =>
    intro lim k c
    cases lim with
    | zero => rfl
    | succ lim => simp only [walkC, walk, getD_wordsToArray, ih]

theorem findC_eq (fwd : ByteArray) :
    ∀ (fuel c : Nat), findC fwd fuel c = find (linksToArray fwd) fuel c := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ n ih => intro c; simp only [findC, find, getD_linksToArray, ih]

theorem findC_lt (fwd : ByteArray) :
    ∀ (fuel c : Nat), c < 2 ^ 32 → findC fwd fuel c < 2 ^ 32 := by
  intro fuel
  induction fuel with
  | zero => intro c hc; exact hc
  | succ n ih =>
    intro c hc
    simp only [findC]
    split
    · exact hc
    · exact ih _ (getLink_lt fwd hc)

theorem scanWordC_eq (L : Nat) (tab : ByteArray) (a : Nat) (w w' : List Nat) :
    scanWordC L tab a w w' = scanWord L (wordsToArray tab) a w w' := by
  simp only [scanWordC, scanWord, walkC_eq]


theorem mergeC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (a b : Nat) :
    (mergeC s a b).toSt = merge s.toSt a b := by
  have hn : s.next ≤ 2 ^ 32 := h.next_lt
  simp only [mergeC, merge, findC_eq]
  obtain ⟨ra, hra⟩ : ∃ ra, find (linksToArray s.fwd) s.next a = ra := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ rb, find (linksToArray s.fwd) s.next b = rb := ⟨_, rfl⟩
  simp only [hra, hrb]
  by_cases hc : (ra == rb || decide (s.next ≤ ra) || decide (s.next ≤ rb)) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hc
    have ha : ra < 2 ^ 32 := by omega
    have hb : rb < 2 ^ 32 := by omega
    by_cases hr : ra < rb
    · simp only [hr, ↓reduceIte, StC.toSt, linksToArray_setLink _ hb ha]
    · simp only [hr, ↓reduceIte, StC.toSt, linksToArray_setLink _ ha hb]

@[expose] def coincTransferC (P : Params) (st : StC) (g x d : Nat) : StC :=
  let ix := P.inv.getD x 0
  let mu := findC st.fwd st.next g
  let nu := findC st.fwd st.next d
  let e := getWord st.tab (mu * P.L + x)
  if e != 0 then mergeC st nu e
  else
    let e' := getWord st.tab (nu * P.L + ix)
    if e' != 0 then mergeC st mu e'
    else { st with tab := setWord (setWord st.tab (mu * P.L + x) nu) (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincClearC (P : Params) (st : StC) (g x d : Nat) : StC :=
  coincTransferC P (if getWord st.tab (d * P.L + P.inv.getD x 0) == g then
      { st with tab := setWord st.tab (d * P.L + P.inv.getD x 0) 0 } else st) g x d

theorem coincLetterC_eq (P : Params) (st : StC) (g x : Nat) :
    coincLetterC P st g x =
      if getWord st.tab (g * P.L + x) == 0 then st
      else coincClearC P st g x (getWord st.tab (g * P.L + x)) := rfl

theorem coincTransferC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params)
    (g x d : Nat) (hg : g < 2 ^ 32) (hd : d < 2 ^ 32) :
    (coincTransferC P s g x d).toSt = coincTransfer P s.toSt g x d := by
  unfold coincTransferC coincTransfer
  dsimp only
  simp only [findC_eq, getD_wordsToArray]
  obtain ⟨mu, hmu⟩ : ∃ mu, find (linksToArray s.fwd) s.next g = mu := ⟨_, rfl⟩
  obtain ⟨nu, hnu⟩ : ∃ nu, find (linksToArray s.fwd) s.next d = nu := ⟨_, rfl⟩
  have hmu32 : mu < 2 ^ 32 := by rw [← hmu, ← findC_eq]; exact findC_lt _ _ _ hg
  have hnu32 : nu < 2 ^ 32 := by rw [← hnu, ← findC_eq]; exact findC_lt _ _ _ hd
  simp only [hmu, hnu]
  obtain ⟨e, he⟩ : ∃ e, getWord s.tab (mu * P.L + x) = e := ⟨_, rfl⟩
  simp only [he]
  by_cases hne : (e != 0) = true
  · simp only [hne, ↓reduceIte]
    exact mergeC_toSt h _ _
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e', he'⟩ : ∃ e', getWord s.tab (nu * P.L + P.inv.getD x 0) = e' := ⟨_, rfl⟩
    simp only [he']
    by_cases hne' : (e' != 0) = true
    · simp only [hne', ↓reduceIte]
      exact mergeC_toSt h _ _
    · simp only [hne', Bool.false_eq_true, ↓reduceIte]
      simp only [StC.toSt, wordsToArray_setWord _ hnu32, wordsToArray_setWord _ hmu32]

theorem coincClearC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params)
    (g x d : Nat) (hg : g < 2 ^ 32) (hd : d < 2 ^ 32) :
    (coincClearC P s g x d).toSt = coincClear P s.toSt g x d := by
  unfold coincClearC coincClear
  simp only [getD_wordsToArray]
  by_cases hc : (getWord s.tab (d * P.L + P.inv.getD x 0) == g) = true
  · simp only [hc, ↓reduceIte]
    have hs : ({ s with tab := setWord s.tab (d * P.L + P.inv.getD x 0) 0 } : StC).toSt =
        { s.toSt with tab := s.toSt.tab.set! (d * P.L + P.inv.getD x 0) 0 } := by
      simp only [StC.toSt, wordsToArray_setWord _ (by decide : 0 < 2 ^ 32)]
    have h1 : Fits L cap
        ({ s with tab := setWord s.tab (d * P.L + P.inv.getD x 0) 0 } : StC).toSt :=
      h.of_fields rfl rfl rfl
    rw [coincTransferC_toSt h1 P g x d hg hd, hs]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact coincTransferC_toSt h P g x d hg hd

theorem coincLetterC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params)
    (g x : Nat) (hg : g < 2 ^ 32) :
    (coincLetterC P s g x).toSt = coincLetter P s.toSt g x := by
  rw [coincLetterC_eq, coincLetter_eq]
  simp only [getD_wordsToArray]
  by_cases hc : (getWord s.tab (g * P.L + x) == 0) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact coincClearC_toSt h P g x _ hg (getWord_lt _ _)

theorem coincRowC_toSt {L cap : Nat} (P : Params) (g : Nat) (hg : g < 2 ^ 32) :
    ∀ (n : Nat) {s : StC}, Fits L cap s.toSt →
      (coincRowC P g n s).toSt = coincRow P g n s.toSt := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    simp only [coincRowC, coincRow]
    rw [ih (by rw [coincLetterC_toSt h P g _ hg]; exact coincLetter_fits h P g _),
      coincLetterC_toSt h P g _ hg]

theorem coincQueueC_toSt {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {s : StC}, Fits L cap s.toSt →
      (coincQueueC P fuel s).toSt = coincQueue P fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    simp only [coincQueueC, coincQueue]
    by_cases hq : s.qi < s.queue.size
    · simp only [hq, ↓reduceIte]
      have hg : s.queue.getD s.qi 0 < 2 ^ 32 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq, Option.getD_some]
        exact h.queue_lt32 _ (Array.getElem_mem hq)
      have h1 : Fits L cap ({ s with qi := s.qi + 1 } : StC).toSt := h.of_fields rfl rfl rfl
      have h2 := coincRowC_toSt (cap := cap) P (s.queue.getD s.qi 0) hg P.L h1
      rw [ih (by rw [h2]; exact coincRow_fits P _ _ h1), h2]
    · simp only [hq, ↓reduceIte]

theorem coincidenceC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params) (a b : Nat) :
    (coincidenceC P s a b).toSt = coincidence P s.toSt a b := by
  unfold coincidenceC coincidence
  rw [coincQueueC_toSt P _ (by rw [mergeC_toSt h]; exact merge_fits h a b), mergeC_toSt h]

theorem deduceC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params) (f x b : Nat) :
    (deduceC P s f x b).toSt = deduce P s.toSt f x b := by
  have hn : s.next ≤ 2 ^ 32 := h.next_lt
  unfold deduceC deduce
  dsimp only []
  by_cases hg : (f < s.next ∧ b < s.next) ∧ x < P.L
  · obtain ⟨⟨hf, hb⟩, hx⟩ := hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, hf, hb, hx, and_self, ↓reduceIte]
    simp only [StC.toSt, wordsToArray_setWord _ (by omega : b < 2 ^ 32),
      wordsToArray_setWord _ (by omega : f < 2 ^ 32)]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, hg, ↓reduceIte]

theorem defineC_toSt {cap : Nat} {P : Params} {s : StC} (h : Fits P.L cap s.toSt) (a x : Nat) :
    (defineC P s a x).toSt = define P s.toSt a x := by
  unfold defineC define
  dsimp only []
  by_cases hg : ((0 < a ∧ a < s.next) ∧ x < P.L) ∧ s.next < s.par.size / 4
  · obtain ⟨⟨⟨h0, ha⟩, hx⟩, hb⟩ := hg
    have hpar : s.par.size / 4 = cap + 1 := by
      have := h.par_size
      simpa only [size_wordsToArray] using this
    have hsz := h.size_le
    have h1 : (a + 1) * P.L ≤ (cap + 2) * (P.L + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (a + 1) * P.L = a * P.L + P.L := by rw [Nat.add_mul, Nat.one_mul]
    have hpv : a * P.L + x < 2 ^ 32 := by omega
    have hb32 : s.next < 2 ^ 32 := by
      have : cap + 2 ≤ (cap + 2) * (P.L + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, size_wordsToArray, h0, ha, hx, hb, and_self,
      ↓reduceIte]
    simp only [StC.toSt, wordsToArray_setWord _ hb32,
      wordsToArray_setWord _ (by omega : a < 2 ^ 32), wordsToArray_setWord _ hpv]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, size_wordsToArray, hg, ↓reduceIte]

theorem scanC_toSt {L cap : Nat} {s : StC} (h : Fits L cap s.toSt) (P : Params) (a : Nat)
    (w w' : List Nat) : (scanC P s a w w').toSt = scan P s.toSt a w w' := by
  unfold scanC scan
  rw [scanWordC_eq]
  cases hr : scanWord P.L (wordsToArray s.tab) a w w' with
  | closed => rfl
  | coinc f b => exact coincidenceC_toSt h P _ _
  | deduct f x b => exact deduceC_toSt h P _ _ _
  | gap f x => rfl

theorem scanAllC_toSt {L cap : Nat} (P : Params) (a : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {s : StC}, Fits L cap s.toSt →
      (scanAllC P a ps s).toSt = scanAll P a ps s.toSt := by
  intro ps
  induction ps with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    unfold scanAllC scanAll
    simp only [getD_linksToArray]
    by_cases hc : (getLink s.fwd a == a) = true
    · simp only [hc, ↓reduceIte]
      have h1 := scanC_toSt h P a p.1 p.2
      rw [ih (by rw [h1]; exact scan_fits h P a _ _), h1]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem processDedC_toSt {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {s : StC}, Fits L cap s.toSt →
      (processDedC P fuel s).toSt = processDed P fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold processDedC processDed
    rcases hb : s.ded.back? with _ | e
    · rfl
    · simp only [getD_linksToArray]
      have h1 : Fits L cap ({ s with ded := s.ded.pop } : StC).toSt := h.of_fields rfl rfl rfl
      by_cases hc : (getLink s.fwd (e / P.L) == e / P.L) = true
      · simp only [hc, ↓reduceIte]
        have h2 := scanAllC_toSt P (e / P.L) (P.scans.getD (e % P.L) []) h1
        rw [ih (by rw [h2]; exact scanAll_fits P _ _ h1), h2]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ih h1

theorem fillWordC_toSt {cap : Nat} (P : Params) (w w' : List Nat) :
    ∀ (fuel : Nat) {s : StC}, Fits P.L cap s.toSt →
      (fillWordC P w w' fuel s).toSt = fillWord P w w' fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold fillWordC fillWord
    rw [scanWordC_eq]
    cases hr : scanWord P.L (wordsToArray s.tab) 1 w w' with
    | closed => rfl
    | coinc f b => exact coincidenceC_toSt h P _ _
    | deduct f x b => exact deduceC_toSt h P _ _ _
    | gap f x =>
      dsimp only
      have h1 := defineC_toSt h f x
      have ho : (defineC P s f x).overflow = (define P s.toSt f x).overflow :=
        congrArg St.overflow h1
      simp only [ho]
      by_cases hov : (define P s.toSt f x).overflow = true
      · simp only [hov, ↓reduceIte]
        exact h1
      · simp only [hov, Bool.false_eq_true, ↓reduceIte]
        rw [ih (by rw [h1]; exact define_fits h P _ _), h1]

theorem fillSubsC_toSt {cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {s : StC}, Fits P.L cap s.toSt →
      (fillSubsC P fuel ps s).toSt = fillSubs P fuel ps s.toSt := by
  intro ps
  induction ps with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    unfold fillSubsC fillSubs
    have h1 := fillWordC_toSt P p.1 p.2 (p.1.length + 1) h
    have h2 := processDedC_toSt P fuel
      (s := fillWordC P p.1 p.2 (p.1.length + 1) s) (by rw [h1]; exact fillWord_fits P _ _ _ h)
    rw [ih (by rw [h2, h1]; exact processDed_fits P _ (fillWord_fits P _ _ _ h)), h2, h1]

theorem fillRowC_toSt {cap : Nat} (P : Params) (fuel c : Nat) :
    ∀ (n : Nat) {s : StC}, Fits P.L cap s.toSt →
      (fillRowC P fuel c n s).toSt = fillRow P fuel c n s.toSt := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold fillRowC fillRow
    simp only [getD_linksToArray, getD_wordsToArray]
    by_cases hc : (s.overflow || getLink s.fwd c != c) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (getWord s.tab (c * P.L + (P.L - (n + 1))) == 0) = true
      · simp only [he, ↓reduceIte]
        have h1 := defineC_toSt h c (P.L - (n + 1))
        have h2 := processDedC_toSt P fuel (s := defineC P s c (P.L - (n + 1)))
          (by rw [h1]; exact define_fits h P _ _)
        rw [ih (by rw [h2, h1]; exact processDed_fits P _ (define_fits h P _ _)), h2, h1]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact ih h

theorem felschC_toSt {cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (n c : Nat) {s : StC}, Fits P.L cap s.toSt →
      (felschC P fuel n c s).toSt = felsch P fuel n c s.toSt := by
  intro n
  induction n with
  | zero => intro c s _; rfl
  | succ n ih =>
    intro c s h
    unfold felschC felsch
    by_cases hc : (decide (c < s.next) && !s.overflow) = true
    · simp only [hc, ↓reduceIte]
      have h1 := fillRowC_toSt P fuel c P.L h
      rw [ih _ (by rw [h1]; exact fillRow_fits P _ _ _ h), h1]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem hltWordC_toSt {cap : Nat} (P : Params) (c : Nat) (w w' : List Nat) :
    ∀ (fuel : Nat) {s : StC}, Fits P.L cap s.toSt →
      (hltWordC P c w w' fuel s).toSt = hltWord P c w w' fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold hltWordC hltWord
    simp only [getD_linksToArray]
    by_cases hc : (getLink s.fwd c != c) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      rw [scanWordC_eq]
      cases hr : scanWord P.L (wordsToArray s.tab) c w w' with
      | closed => rfl
      | coinc f b => exact coincidenceC_toSt h P _ _
      | deduct f x b => exact deduceC_toSt h P _ _ _
      | gap f x =>
        dsimp only
        have h1 := defineC_toSt h f x
        have ho : (defineC P s f x).overflow = (define P s.toSt f x).overflow :=
          congrArg St.overflow h1
        simp only [ho]
        by_cases hov : (define P s.toSt f x).overflow = true
        · simp only [hov, ↓reduceIte]
          exact h1
        · simp only [hov, Bool.false_eq_true, ↓reduceIte]
          rw [ih (by rw [h1]; exact define_fits h P _ _), h1]

theorem hltRowC_toSt {cap : Nat} (P : Params) (fuel c : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {s : StC}, Fits P.L cap s.toSt →
      (hltRowC P fuel c ps s).toSt = hltRow P fuel c ps s.toSt := by
  intro ps
  induction ps with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    unfold hltRowC hltRow
    by_cases ho : s.overflow = true
    · simp only [ho, ↓reduceIte]
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      have h1 := hltWordC_toSt P c p.1 p.2 (p.1.length + 1) h
      have h2 := processDedC_toSt P fuel
        (s := hltWordC P c p.1 p.2 (p.1.length + 1) s)
        (by rw [h1]; exact hltWord_fits P c p.1 p.2 _ h)
      rw [ih (by rw [h2, h1]; exact processDed_fits P _ (hltWord_fits P c p.1 p.2 _ h)), h2, h1]

theorem hltC_toSt {cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (n c : Nat) {s : StC}, Fits P.L cap s.toSt →
      (hltC P fuel n c s).toSt = hlt P fuel n c s.toSt := by
  intro n
  induction n with
  | zero => intro c s _; rfl
  | succ n ih =>
    intro c s h
    unfold hltC hlt
    by_cases hc : (decide (c < s.next) && !s.overflow) = true
    · simp only [hc, ↓reduceIte]
      have h1 := hltRowC_toSt P fuel c P.rels h
      rw [ih _ (by rw [h1]; exact hltRow_fits P fuel c _ h), h1]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem init_toSt (L cap : Nat) : (StC.init L cap).toSt = St.init L cap := by
  simp only [StC.init, StC.toSt, St.init, wordsToArray_zeroWords, linksToArray_zeroWords]

theorem enumerateC_toSt {P : Params} {cap : Nat} (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    (enumerateC P cap).toSt = enumerate P cap := by
  have h0 : Fits P.L cap (StC.init P.L cap).toSt := by
    rw [init_toSt]
    exact init_fits _ _ hcap
  unfold enumerateC enumerate
  dsimp only
  have h1 := fillSubsC_toSt P (64 * (cap + 1) * (P.L + 1)) P.subs h0
  rw [felschC_toSt P _ _ _
    (by rw [h1, init_toSt]; exact fillSubs_fits _ _ _ (init_fits _ _ hcap)), h1, init_toSt]

theorem liveC_eq (s : StC) (c : Nat) : s.liveC c = s.toSt.live c := by
  simp only [StC.liveC, St.live, getD_linksToArray]

theorem liveCountC_eq (s : StC) : s.liveCountC = s.toSt.liveCount := by
  unfold StC.liveCountC St.liveCount
  congr 1
  funext c
  exact liveC_eq s c

theorem completeC_eq (L : Nat) (s : StC) : s.completeC L = s.toSt.complete L := by
  simp only [StC.completeC, St.complete, liveC_eq, getD_wordsToArray]

theorem checkC_eq {P : Params} {cap : Nat} (n : Nat) (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    checkC P cap n = check P cap n := by
  unfold checkC check
  rw [← enumerateC_toSt hcap]
  simp only [completeC_eq, liveCountC_eq]

theorem enumerateHLTC_toSt {P : Params} {cap : Nat} (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    (enumerateHLTC P cap).toSt = enumerateHLT P cap := by
  have h0 : Fits P.L cap (StC.init P.L cap).toSt := by
    rw [init_toSt]
    exact init_fits _ _ hcap
  unfold enumerateHLTC enumerateHLT
  dsimp only
  have h1 := fillSubsC_toSt P (64 * (cap + 1) * (P.L + 1)) P.subs h0
  have h1' : Fits P.L cap (fillSubs P (64 * (cap + 1) * (P.L + 1)) P.subs (St.init P.L cap)) :=
    fillSubs_fits _ _ _ (init_fits _ _ hcap)
  have h2 := hltC_toSt P (64 * (cap + 1) * (P.L + 1)) (cap + 1) 1
    (s := fillSubsC P (64 * (cap + 1) * (P.L + 1)) P.subs (StC.init P.L cap))
    (by rw [h1, init_toSt]; exact h1')
  rw [felschC_toSt P _ _ _ (by rw [h2, h1, init_toSt]; exact hlt_fits P _ _ _ h1'), h2, h1,
    init_toSt]

theorem checkHLTC_eq {P : Params} {cap : Nat} (n : Nat) (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    checkHLTC P cap n = checkHLT P cap n := by
  unfold checkHLTC checkHLT
  rw [← enumerateHLTC_toSt hcap]
  simp only [completeC_eq, liveCountC_eq]

end CFSG.CosetTable
