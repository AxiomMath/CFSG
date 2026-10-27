module

public import Certificates.Data.Kernel.CosetW.EnumW
public import CFSG.Certificates.CosetTableCompactPresented
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Data.Nat.Bitwise

public noncomputable section

namespace CFSG.CosetTable

open CFSG.Certificates.CosetEnumeration

theorem WStore.get_of_ge {b : WStore} {i : Nat} (h : b.n ≤ i) : b.get i = 0 := by
  unfold WStore.get
  simp [show ¬ i < b.n by omega]

theorem WStore.get_lt (b : WStore) (i : Nat) : b.get i < 2 ^ 32 := by
  unfold WStore.get
  split
  · exact Nat.mod_lt _ (by decide)
  · decide

theorem WStore.n_set (b : WStore) (i v : Nat) : (b.set i v).n = b.n := by
  unfold WStore.set
  split <;> rfl

theorem testBit_of_lt_of_le {x k p : Nat} (hx : x < 2 ^ k) (hp : k ≤ p) : x.testBit p = false :=
  Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hp))

theorem WStore.get_set (b : WStore) (i v j : Nat) :
    (b.set i v).get j = if i = j ∧ i < b.n then v % 2 ^ 32 else b.get j := by
  by_cases hi : i < b.n
  · generalize hD : (b.t >>> (64 + 32 * i)) % 2 ^ 32 ^^^ v % 2 ^ 32 = D
    generalize hS : b.t % 2 ^ 64 ^^^ WStore.mix (b.t % 2 ^ 64) i v = S
    have hs : b.set i v = { n := b.n, t := b.t ^^^ (D <<< (64 + 32 * i)) ^^^ S } := by
      unfold WStore.set
      rw [if_pos hi, hD, hS]
    have hDlt : D < 2 ^ 32 :=
      hD ▸ Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    have hSlt : S < 2 ^ 64 :=
      hS ▸ Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    rw [hs]
    unfold WStore.get
    by_cases hj : j < b.n
    · simp only [hj, ↓reduceIte]
      apply Nat.eq_of_testBit_eq
      intro m
      rw [Nat.testBit_mod_two_pow]
      by_cases hm : m < 32
      · have e1 : S.testBit (64 + 32 * j + m) = false := testBit_of_lt_of_le hSlt (by omega)
        rw [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_xor, e1, Bool.xor_false,
          Nat.testBit_shiftLeft]
        by_cases hij : i = j
        · subst hij
          simp only [hi, and_self, ↓reduceIte, Nat.testBit_mod_two_pow, hm, decide_true,
            Bool.true_and, ge_iff_le, Nat.le_add_right, Nat.add_sub_cancel_left, ← hD,
            Nat.testBit_xor, Nat.testBit_shiftRight]
          cases b.t.testBit (64 + 32 * i + m) <;> simp
        · have e2 : (decide (64 + 32 * j + m ≥ 64 + 32 * i) &&
              D.testBit (64 + 32 * j + m - (64 + 32 * i))) = false := by
            by_cases hle : 64 + 32 * i ≤ 64 + 32 * j + m
            · rw [testBit_of_lt_of_le hDlt (by omega), Bool.and_false]
            · simp [hle]
          simp only [hij, false_and, ↓reduceIte, e2, Bool.xor_false, Nat.testBit_mod_two_pow,
            hm, decide_true, Bool.true_and, Nat.testBit_shiftRight]
      · simp only [hm, decide_false, Bool.false_and]
        split
        · rw [Nat.testBit_mod_two_pow]
          simp [hm]
        · rw [Nat.testBit_mod_two_pow]
          simp [hm]
    · have hij : ¬ (i = j ∧ i < b.n) := fun h => hj (h.1 ▸ h.2)
      simp only [hj, ↓reduceIte, hij]
  · have : b.set i v = b := by unfold WStore.set; simp [hi]
    rw [this]
    simp [hi]

theorem WStore.getL_lt (b : WStore) {c : Nat} (hc : c < 2 ^ 32) : b.getL c < 2 ^ 32 :=
  Nat.xor_lt_two_pow (b.get_lt c) hc

theorem WStore.getL_of_ge {b : WStore} {c : Nat} (h : b.n ≤ c) : b.getL c = c := by
  simp [WStore.getL, WStore.get_of_ge h]

theorem WStore.getL_setL (b : WStore) {c v : Nat} (hc : c < 2 ^ 32) (hv : v < 2 ^ 32)
    (j : Nat) : (b.setL c v).getL j = if c = j ∧ c < b.n then v else b.getL j := by
  unfold WStore.getL WStore.setL
  rw [WStore.get_set]
  by_cases h : c = j ∧ c < b.n
  · have h' := h
    obtain ⟨rfl, -⟩ := h'
    simp only [h, and_self, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hv hc), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · simp [h]

@[expose] def WStore.toArr (b : WStore) : Array Nat := (Array.range b.n).map b.get

@[expose] def WStore.linksArr (b : WStore) : Array Nat := (Array.range b.n).map b.getL

theorem WStore.size_toArr (b : WStore) : b.toArr.size = b.n := by simp [WStore.toArr]

theorem WStore.getD_toArr (b : WStore) (i : Nat) : b.toArr.getD i 0 = b.get i := by
  rw [Array.getD_eq_getD_getElem?]
  simp only [WStore.toArr, Array.getElem?_map, Array.getElem?_range]
  by_cases h : i < b.n
  · simp [h]
  · simp [h, WStore.get_of_ge (by omega : b.n ≤ i)]

theorem WStore.getD_linksArr (b : WStore) (c : Nat) : b.linksArr.getD c c = b.getL c := by
  rw [Array.getD_eq_getD_getElem?]
  simp only [WStore.linksArr, Array.getElem?_map, Array.getElem?_range]
  by_cases h : c < b.n
  · simp [h]
  · simp [h, WStore.getL_of_ge (by omega : b.n ≤ c)]

theorem WStore.toArr_set (b : WStore) {i v : Nat} (hv : v < 2 ^ 32) :
    (b.set i v).toArr = b.toArr.set! i v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp only [WStore.toArr, WStore.n_set, Array.getElem?_map, Array.getElem?_range,
    Array.size_map, Array.size_range]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < b.n
    · have hv' : v < 4294967296 := hv
      simp [h2, WStore.get_set, Nat.mod_eq_of_lt hv']
    · simp [h2]
  · simp [h1, WStore.get_set]

theorem WStore.linksArr_setL (b : WStore) {c v : Nat} (hc : c < 2 ^ 32) (hv : v < 2 ^ 32) :
    (b.setL c v).linksArr = b.linksArr.set! c v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  have hs : (b.setL c v).n = b.n := WStore.n_set _ _ _
  simp only [WStore.linksArr, hs, Array.getElem?_map, Array.getElem?_range, Array.size_map,
    Array.size_range]
  by_cases h1 : c = j
  · subst h1
    by_cases h2 : c < b.n
    · simp [h2, WStore.getL_setL b hc hv]
    · simp [h2]
  · simp [h1, WStore.getL_setL b hc hv]

theorem WStore.get_zero (n s i : Nat) (hs : s < 2 ^ 64) : (⟨n, s⟩ : WStore).get i = 0 := by
  unfold WStore.get
  split
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hs (Nat.pow_le_pow_right (by decide) (by omega)))]
  · rfl

theorem WStore.toArr_zero (n s : Nat) (hs : s < 2 ^ 64) :
    (⟨n, s⟩ : WStore).toArr = Array.replicate n 0 := by
  apply Array.ext_getElem?
  intro j
  simp [WStore.toArr, WStore.get_zero n s _ hs, Array.getElem?_replicate, Array.getElem?_range]

theorem WStore.linksArr_zero (n s : Nat) (hs : s < 2 ^ 64) :
    (⟨n, s⟩ : WStore).linksArr = Array.range n := by
  apply Array.ext_getElem?
  intro j
  simp [WStore.linksArr, WStore.getL, WStore.get_zero n s _ hs, Array.getElem?_range]

@[expose, reducible] def StW.toSt (s : StW) : St where
  tab := s.tab.toArr
  fwd := s.fwd.linksArr
  par := s.par.toArr
  next := s.next
  ded := s.ded
  queue := s.queue
  qi := s.qi
  overflow := s.overflow

theorem walkWS_eq (L : Nat) (tab : WStore) :
    ∀ (w : List Nat) (lim k c : Nat), walkWS L tab lim k c w = walk L tab.toArr lim k c w := by
  intro w
  induction w with
  | nil => intro lim k c; cases lim <;> rfl
  | cons x w ih =>
    intro lim k c
    cases lim with
    | zero => rfl
    | succ lim => simp only [walkWS, walk, WStore.getD_toArr, ih]

theorem findWS_eq (fwd : WStore) :
    ∀ (fuel c : Nat), findWS fwd fuel c = find fwd.linksArr fuel c := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ n ih => intro c; simp only [findWS, find, WStore.getD_linksArr, ih]

theorem findWS_lt (fwd : WStore) :
    ∀ (fuel c : Nat), c < 2 ^ 32 → findWS fwd fuel c < 2 ^ 32 := by
  intro fuel
  induction fuel with
  | zero => intro c hc; exact hc
  | succ n ih =>
    intro c hc
    simp only [findWS]
    split
    · exact hc
    · exact ih _ (WStore.getL_lt fwd hc)

theorem scanWordW_eq (L : Nat) (tab : WStore) (a : Nat) (w w' : List Nat) :
    scanWordW L tab a w w' = scanWord L tab.toArr a w w' := by
  simp only [scanWordW, scanWord, walkWS_eq]

theorem mergeW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (a b : Nat) :
    (mergeW s a b).toSt = merge s.toSt a b := by
  have hn : s.next ≤ 2 ^ 32 := h.next_lt
  simp only [mergeW, merge, findWS_eq]
  obtain ⟨ra, hra⟩ : ∃ ra, find s.fwd.linksArr s.next a = ra := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ rb, find s.fwd.linksArr s.next b = rb := ⟨_, rfl⟩
  simp only [hra, hrb]
  by_cases hc : (ra == rb || decide (s.next ≤ ra) || decide (s.next ≤ rb)) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hc
    have ha : ra < 2 ^ 32 := by omega
    have hb : rb < 2 ^ 32 := by omega
    by_cases hr : ra < rb
    · simp only [hr, ↓reduceIte, StW.toSt, WStore.linksArr_setL _ hb ha]
    · simp only [hr, ↓reduceIte, StW.toSt, WStore.linksArr_setL _ ha hb]

@[expose] def coincTransferW (P : Params) (st : StW) (g x d : Nat) : StW :=
  let ix := P.inv.getD x 0
  let mu := findWS st.fwd st.next g
  let nu := findWS st.fwd st.next d
  let e := st.tab.get (mu * P.L + x)
  if e != 0 then mergeW st nu e
  else
    let e' := st.tab.get (nu * P.L + ix)
    if e' != 0 then mergeW st mu e'
    else { st with tab := (st.tab.set (mu * P.L + x) nu).set (nu * P.L + ix) mu,
                   ded := st.ded.push (mu * P.L + x) }

@[expose] def coincClearW (P : Params) (st : StW) (g x d : Nat) : StW :=
  coincTransferW P (if st.tab.get (d * P.L + P.inv.getD x 0) == g then
      { st with tab := st.tab.set (d * P.L + P.inv.getD x 0) 0 } else st) g x d

theorem coincLetterW_eq (P : Params) (st : StW) (g x : Nat) :
    coincLetterW P st g x =
      if st.tab.get (g * P.L + x) == 0 then st
      else coincClearW P st g x (st.tab.get (g * P.L + x)) := rfl

theorem coincTransferW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params)
    (g x d : Nat) (hg : g < 2 ^ 32) (hd : d < 2 ^ 32) :
    (coincTransferW P s g x d).toSt = coincTransfer P s.toSt g x d := by
  unfold coincTransferW coincTransfer
  dsimp only
  simp only [findWS_eq, WStore.getD_toArr]
  obtain ⟨mu, hmu⟩ : ∃ mu, find s.fwd.linksArr s.next g = mu := ⟨_, rfl⟩
  obtain ⟨nu, hnu⟩ : ∃ nu, find s.fwd.linksArr s.next d = nu := ⟨_, rfl⟩
  have hmu32 : mu < 2 ^ 32 := by rw [← hmu, ← findWS_eq]; exact findWS_lt _ _ _ hg
  have hnu32 : nu < 2 ^ 32 := by rw [← hnu, ← findWS_eq]; exact findWS_lt _ _ _ hd
  simp only [hmu, hnu]
  obtain ⟨e, he⟩ : ∃ e, s.tab.get (mu * P.L + x) = e := ⟨_, rfl⟩
  simp only [he]
  by_cases hne : (e != 0) = true
  · simp only [hne, ↓reduceIte]
    exact mergeW_toSt h _ _
  · simp only [hne, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e', he'⟩ : ∃ e', s.tab.get (nu * P.L + P.inv.getD x 0) = e' := ⟨_, rfl⟩
    simp only [he']
    by_cases hne' : (e' != 0) = true
    · simp only [hne', ↓reduceIte]
      exact mergeW_toSt h _ _
    · simp only [hne', Bool.false_eq_true, ↓reduceIte]
      simp only [StW.toSt, WStore.toArr_set _ hnu32, WStore.toArr_set _ hmu32]

theorem coincClearW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params)
    (g x d : Nat) (hg : g < 2 ^ 32) (hd : d < 2 ^ 32) :
    (coincClearW P s g x d).toSt = coincClear P s.toSt g x d := by
  unfold coincClearW coincClear
  simp only [WStore.getD_toArr]
  by_cases hc : (s.tab.get (d * P.L + P.inv.getD x 0) == g) = true
  · simp only [hc, ↓reduceIte]
    have hs : ({ s with tab := s.tab.set (d * P.L + P.inv.getD x 0) 0 } : StW).toSt =
        { s.toSt with tab := s.toSt.tab.set! (d * P.L + P.inv.getD x 0) 0 } := by
      simp only [StW.toSt, WStore.toArr_set _ (by decide : 0 < 2 ^ 32)]
    have h1 : Fits L cap
        ({ s with tab := s.tab.set (d * P.L + P.inv.getD x 0) 0 } : StW).toSt :=
      h.of_fields rfl rfl rfl
    rw [coincTransferW_toSt h1 P g x d hg hd, hs]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact coincTransferW_toSt h P g x d hg hd

theorem coincLetterW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params)
    (g x : Nat) (hg : g < 2 ^ 32) :
    (coincLetterW P s g x).toSt = coincLetter P s.toSt g x := by
  rw [coincLetterW_eq, coincLetter_eq]
  simp only [WStore.getD_toArr]
  by_cases hc : (s.tab.get (g * P.L + x) == 0) = true
  · simp only [hc, ↓reduceIte]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    exact coincClearW_toSt h P g x _ hg (WStore.get_lt _ _)

theorem coincRowW_toSt {L cap : Nat} (P : Params) (g : Nat) (hg : g < 2 ^ 32) :
    ∀ (n : Nat) {s : StW}, Fits L cap s.toSt →
      (coincRowW P g n s).toSt = coincRow P g n s.toSt := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    simp only [coincRowW, coincRow]
    rw [ih (by rw [coincLetterW_toSt h P g _ hg]; exact coincLetter_fits h P g _),
      coincLetterW_toSt h P g _ hg]

theorem coincQueueW_toSt {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {s : StW}, Fits L cap s.toSt →
      (coincQueueW P fuel s).toSt = coincQueue P fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    simp only [coincQueueW, coincQueue]
    by_cases hq : s.qi < s.queue.size
    · simp only [hq, ↓reduceIte]
      have hg : s.queue.getD s.qi 0 < 2 ^ 32 := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq, Option.getD_some]
        exact h.queue_lt32 _ (Array.getElem_mem hq)
      have h1 : Fits L cap ({ s with qi := s.qi + 1 } : StW).toSt := h.of_fields rfl rfl rfl
      have h2 := coincRowW_toSt (cap := cap) P (s.queue.getD s.qi 0) hg P.L h1
      rw [ih (by rw [h2]; exact coincRow_fits P _ _ h1), h2]
    · simp only [hq, ↓reduceIte]

theorem coincidenceW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params)
    (a b : Nat) : (coincidenceW P s a b).toSt = coincidence P s.toSt a b := by
  unfold coincidenceW coincidence
  rw [coincQueueW_toSt P _ (by rw [mergeW_toSt h]; exact merge_fits h a b), mergeW_toSt h]

theorem deduceW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params)
    (f x b : Nat) : (deduceW P s f x b).toSt = deduce P s.toSt f x b := by
  have hn : s.next ≤ 2 ^ 32 := h.next_lt
  unfold deduceW deduce
  dsimp only []
  by_cases hg : (f < s.next ∧ b < s.next) ∧ x < P.L
  · obtain ⟨⟨hf, hb⟩, hx⟩ := hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, hf, hb, hx, and_self, ↓reduceIte]
    simp only [StW.toSt, WStore.toArr_set _ (by omega : b < 2 ^ 32),
      WStore.toArr_set _ (by omega : f < 2 ^ 32)]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, hg, ↓reduceIte]

theorem defineW_toSt {cap : Nat} {P : Params} {s : StW} (h : Fits P.L cap s.toSt) (a x : Nat) :
    (defineW P s a x).toSt = define P s.toSt a x := by
  unfold defineW define
  dsimp only []
  by_cases hg : ((0 < a ∧ a < s.next) ∧ x < P.L) ∧ s.next < s.par.n
  · obtain ⟨⟨⟨h0, ha⟩, hx⟩, hb⟩ := hg
    have hpar : s.par.n = cap + 1 := by
      have := h.par_size
      simpa only [WStore.size_toArr] using this
    have hsz := h.size_le
    have h1 : (a + 1) * P.L ≤ (cap + 2) * (P.L + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : (a + 1) * P.L = a * P.L + P.L := by rw [Nat.add_mul, Nat.one_mul]
    have hpv : a * P.L + x < 2 ^ 32 := by omega
    have hb32 : s.next < 2 ^ 32 := by
      have : cap + 2 ≤ (cap + 2) * (P.L + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, WStore.size_toArr, h0, ha, hx, hb, and_self,
      ↓reduceIte]
    simp only [StW.toSt, WStore.toArr_set _ hb32, WStore.toArr_set _ (by omega : a < 2 ^ 32),
      WStore.toArr_set _ hpv]
  · simp only [Bool.and_eq_true, decide_eq_true_eq, WStore.size_toArr, hg, ↓reduceIte]

theorem scanW_toSt {L cap : Nat} {s : StW} (h : Fits L cap s.toSt) (P : Params) (a : Nat)
    (w w' : List Nat) : (scanW P s a w w').toSt = scan P s.toSt a w w' := by
  unfold scanW scan
  rw [scanWordW_eq]
  cases hr : scanWord P.L s.tab.toArr a w w' with
  | closed => rfl
  | coinc f b => exact coincidenceW_toSt h P _ _
  | deduct f x b => exact deduceW_toSt h P _ _ _
  | gap f x => rfl

theorem scanAllW_toSt {L cap : Nat} (P : Params) (a : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {s : StW}, Fits L cap s.toSt →
      (scanAllW P a ps s).toSt = scanAll P a ps s.toSt := by
  intro ps
  induction ps with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    unfold scanAllW scanAll
    simp only [WStore.getD_linksArr]
    by_cases hc : (s.fwd.getL a == a) = true
    · simp only [hc, ↓reduceIte]
      have h1 := scanW_toSt h P a p.1 p.2
      rw [ih (by rw [h1]; exact scan_fits h P a _ _), h1]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem processDedW_toSt {L cap : Nat} (P : Params) :
    ∀ (fuel : Nat) {s : StW}, Fits L cap s.toSt →
      (processDedW P fuel s).toSt = processDed P fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold processDedW processDed
    rcases hb : s.ded.back? with _ | e
    · rfl
    · simp only [WStore.getD_linksArr]
      have h1 : Fits L cap ({ s with ded := s.ded.pop } : StW).toSt := h.of_fields rfl rfl rfl
      by_cases hc : (s.fwd.getL (e / P.L) == e / P.L) = true
      · simp only [hc, ↓reduceIte]
        have h2 := scanAllW_toSt P (e / P.L) (P.scans.getD (e % P.L) []) h1
        rw [ih (by rw [h2]; exact scanAll_fits P _ _ h1), h2]
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact ih h1

theorem fillWordW_toSt {cap : Nat} (P : Params) (w w' : List Nat) :
    ∀ (fuel : Nat) {s : StW}, Fits P.L cap s.toSt →
      (fillWordW P w w' fuel s).toSt = fillWord P w w' fuel s.toSt := by
  intro fuel
  induction fuel with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold fillWordW fillWord
    rw [scanWordW_eq]
    cases hr : scanWord P.L s.tab.toArr 1 w w' with
    | closed => rfl
    | coinc f b => exact coincidenceW_toSt h P _ _
    | deduct f x b => exact deduceW_toSt h P _ _ _
    | gap f x =>
      dsimp only
      have h1 := defineW_toSt h f x
      have ho : (defineW P s f x).overflow = (define P s.toSt f x).overflow :=
        congrArg St.overflow h1
      simp only [ho]
      by_cases hov : (define P s.toSt f x).overflow = true
      · simp only [hov, ↓reduceIte]
        exact h1
      · simp only [hov, Bool.false_eq_true, ↓reduceIte]
        rw [ih (by rw [h1]; exact define_fits h P _ _), h1]

theorem fillSubsW_toSt {cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (ps : List (List Nat × List Nat)) {s : StW}, Fits P.L cap s.toSt →
      (fillSubsW P fuel ps s).toSt = fillSubs P fuel ps s.toSt := by
  intro ps
  induction ps with
  | nil => intro s _; rfl
  | cons p ps ih =>
    intro s h
    unfold fillSubsW fillSubs
    have h1 := fillWordW_toSt P p.1 p.2 (p.1.length + 1) h
    have h2 := processDedW_toSt P fuel
      (s := fillWordW P p.1 p.2 (p.1.length + 1) s) (by rw [h1]; exact fillWord_fits P _ _ _ h)
    rw [ih (by rw [h2, h1]; exact processDed_fits P _ (fillWord_fits P _ _ _ h)), h2, h1]

theorem fillRowW_toSt {cap : Nat} (P : Params) (fuel c : Nat) :
    ∀ (n : Nat) {s : StW}, Fits P.L cap s.toSt →
      (fillRowW P fuel c n s).toSt = fillRow P fuel c n s.toSt := by
  intro n
  induction n with
  | zero => intro s _; rfl
  | succ n ih =>
    intro s h
    unfold fillRowW fillRow
    simp only [WStore.getD_linksArr, WStore.getD_toArr]
    by_cases hc : (s.overflow || s.fwd.getL c != c) = true
    · simp only [hc, ↓reduceIte]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      by_cases he : (s.tab.get (c * P.L + (P.L - (n + 1))) == 0) = true
      · simp only [he, ↓reduceIte]
        have h1 := defineW_toSt h c (P.L - (n + 1))
        have h2 := processDedW_toSt P fuel (s := defineW P s c (P.L - (n + 1)))
          (by rw [h1]; exact define_fits h P _ _)
        rw [ih (by rw [h2, h1]; exact processDed_fits P _ (define_fits h P _ _)), h2, h1]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact ih h

theorem felschW_toSt {cap : Nat} (P : Params) (fuel : Nat) :
    ∀ (n c : Nat) {s : StW}, Fits P.L cap s.toSt →
      (felschW P fuel n c s).toSt = felsch P fuel n c s.toSt := by
  intro n
  induction n with
  | zero => intro c s _; rfl
  | succ n ih =>
    intro c s h
    unfold felschW felsch
    by_cases hc : (decide (c < s.next) && !s.overflow) = true
    · simp only [hc, ↓reduceIte]
      have h1 := fillRowW_toSt P fuel c P.L h
      rw [ih _ (by rw [h1]; exact fillRow_fits P _ _ _ h), h1]
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem initW_toSt (L cap : Nat) : (StW.init L cap).toSt = St.init L cap := by
  simp only [StW.init, StW.toSt, St.init, WStore.toArr_zero _ _ (by decide : 1 < 2 ^ 64),
    WStore.toArr_zero _ _ (by decide : 3 < 2 ^ 64), WStore.linksArr_zero _ _ (by decide : 2 < 2 ^ 64)]

theorem enumerateW_toSt {P : Params} {cap : Nat} (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    (enumerateW P cap).toSt = enumerate P cap := by
  have h0 : Fits P.L cap (StW.init P.L cap).toSt := by
    rw [initW_toSt]
    exact init_fits _ _ hcap
  unfold enumerateW enumerate
  dsimp only
  have h1 := fillSubsW_toSt P (64 * (cap + 1) * (P.L + 1)) P.subs h0
  rw [felschW_toSt P _ _ _
    (by rw [h1, initW_toSt]; exact fillSubs_fits _ _ _ (init_fits _ _ hcap)), h1, initW_toSt]

theorem liveW_eq (s : StW) (c : Nat) : s.liveW c = s.toSt.live c := by
  simp only [StW.liveW, St.live, WStore.getD_linksArr]

theorem liveCountW_eq (s : StW) : s.liveCountW = s.toSt.liveCount := by
  unfold StW.liveCountW St.liveCount
  congr 1
  funext c
  exact liveW_eq s c

theorem completeW_eq (L : Nat) (s : StW) : s.completeW L = s.toSt.complete L := by
  simp only [StW.completeW, St.complete, liveW_eq, WStore.getD_toArr]

theorem checkW_eq {P : Params} {cap : Nat} (n : Nat) (hcap : (cap + 2) * (P.L + 1) ≤ 2 ^ 32) :
    checkW P cap n = check P cap n := by
  unfold checkW check
  rw [← enumerateW_toSt hcap]
  simp only [completeW_eq, liveCountW_eq]

@[expose] def lenFilter (k : Nat) (M : List (List Nat)) : List (List Nat) :=
  M.filter fun w => w.length == k

abbrev LenSorted (M : List (List Nat)) : Prop := M.Pairwise fun u v => u.length ≤ v.length

theorem lenFilter_cons (k : Nat) (a : List Nat) (M : List (List Nat)) :
    lenFilter k (a :: M) = if a.length = k then a :: lenFilter k M else lenFilter k M := by
  unfold lenFilter
  rw [List.filter_cons]
  by_cases h : a.length = k <;> simp [h]

theorem eq_of_lenFilter : ∀ (M₁ M₂ : List (List Nat)), LenSorted M₁ → LenSorted M₂ →
    (∀ k, lenFilter k M₁ = lenFilter k M₂) → M₁ = M₂ := by
  intro M₁
  induction M₁ with
  | nil =>
    intro M₂ _ _ h
    cases M₂ with
    | nil => rfl
    | cons b r =>
      have := h b.length
      simp [lenFilter_cons, lenFilter] at this
  | cons a r₁ ih =>
    intro M₂ h₁ h₂ h
    cases M₂ with
    | nil =>
      have := h a.length
      simp [lenFilter_cons, lenFilter] at this
    | cons b r₂ =>
      simp only [LenSorted, List.pairwise_cons] at h₁ h₂
      have mem : ∀ (x : List Nat) (M : List (List Nat)) (k : Nat),
          x ∈ lenFilter k M → x ∈ M ∧ x.length = k := by
        intro x M k hx
        simpa [lenFilter] using hx
      have hab : a.length = b.length := by
        have ha : a ∈ lenFilter a.length (b :: r₂) := by
          rw [← h a.length, lenFilter_cons, if_pos rfl]
          exact List.mem_cons_self
        have hb : b ∈ lenFilter b.length (a :: r₁) := by
          rw [h b.length, lenFilter_cons, if_pos rfl]
          exact List.mem_cons_self
        obtain ⟨ha1, -⟩ := mem _ _ _ ha
        obtain ⟨hb1, -⟩ := mem _ _ _ hb
        have e1 : b.length ≤ a.length := by
          rcases List.mem_cons.mp ha1 with e | e
          · rw [e]
          · exact h₂.1 a e
        have e2 : a.length ≤ b.length := by
          rcases List.mem_cons.mp hb1 with e | e
          · rw [e]
          · exact h₁.1 b e
        omega
      have hk := h a.length
      rw [lenFilter_cons, lenFilter_cons, if_pos rfl, if_pos hab.symm] at hk
      obtain ⟨rfl, -⟩ := List.cons.inj hk
      congr 1
      apply ih r₂ h₁.2 h₂.2
      intro k
      have hk' := h k
      rw [lenFilter_cons, lenFilter_cons] at hk'
      by_cases e : a.length = k
      · rw [if_pos e, if_pos e] at hk'
        exact (List.cons.inj hk').2
      · rw [if_neg e, if_neg e] at hk'
        exact hk'

theorem lenSorted_mergeSort (l : List (List Nat)) :
    LenSorted (l.mergeSort fun u v => decide (u.length ≤ v.length)) := by
  have := List.pairwise_mergeSort (le := fun u v : List Nat => decide (u.length ≤ v.length))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  simpa using this

theorem lenFilter_mergeSort (k : Nat) (l : List (List Nat)) :
    lenFilter k (l.mergeSort fun u v => decide (u.length ≤ v.length)) = lenFilter k l := by
  symm
  apply List.Sublist.eq_of_length
  · have hs : List.Sublist (lenFilter k l)
        (l.mergeSort fun u v => decide (u.length ≤ v.length)) := by
      apply List.sublist_mergeSort
        (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
        (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      · unfold lenFilter
        apply List.Pairwise.imp_of_mem (R := fun u v => u.length = k ∧ v.length = k)
        · intro u v _ _ huv
          simp [huv.1, huv.2]
        · rw [List.pairwise_iff_forall_sublist]
          intro u v huv
          have hu := huv.subset (List.mem_cons_self)
          have hv := huv.subset (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [List.mem_filter, beq_iff_eq] at hu hv
          exact ⟨hu.2, hv.2⟩
      · exact List.filter_sublist
    have := hs.filter (fun w => w.length == k)
    unfold lenFilter at this ⊢
    rwa [List.filter_filter, List.filter_congr (q := fun w => w.length == k)] at this
    intro x _
    simp
  · unfold lenFilter
    exact ((List.mergeSort_perm _ _).filter _).length_eq.symm

theorem mem_insW (a x : List Nat) : ∀ M, x ∈ insW a M ↔ x = a ∨ x ∈ M := by
  intro M
  induction M with
  | nil => simp [insW]
  | cons b m ih =>
    unfold insW
    split
    · simp
    · rw [List.mem_cons, ih, List.mem_cons]
      tauto

theorem lenFilter_insW (k : Nat) (a : List Nat) :
    ∀ M, lenFilter k (insW a M) = lenFilter k (a :: M) := by
  intro M
  induction M with
  | nil => rfl
  | cons b m ih =>
    unfold insW
    split
    · rfl
    · rename_i hlt
      simp only [lenFilter_cons, ih]
      by_cases ha : a.length = k <;> by_cases hb : b.length = k <;> simp [ha, hb] <;> omega

theorem lenSorted_insW (a : List Nat) : ∀ M, LenSorted M → LenSorted (insW a M) := by
  intro M
  induction M with
  | nil => intro _; simp [insW]
  | cons b m ih =>
    intro h
    simp only [LenSorted, List.pairwise_cons] at h
    unfold insW
    split
    · rename_i hab
      simp only [LenSorted, List.pairwise_cons]
      refine ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.mp hx with e | e
      · rw [e]; exact hab
      · exact Nat.le_trans hab (h.1 x e)
    · rename_i hab
      simp only [LenSorted, List.pairwise_cons]
      refine ⟨?_, ih h.2⟩
      intro x hx
      rcases (mem_insW a x m).mp hx with e | e
      · rw [e]; omega
      · exact h.1 x e

theorem lenSorted_msortW : ∀ l, LenSorted (msortW l) := by
  intro l
  induction l with
  | nil => simp [msortW]
  | cons a l ih => exact lenSorted_insW a _ ih

theorem lenFilter_msortW (k : Nat) : ∀ l, lenFilter k (msortW l) = lenFilter k l := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [msortW, lenFilter_insW, lenFilter_cons, ih, lenFilter_cons]

theorem msortW_eq (l : List (List Nat)) :
    msortW l = l.mergeSort fun u v => decide (u.length ≤ v.length) :=
  eq_of_lenFilter _ _ (lenSorted_msortW l) (lenSorted_mergeSort l) fun k => by
    rw [lenFilter_msortW, lenFilter_mergeSort]

theorem mkParamsW_eq (L : Nat) (inv : Array Nat) (rels subs : List (List Nat)) :
    mkParamsW L inv rels subs = mkParams L inv rels subs := by
  unfold mkParamsW mkParams
  simp only [msortW_eq, ← List.toArray_range, List.map_toArray]

theorem invArrW_eq (m : Nat) : invArrW m = invArr m := by
  unfold invArrW invArr
  rw [← List.toArray_range, List.map_toArray]
  rfl

theorem subsetCheck_eq_checkW {m : Nat} (ws : List (List (Fin m × Bool))) (S : List Nat)
    {cap n : Nat} (hcap : (cap + 2) * (2 * m + 1) ≤ 2 ^ 32) :
    subsetCheck ws S cap n = checkW (mkParamsW (2 * m) (invArrW m) (codes ws)
      (codes ((subsetOf m S).map fun x => [(x, true)]))) cap n := by
  unfold subsetCheck presParams
  rw [mkParamsW_eq, invArrW_eq, checkW_eq n hcap]

theorem cyclicCheckC_eq_checkW {m : Nat} (ws : List (List (Fin m × Bool))) (u : List Nat)
    {k cap n : Nat} (hcap : (cap + 2) * (2 * m + 1) ≤ 2 ^ 32) :
    cyclicCheckC ws u k cap n = (u.all (fun c => decide (c < 2 * m)) &&
      (codes ws).contains (List.replicate k u).flatten &&
      checkW (mkParamsW (2 * m) (invArrW m) (codes ws) [u]) cap n) := by
  unfold cyclicCheckC
  rw [checkC_eq n hcap, mkParamsW_eq, invArrW_eq, checkW_eq n hcap]
  have h' : (cap + 2) * (2 * m + 1) ≤ 4294967296 := hcap
  simp [h']

end CFSG.CosetTable
