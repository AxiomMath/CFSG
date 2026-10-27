
module

public import CFSG.LargeExtraspecial.SMod20UaBasic

@[expose] public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

@[expose, irreducible] def collI : Array (Array ℕ) := collInvs collS2 (collMeet collS2)

structure CollFacts : Prop where
  co : collCoOK = true
  valid : collValid collS2 collBase.toList collSteps = true
  cover : ∀ k < 21, (collBase.toList ++ collSteps.map (·.1)).contains k = true
  frame : collFrame collS2 0 1 4 10 3 = true
  bound : collBoundOK collI (collFixTab collI) (collCommTab collI) = true

theorem getElem!_set!' {a : Array ℕ} {i j v : ℕ} (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ j (by rw [Array.size_setIfInBounds]; exact hj),
    Array.getElem_setIfInBounds hj, getElem!_pos a j hj]

theorem size_set!' (a : Array ℕ) (i v : ℕ) : (a.set! i v).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem array_ext_getElem! {a b : Array ℕ} {n : ℕ} (ha : a.size = n) (hb : b.size = n)
    (h : ∀ k < n, a[k]! = b[k]!) : a = b :=
  Array.ext (ha.trans hb.symm) fun k hk hk' => by
    have := h k (ha ▸ hk)
    rwa [getElem!_pos a k hk, getElem!_pos b k hk'] at this

theorem collId_get {k : ℕ} (hk : k < 21) : collId[k]! = k := by
  unfold collId
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem collComp_get {s t : Array ℕ} {k : ℕ} (hk : k < 21) : (collComp s t)[k]! = s[t[k]!]! := by
  unfold collComp
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem collComp_eq_collId {s : Array ℕ} :
    collComp s s = collId ↔ ∀ k < 21, s[s[k]!]! = k := by
  constructor
  · intro h k hk
    rw [← collComp_get hk, h, collId_get hk]
  · intro h
    refine Array.ext (by rw [collComp_size, collId, Array.size_ofFn]) fun k hk _ => ?_
    have hk' : k < 21 := by rwa [collComp_size] at hk
    rw [collComp_getElem, h k hk']
    simp only [collId, Array.getElem_ofFn]

theorem collS2_get {v : ℕ} (hv : v < 512) :
    collS2[v]! = true ↔ ∃ u < 21, ∃ w < 21, u ≠ w ∧ uaCo[u]! ^^^ uaCo[w]! = v := by
  unfold collS2
  rw [getElem!_pos _ v (by rw [Array.size_ofFn]; exact hv), Array.getElem_ofFn]
  simp only [anyIn_eq_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]

theorem collAdm_parts {s : Array ℕ} (h : collAdm s = true) :
    s.size = 21 ∧ (∀ k < 21, s[k]! < 21) ∧ (∀ k < 21, ∀ l < 21, s[k]! = s[l]! → k = l) ∧
      ∀ k < 21, collAmat s uaCo[k]! = uaCo[s[k]!]! := by
  unfold collAdm at h
  simp only [Bool.and_eq_true, beq_iff_eq, allIn_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    bne_iff_ne] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun k hk => h2 k (Nat.zero_le _) hk, fun k hk l hl he => ?_,
    fun k hk => h4 k (Nat.zero_le _) hk⟩
  exact (h3 k (Nat.zero_le _) hk l (Nat.zero_le _) hl).resolve_right (by simpa using he)

theorem collAmat_xor (s : Array ℕ) (a b : ℕ) :
    collAmat s (a ^^^ b) = collAmat s a ^^^ collAmat s b := by
  simp only [collAmat, collAmatN_eq, bitSum_xor]

theorem uaCo_xor_lt {a b c : ℕ} (ha : a < 21) (hb : b < 21) (hc : c < 21) :
    uaCo[a]! ^^^ uaCo[b]! ^^^ uaCo[c]! < 512 :=
  Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (uaCo_lt ha) (uaCo_lt hb)) (uaCo_lt hc)

theorem collOn_adm {s : Array ℕ} (hs : collAdm s = true) {x y z : ℕ} (hx : x < 21) (hy : y < 21)
    (hz : z < 21) (h : collOn collS2 x y z = true) :
    collOn collS2 s[x]! s[y]! s[z]! = true := by
  obtain ⟨-, hlt, hinj, hA⟩ := collAdm_parts hs
  unfold collOn at h ⊢
  simp only [Bool.and_eq_true, bne_iff_ne] at h ⊢
  obtain ⟨⟨⟨hxy, hyz⟩, hxz⟩, hS⟩ := h
  refine ⟨⟨⟨fun e => hxy (hinj x hx y hy e), fun e => hyz (hinj y hy z hz e)⟩,
    fun e => hxz (hinj x hx z hz e)⟩, ?_⟩
  obtain ⟨u, hu, w, hw, huw, he⟩ := (collS2_get (uaCo_xor_lt hx hy hz)).1 hS
  rw [collS2_get (uaCo_xor_lt (hlt x hx) (hlt y hy) (hlt z hz))]
  refine ⟨s[u]!, hlt u hu, s[w]!, hlt w hw, fun e => huw (hinj u hu w hw e), ?_⟩
  rw [← hA u hu, ← hA w hw, ← collAmat_xor, he, collAmat_xor, collAmat_xor, hA x hx, hA y hy,
    hA z hz]

theorem collP_adm {s : Array ℕ} (hs : collAdm s = true) {z a b : ℕ} (hz : z < 21) (ha : a < 21)
    (hb : b < 21) (h : collP collS2 z a b = true) : collP collS2 s[z]! s[a]! s[b]! = true := by
  unfold collP at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (by rw [h]))
  · exact Or.inl (Or.inr (by rw [h]))
  · exact Or.inr (collOn_adm hs hz ha hb h)

theorem collP_adm_iff {s : Array ℕ} (hs : collAdm s = true) (hinv : ∀ k < 21, s[s[k]!]! = k)
    {z a b : ℕ} (hz : z < 21) (ha : a < 21) (hb : b < 21) :
    collP collS2 s[z]! s[a]! s[b]! = true ↔ collP collS2 z a b = true := by
  obtain ⟨-, hlt, -, -⟩ := collAdm_parts hs
  refine ⟨fun h => ?_, collP_adm hs hz ha hb⟩
  have := collP_adm hs (hlt z hz) (hlt a ha) (hlt b hb) h
  rwa [hinv z hz, hinv a ha, hinv b hb] at this

theorem collOn_adm_iff {s : Array ℕ} (hs : collAdm s = true) (hinv : ∀ k < 21, s[s[k]!]! = k)
    {z a b : ℕ} (hz : z < 21) (ha : a < 21) (hb : b < 21) :
    collOn collS2 s[z]! s[a]! s[b]! = true ↔ collOn collS2 z a b = true := by
  obtain ⟨-, hlt, -, -⟩ := collAdm_parts hs
  refine ⟨fun h => ?_, collOn_adm hs hz ha hb⟩
  have := collOn_adm hs (hlt z hz) (hlt a ha) (hlt b hb) h
  rwa [hinv z hz, hinv a ha, hinv b hb] at this

theorem collMeet_get {a b c d : ℕ} (ha : a < 21) (hb : b < 21) (hc : c < 21) (hd : d < 21) :
    (collMeet collS2)[a * 9261 + b * 441 + c * 21 + d]! = collSearch collS2 a b c d := by
  unfold collMeet
  rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only
  congr 1 <;> omega

theorem collSearch_adm {s : Array ℕ} (hs : collAdm s = true) (hinv : ∀ k < 21, s[s[k]!]! = k)
    {x a b c d : ℕ} (hx : x < 21) (ha : a < 21) (hb : b < 21) (hc : c < 21) (hd : d < 21)
    (huniq : ∀ z < 21, collQ collS2 z a b c d = true ↔ z = x) :
    collSearch collS2 s[a]! s[b]! s[c]! s[d]! = s[x]! := by
  obtain ⟨-, hlt, -, -⟩ := collAdm_parts hs
  unfold collSearch
  rw [find?_range_eq_some (hlt x hx) fun z hz => ?_]
  · rfl
  unfold collQ
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    rw [← hinv z hz] at h1 h2
    have := (huniq s[z]! (hlt z hz)).1 (by
      unfold collQ
      rw [Bool.and_eq_true, ← collP_adm_iff hs hinv (hlt z hz) ha hb,
        ← collP_adm_iff hs hinv (hlt z hz) hc hd]
      exact ⟨h1, h2⟩)
    rw [← hinv z hz, this]
  · rintro rfl
    have h := (huniq x hx).2 rfl
    unfold collQ at h
    rw [Bool.and_eq_true] at h
    exact ⟨collP_adm hs hx ha hb h.1, collP_adm hs hx hc hd h.2⟩

theorem collValid_cons {K : List ℕ} {st : ℕ × ℕ × ℕ × ℕ × ℕ}
    {L : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (h : collValid collS2 K (st :: L) = true) :
    (st.2.1 ∈ K ∧ st.2.2.1 ∈ K ∧ st.2.2.2.1 ∈ K ∧ st.2.2.2.2 ∈ K) ∧ st.1 < 21 ∧
      (∀ z < 21, collQ collS2 z st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 = true ↔ z = st.1) ∧
      collValid collS2 (st.1 :: K) L = true := by
  unfold collValid at h
  simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨⟨h1, h2, h3, h4⟩, h5, fun z hz => ?_, h7⟩
  have := (allIn_eq_true.1 h6) z (Nat.zero_le _) hz
  rw [beq_iff_eq] at this
  rw [this, beq_iff_eq]

theorem foldl_collStep {s : Array ℕ} (hs : collAdm s = true) (hinv : ∀ k < 21, s[s[k]!]! = k) :
    ∀ (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (K : List ℕ) (arr : Array ℕ),
      collValid collS2 K L = true → arr.size = 21 → (∀ k ∈ K, k < 21 ∧ arr[k]! = s[k]!) →
      (L.foldl (collStep (collMeet collS2)) arr).size = 21 ∧
        ∀ k ∈ K ++ L.map (·.1), (L.foldl (collStep (collMeet collS2)) arr)[k]! = s[k]!
  | [], K, arr, _, hsz, hK => ⟨hsz, fun k hk => (hK k (by simpa using hk)).2⟩
  | st :: L, K, arr, hv, hsz, hK => by
    obtain ⟨-, hlt, -, -⟩ := collAdm_parts hs
    obtain ⟨⟨ha, hb, hc, hd⟩, hx, huniq, hv'⟩ := collValid_cons hv
    obtain ⟨ha', ha''⟩ := hK _ ha
    obtain ⟨hb', hb''⟩ := hK _ hb
    obtain ⟨hc', hc''⟩ := hK _ hc
    obtain ⟨hd', hd''⟩ := hK _ hd
    have hstep : collStep (collMeet collS2) arr st = arr.set! st.1 s[st.1]! := by
      unfold collStep
      rw [ha'', hb'', hc'', hd'', collMeet_get (hlt _ ha') (hlt _ hb') (hlt _ hc') (hlt _ hd'),
        collSearch_adm hs hinv hx ha' hb' hc' hd' huniq]
    have H := foldl_collStep hs hinv L (st.1 :: K) (collStep (collMeet collS2) arr st) hv'
      (by rw [hstep, size_set!', hsz]) (fun k hk => by
        rw [hstep]
        rcases List.mem_cons.1 hk with rfl | hk
        · exact ⟨hx, by rw [getElem!_set!' (by rw [hsz]; exact hx)]; simp⟩
        · obtain ⟨hk1, hk2⟩ := hK k hk
          refine ⟨hk1, ?_⟩
          rw [getElem!_set!' (by rw [hsz]; exact hk1)]
          split
          · next he => rw [he]
          · exact hk2)
    rw [List.foldl_cons]
    refine ⟨H.1, fun k hk => H.2 k ?_⟩
    simp only [List.mem_append, List.mem_cons, List.map_cons] at hk ⊢
    tauto

theorem collInit_get (y : Array ℕ) :
    (collInit y)[0]! = y[0]! ∧ (collInit y)[1]! = y[1]! ∧ (collInit y)[4]! = y[2]! ∧
      (collInit y)[10]! = y[3]! ∧ (collInit y)[3]! = y[4]! ∧ (collInit y).size = 21 := by
  unfold collInit
  refine ⟨?_, ?_, ?_, ?_, ?_, Array.size_ofFn⟩ <;>
    rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; norm_num), Array.getElem_ofFn] <;> rfl

theorem mem_collDom {y0 y1 y2 y3 y4 : ℕ} (h0 : y0 < 21) (h1 : y1 < 21) (h2 : y2 < 21)
    (h3 : y3 < 21) (h4 : y4 < 21) (hf : collFrame collS2 y0 y1 y2 y3 y4 = true) :
    #[y0, y1, y2, y3, y4] ∈ collDom collS2 := by
  unfold collDom
  simp only [List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨y0, h0, y1, h1, y2, h2, y3, h3, y4, h4, by simp [hf]⟩

theorem countP_range_eq_card (p : ℕ → Bool) (n : ℕ) :
    (List.range n).countP p = ((Finset.range n).filter fun a => p a = true).card := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card, List.countP_eq_length_filter]
  simp

theorem collFixTab_get {I : Array (Array ℕ)} {i a : ℕ} (hi : i < I.size) (ha : a < 512) :
    ((collFixTab I)[i]!)[a]! = (collAmat I[i]! a == a) := by
  unfold collFixTab
  rw [getElem!_pos _ i (by rw [Array.size_map]; exact hi), Array.getElem_map,
    getElem!_pos _ a (by rw [Array.size_ofFn]; exact ha), Array.getElem_ofFn,
    getElem!_pos I i hi]

theorem collCommTab_get {I : Array (Array ℕ)} {i j : ℕ} (hi : i < I.size) (hj : j < I.size) :
    ((collCommTab I)[i]!)[j]! = (collComp I[i]! I[j]! == collComp I[j]! I[i]!) := by
  unfold collCommTab
  rw [getElem!_pos _ i (by rw [Array.size_map]; exact hi), Array.getElem_map,
    getElem!_pos _ j (by rw [Array.size_map]; exact hj), Array.getElem_map,
    getElem!_pos I i hi, getElem!_pos I j hj]

theorem exists_idx_collI {s : Array ℕ} (hs : s ∈ collI) : ∃ i < collI.size, collI[i]! = s := by
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.1 hs
  exact ⟨i, hi, by rw [getElem!_pos collI i hi, he]⟩

end CFSG.LargeExtraspecial.SMod20
