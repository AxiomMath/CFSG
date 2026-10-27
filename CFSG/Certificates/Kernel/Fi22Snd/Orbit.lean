module

public import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.KC.Fi22Snd

open CFSG.Sporadic.FischerOddCore.Native

private def cmBody (c : Array Nat) (w : Nat) (mp : Std.HashMap Nat Nat) :
    Id (ForInStep (Std.HashMap Nat Nat)) :=
  pure (ForInStep.yield (mp.insert c[w]! w))

private theorem colMatch_eq_loop (n : Nat) (c src : Array Nat) :
    colMatch n c src = Array.ofFn (n := n) fun v =>
      (Id.run (forIn (List.range' 0 n) (∅ : Std.HashMap Nat Nat) (cmBody c))).getD
        src[v.val]! n := by
  unfold colMatch
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def CmInv (n : Nat) (c : Array Nat) (s : Nat) (mp : Std.HashMap Nat Nat) : Prop :=
  ∀ a, ((∃ w < s, c[w]! = a) → mp.getD a n < s ∧ c[mp.getD a n]! = a) ∧
    ((¬∃ w < s, c[w]! = a) → mp.getD a n = n)

private theorem cmInv_step {n : Nat} {c : Array Nat} {s : Nat} {mp : Std.HashMap Nat Nat}
    (h : CmInv n c s mp) : CmInv n c (s + 1) (mp.insert c[s]! s) := by
  intro a
  rw [Std.HashMap.getD_insert]
  by_cases hca : c[s]! = a
  · have hb : (c[s]! == a) = true := beq_iff_eq.2 hca
    rw [if_pos hb]
    exact ⟨fun _ => ⟨Nat.lt_succ_self s, hca⟩, fun hne => absurd ⟨s, Nat.lt_succ_self s, hca⟩ hne⟩
  · have hb : ¬ (c[s]! == a) = true := fun hh => hca (beq_iff_eq.1 hh)
    rw [if_neg hb]
    refine ⟨fun ⟨w, hw, hwa⟩ => ?_, fun hne => ?_⟩
    · have hws : w < s := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h' | h'
        · exact h'
        · subst h'; exact absurd hwa hca
      obtain ⟨h1, h2⟩ := (h a).1 ⟨w, hws, hwa⟩
      exact ⟨Nat.lt_succ_of_lt h1, h2⟩
    · apply (h a).2
      rintro ⟨w, hw, hwa⟩
      exact hne ⟨w, Nat.lt_succ_of_lt hw, hwa⟩

private theorem cmInv_loop {n : Nat} {c : Array Nat} :
    ∀ (m s : Nat) (mp : Std.HashMap Nat Nat), CmInv n c s mp →
      CmInv n c (s + m) (Id.run (forIn (List.range' s m) mp (cmBody c))) := by
  intro m
  induction m with
  | zero => intro s mp h; exact h
  | succ m ih =>
    intro s mp h
    rw [List.range'_succ, List.forIn_cons]
    have := ih (s + 1) (mp.insert c[s]! s) (cmInv_step h)
    rw [show s + (m + 1) = s + 1 + m by omega]
    exact this

private theorem colMatch_getElem {n : Nat} {c src : Array Nat} {v : Nat} (hv : v < n) :
    (colMatch n c src)[v]! =
      (Id.run (forIn (List.range' 0 n) (∅ : Std.HashMap Nat Nat) (cmBody c))).getD src[v]! n := by
  rw [colMatch_eq_loop, getElem!_pos _ _ (by simpa using hv)]
  simp [Array.getElem_ofFn]

private theorem cmInv_final (n : Nat) (c : Array Nat) :
    CmInv n c n (Id.run (forIn (List.range' 0 n) (∅ : Std.HashMap Nat Nat) (cmBody c))) := by
  have h0 : CmInv n c 0 (∅ : Std.HashMap Nat Nat) := fun a => by
    refine ⟨fun ⟨w, hw, _⟩ => absurd hw (Nat.not_lt_zero w), fun _ => ?_⟩
    simp
  simpa using cmInv_loop n 0 _ h0

private abbrev OE := Nat × Nat × Nat × Nat

private def gBody (n : Nat) (gens : Array (Array Nat)) (k x g : Nat)
    (s : Array OE × Array Nat) : Id (ForInStep (Array OE × Array Nat)) :=
  if (decide ((gens[g]!)[x]! < n) && (s.1[(gens[g]!)[x]!]!).1 == 0) = true then
    pure (ForInStep.yield (s.1.set! ((gens[g]!)[x]!) (k, x, g, (s.1[x]!).2.2.2 + 1),
      s.2.push ((gens[g]!)[x]!)))
  else pure (ForInStep.yield (s.1, s.2))

private def qBody (n : Nat) (gens : Array (Array Nat)) (k : Nat) (_ : Nat)
    (s : Array OE × Array Nat × Nat) : Id (ForInStep (Array OE × Array Nat × Nat)) :=
  if s.2.2 < s.2.1.size then do
    let t ← forIn (List.range' 0 gens.size) ((s.1, s.2.1) : Array OE × Array Nat)
      (gBody n gens k (s.2.1[s.2.2]!))
    pure (ForInStep.yield (t.1, t.2, s.2.2 + 1))
  else pure (ForInStep.done (s.1, s.2.1, s.2.2))

private def rBody (n : Nat) (gens : Array (Array Nat)) (r : Nat) (s : Array OE × Nat) :
    Id (ForInStep (Array OE × Nat)) :=
  if (decide (r < n) && (s.1[r]!).1 == 0) = true then do
    let t ← forIn (List.range' 0 n)
      ((s.1.set! r (s.2 + 1, r, 0, 1), #[r], 0) : Array OE × Array Nat × Nat)
      (qBody n gens (s.2 + 1))
    pure (ForInStep.yield (t.1, s.2 + 1))
  else pure (ForInStep.yield (s.1, s.2 + 1))

private theorem orbitCert_eq_loop (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) :
    orbitCert n gens reps = (Id.run (forIn reps
      ((Array.replicate n (0, 0, 0, 0), 0) : Array OE × Nat) (rBody n gens))).1 := by
  unfold orbitCert
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

private def oExt (oc oc' : Array OE) : Prop := ∀ y : Nat, (oc[y]!).1 ≠ 0 → oc'[y]! = oc[y]!

private theorem oext_refl (oc : Array OE) : oExt oc oc := fun _ _ => rfl

private theorem oext_trans {a b c : Array OE} (h1 : oExt a b) (h2 : oExt b c) : oExt a c := by
  intro y hy
  have e1 := h1 y hy
  have hb : (b[y]!).1 ≠ 0 := by rw [e1]; exact hy
  rw [h2 y hb, e1]

private theorem oext_mk {a b : Array OE} (h : oExt a b) {y : Nat} (hy : (a[y]!).1 ≠ 0) :
    (b[y]!).1 ≠ 0 := by
  rw [h y hy]; exact hy

private theorem oext_set {oc : Array OE} {y : Nat} (v : OE) (hy : (oc[y]!).1 = 0) :
    oExt oc (oc.set! y v) := by
  intro z hz
  exact Array.getElem!_set!_ne oc y z v (fun h => hz (h ▸ hy))

private theorem gcond_iff {n : Nat} {oc : Array OE} {y : Nat} :
    (decide (y < n) && (oc[y]!).1 == 0) = true ↔ y < n ∧ (oc[y]!).1 = 0 := by
  simp

private theorem recOK_iff {gens : Array (Array Nat)} {reps : List Nat} {oc : Array OE}
    {w k p g d : Nat} (he : oc[w]! = (k, p, g, d)) :
    orbitRecOK gens reps oc w = true ↔
      (k = 0 ∨ (k ≤ reps.length ∧ 0 < d ∧
        ((d = 1 ∧ w = reps.getD (k - 1) 0) ∨
          (d ≠ 1 ∧ (oc[p]!).1 = k ∧ (oc[p]!).2.2.2 < d ∧ g < gens.size ∧
            (gens[g]!)[p]! = w)))) := by
  simp only [orbitRecOK, he]
  by_cases hd : d = 1
  · subst hd; simp
  · simp [hd, and_assoc]

private theorem recOK_zero {gens : Array (Array Nat)} {reps : List Nat} {oc : Array OE} {w : Nat}
    (h : (oc[w]!).1 = 0) : orbitRecOK gens reps oc w = true := by
  rcases he : oc[w]! with ⟨k, p, g, d⟩
  rw [he] at h
  exact (recOK_iff he).2 (Or.inl h)

private theorem recOK_pos {gens : Array (Array Nat)} {reps : List Nat} {oc : Array OE} {w : Nat}
    (h : orbitRecOK gens reps oc w = true) (hm : (oc[w]!).1 ≠ 0) : 0 < (oc[w]!).2.2.2 := by
  rcases he : oc[w]! with ⟨k, p, g, d⟩
  rw [he] at hm
  rcases (recOK_iff he).1 h with h0 | ⟨-, h1, -⟩
  · exact absurd h0 hm
  · exact h1

private theorem recOK_ext {gens : Array (Array Nat)} {reps : List Nat} {oc oc' : Array OE}
    {w : Nat} (hext : oExt oc oc') (hm : (oc[w]!).1 ≠ 0)
    (h : orbitRecOK gens reps oc w = true) : orbitRecOK gens reps oc' w = true := by
  rcases he : oc[w]! with ⟨k, p, g, d⟩
  have he' : oc'[w]! = (k, p, g, d) := (hext w hm).trans he
  rw [he] at hm
  rcases (recOK_iff he).1 h with h0 | ⟨h1, h2, h3 | ⟨h3, h4, h5, h6, h7⟩⟩
  · exact absurd h0 hm
  · exact (recOK_iff he').2 (Or.inr ⟨h1, h2, Or.inl h3⟩)
  · have hp : (oc[p]!).1 ≠ 0 := by rw [h4]; exact hm
    have hp' : oc'[p]! = oc[p]! := hext p hp
    refine (recOK_iff he').2 (Or.inr ⟨h1, h2, Or.inr ⟨h3, ?_, ?_, h6, h7⟩⟩)
    · rw [hp']; exact h4
    · rw [hp']; exact h5

private theorem recOK_child {gens : Array (Array Nat)} {reps : List Nat} {oc' : Array OE}
    {y x g k d : Nat} (hk : k ≠ 0) (hkl : k ≤ reps.length) (hy : oc'[y]! = (k, x, g, d + 1))
    (hx1 : (oc'[x]!).1 = k) (hx2 : (oc'[x]!).2.2.2 = d) (hd : 0 < d) (hg : g < gens.size)
    (hxy : (gens[g]!)[x]! = y) : orbitRecOK gens reps oc' y = true := by
  refine (recOK_iff hy).2 (Or.inr ⟨hkl, Nat.succ_pos d, Or.inr ⟨by omega, hx1, ?_, hg, hxy⟩⟩)
  rw [hx2]; exact Nat.lt_succ_self d

private theorem recOK_root {gens : Array (Array Nat)} {reps : List Nat} {oc' : Array OE}
    {a k : Nat} (hkl : k ≤ reps.length) (hy : oc'[a]! = (k, a, 0, 1))
    (ha : a = reps.getD (k - 1) 0) : orbitRecOK gens reps oc' a = true :=
  (recOK_iff hy).2 (Or.inr ⟨hkl, Nat.one_pos, Or.inl ⟨rfl, ha⟩⟩)

private def oProc (n : Nat) (gens : Array (Array Nat)) (oc : Array OE) (x : Nat) : Prop :=
  ∀ g : Nat, g < gens.size → (gens[g]!)[x]! < n → (oc[(gens[g]!)[x]!]!).1 ≠ 0

private theorem oProc_mono {n : Nat} {gens : Array (Array Nat)} {oc oc' : Array OE}
    (h : oExt oc oc') {x : Nat} (hp : oProc n gens oc x) : oProc n gens oc' x :=
  fun g hg hy => oext_mk h (hp g hg hy)

private structure OQI (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) (k1 : Nat)
    (oc : Array OE) (queue : Array Nat) (head : Nat) : Prop where
  sz : oc.size = n
  rk : ∀ w, orbitRecOK gens reps oc w = true
  mem : ∀ z ∈ queue.toList, z < n ∧ (oc[z]!).1 = k1
  nd : queue.toList.Nodup
  hle : head ≤ queue.size
  pend : ∀ z, (oc[z]!).1 ≠ 0 → z ∈ queue.toList.drop head ∨ oProc n gens oc z

private theorem oqi_size_le {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {k1 : Nat}
    {oc : Array OE} {queue : Array Nat} {head : Nat}
    (h : OQI n gens reps k1 oc queue head) : queue.size ≤ n := by
  have := h.nd.length_le_of_subset (l₂ := List.range n)
    (fun z hz => List.mem_range.2 (h.mem z hz).1)
  simpa using this

private theorem oqi_push {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {k1 : Nat}
    {oc : Array OE} {queue : Array Nat} {h0 x y g : Nat} (hk : k1 ≠ 0) (hkl : k1 ≤ reps.length)
    (hq : OQI n gens reps k1 oc queue h0) (hx : x ∈ queue.toList)
    (hg : g < gens.size) (hxy : (gens[g]!)[x]! = y) (hy : y < n) (hy0 : (oc[y]!).1 = 0) :
    OQI n gens reps k1 (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1)) (queue.push y) h0 ∧
      oExt oc (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1)) ∧
      ((oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1))[y]!).1 ≠ 0 := by
  have hy_lt : y < oc.size := by rw [hq.sz]; exact hy
  have hxk := hq.mem x hx
  have hxm : (oc[x]!).1 ≠ 0 := by rw [hxk.2]; exact hk
  have hd : 0 < (oc[x]!).2.2.2 := recOK_pos (hq.rk x) hxm
  have hext : oExt oc (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1)) := oext_set _ hy0
  have hyx : y ≠ x := fun h => by rw [h] at hy0; exact hxm hy0
  have hset_y : (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1))[y]! =
      (k1, x, g, (oc[x]!).2.2.2 + 1) := Array.getElem!_set!_self oc y _ hy_lt
  have hset_x : (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1))[x]! = oc[x]! :=
    Array.getElem!_set!_ne oc y x _ hyx
  have hset_ne : ∀ z, y ≠ z → (oc.set! y (k1, x, g, (oc[x]!).2.2.2 + 1))[z]! = oc[z]! :=
    fun z hz => Array.getElem!_set!_ne oc y z _ hz
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hext, by rw [hset_y]; exact hk⟩
  · rw [Array.size_set!, hq.sz]
  · intro w
    by_cases hwy : y = w
    · subst hwy
      exact recOK_child hk hkl hset_y (by rw [hset_x]; exact hxk.2) (by rw [hset_x]) hd hg hxy
    · by_cases h0 : (oc[w]!).1 = 0
      · exact recOK_zero (by rw [hset_ne w hwy]; exact h0)
      · exact recOK_ext hext h0 (hq.rk w)
  · intro z hz
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | rfl
    · obtain ⟨hz1, hz2⟩ := hq.mem z hz
      have hzy : y ≠ z := by
        intro h
        rw [← h, hy0] at hz2
        exact hk hz2.symm
      refine ⟨hz1, ?_⟩
      rw [hset_ne z hzy]; exact hz2
    · exact ⟨hy, by rw [hset_y]⟩
  · rw [Array.toList_push]
    refine List.nodup_append.2 ⟨hq.nd, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    intro hab
    subst hab
    have := (hq.mem _ ha).2
    rw [hy0] at this
    exact hk this.symm
  · rw [Array.size_push]; have := hq.hle; omega
  · intro z hz
    by_cases hzy : y = z
    · subst hzy
      left
      rw [Array.toList_push, List.drop_append_of_le_length (by simpa using hq.hle)]
      simp
    · rw [hset_ne z hzy] at hz
      rcases hq.pend z hz with h | h
      · left
        rw [Array.toList_push, List.drop_append_of_le_length (by simpa using hq.hle)]
        exact List.mem_append_left _ h
      · right
        exact oProc_mono hext h

private theorem gLoop_inv {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {k1 : Nat}
    (hk : k1 ≠ 0) (hkl : k1 ≤ reps.length) {x h0 : Nat} :
    ∀ (m j : Nat) (oc : Array OE) (queue : Array Nat),
      OQI n gens reps k1 oc queue h0 → h0 < queue.size → queue[h0]? = some x →
      (∀ g < j, g < gens.size → (gens[g]!)[x]! < n → (oc[(gens[g]!)[x]!]!).1 ≠ 0) →
      j + m = gens.size →
      ∃ oc' queue', Id.run (forIn (List.range' j m) (oc, queue) (gBody n gens k1 x)) =
          (oc', queue') ∧
        OQI n gens reps k1 oc' queue' h0 ∧ h0 < queue'.size ∧ queue'[h0]? = some x ∧
        oProc n gens oc' x ∧ oExt oc oc' := by
  intro m
  induction m with
  | zero =>
    intro j oc queue hq hh hx hj hjm
    exact ⟨oc, queue, rfl, hq, hh, hx, fun g hg hy => hj g (by omega) hg hy, oext_refl oc⟩
  | succ m ih =>
    intro j oc queue hq hh hx hj hjm
    have hjlt : j < gens.size := by omega
    have hxq : x ∈ queue.toList := Array.mem_toList_iff.2 (Array.mem_of_getElem? hx)
    rw [List.range'_succ, List.forIn_cons]
    by_cases hc : (decide ((gens[j]!)[x]! < n) && (oc[(gens[j]!)[x]!]!).1 == 0) = true
    · obtain ⟨hy, hy0⟩ := gcond_iff.1 hc
      obtain ⟨hq', hext, hmk⟩ := oqi_push hk hkl hq hxq hjlt rfl hy hy0
      have hstep : gBody n gens k1 x j (oc, queue) = pure (ForInStep.yield
          (oc.set! ((gens[j]!)[x]!) (k1, x, j, (oc[x]!).2.2.2 + 1),
            queue.push ((gens[j]!)[x]!))) := by
        simp only [gBody, hc, ↓reduceIte]
      rw [hstep]
      have hh' : h0 < (queue.push ((gens[j]!)[x]!)).size := by rw [Array.size_push]; omega
      have hx' : (queue.push ((gens[j]!)[x]!))[h0]? = some x := by
        rw [Array.getElem?_push, if_neg (by omega)]; exact hx
      have hj' : ∀ g < j + 1, g < gens.size → (gens[g]!)[x]! < n →
          ((oc.set! ((gens[j]!)[x]!) (k1, x, j, (oc[x]!).2.2.2 + 1))[(gens[g]!)[x]!]!).1 ≠ 0 := by
        intro g hg hgs hy'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · exact oext_mk hext (hj g hg hgs hy')
        · rw [hg]; exact hmk
      obtain ⟨oc2, q2, e, h1, h2, h3, h4, h5⟩ := ih (j + 1) _ _ hq' hh' hx' hj' (by omega)
      exact ⟨oc2, q2, e, h1, h2, h3, h4, oext_trans hext h5⟩
    · have hstep : gBody n gens k1 x j (oc, queue) = pure (ForInStep.yield (oc, queue)) := by
        unfold gBody
        exact if_neg hc
      rw [hstep]
      have hj' : ∀ g < j + 1, g < gens.size → (gens[g]!)[x]! < n →
          (oc[(gens[g]!)[x]!]!).1 ≠ 0 := by
        intro g hg hgs hy'
        rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | hg
        · exact hj g hg hgs hy'
        · rw [hg] at hy' ⊢
          exact fun h0 => hc (gcond_iff.2 ⟨hy', h0⟩)
      obtain ⟨oc2, q2, e, h1, h2, h3, h4, h5⟩ := ih (j + 1) oc queue hq hh hx hj' (by omega)
      exact ⟨oc2, q2, e, h1, h2, h3, h4, h5⟩

private theorem oqi_advance {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {k1 : Nat}
    {oc : Array OE} {queue : Array Nat} {head x : Nat}
    (hq : OQI n gens reps k1 oc queue head) (hh : head < queue.size)
    (hx : queue[head]? = some x) (hp : oProc n gens oc x) :
    OQI n gens reps k1 oc queue (head + 1) := by
  refine ⟨hq.sz, hq.rk, hq.mem, hq.nd, hh, fun z hz => ?_⟩
  rcases hq.pend z hz with h | h
  · obtain ⟨hh', hxe⟩ := Array.getElem?_eq_some_iff.1 hx
    have hd : queue.toList.drop head = queue[head] :: queue.toList.drop (head + 1) :=
      List.drop_eq_getElem_cons (by simpa using hh)
    rw [hd, List.mem_cons] at h
    rcases h with h | h
    · rw [h.trans hxe]
      exact Or.inr hp
    · exact Or.inl h
  · exact Or.inr h

private theorem qLoop_inv {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {k1 : Nat}
    (hk : k1 ≠ 0) (hkl : k1 ≤ reps.length) :
    ∀ (l : List Nat) (oc : Array OE) (queue : Array Nat) (head : Nat),
      OQI n gens reps k1 oc queue head → n ≤ head + l.length →
      ∃ oc' queue' head', Id.run (forIn l (oc, queue, head) (qBody n gens k1)) =
          (oc', queue', head') ∧
        OQI n gens reps k1 oc' queue' head' ∧ head' = queue'.size ∧ oExt oc oc' := by
  intro l
  induction l with
  | nil =>
    intro oc queue head hq hn
    refine ⟨oc, queue, head, rfl, hq, ?_, oext_refl oc⟩
    have h1 := oqi_size_le hq
    have h2 := hq.hle
    simp only [List.length_nil] at hn
    omega
  | cons a l ih =>
    intro oc queue head hq hn
    rw [List.forIn_cons]
    by_cases hlt : head < queue.size
    · have hxh : queue[head]? = some queue[head]! :=
        Array.getElem?_eq_some_getElem! queue head hlt
      obtain ⟨oc2, q2, e2, hq2, hh2, hx2, hp2, hext2⟩ :=
        gLoop_inv (x := queue[head]!) (h0 := head) hk hkl gens.size 0 oc queue hq hlt hxh
          (fun g hg => absurd hg (Nat.not_lt_zero g)) (by omega)
      have hstep : qBody n gens k1 a (oc, queue, head) = pure (ForInStep.yield
          ((Id.run (forIn (List.range' 0 gens.size) (oc, queue)
            (gBody n gens k1 queue[head]!))).1,
           (Id.run (forIn (List.range' 0 gens.size) (oc, queue)
            (gBody n gens k1 queue[head]!))).2, head + 1)) := by
        simp only [qBody, hlt, ↓reduceIte] <;> rfl
      rw [hstep, e2]
      obtain ⟨oc3, q3, h3, e3, hq3, hh3, hext3⟩ :=
        ih oc2 q2 (head + 1) (oqi_advance hq2 hh2 hx2 hp2)
          (by simp only [List.length_cons] at hn; omega)
      exact ⟨oc3, q3, h3, e3, hq3, hh3, oext_trans hext2 hext3⟩
    · have hh : head = queue.size := by have := hq.hle; omega
      have hstep : qBody n gens k1 a (oc, queue, head) =
          pure (ForInStep.done (oc, queue, head)) := by
        simp only [qBody, hlt, ↓reduceIte] <;> rfl
      rw [hstep]
      exact ⟨oc, queue, head, rfl, hq, hh, oext_refl oc⟩

private structure OGI (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) (oc : Array OE) :
    Prop where
  sz : oc.size = n
  rk : ∀ w, orbitRecOK gens reps oc w = true
  closed : ∀ x, (oc[x]!).1 ≠ 0 → oProc n gens oc x

private theorem drop_cons_facts {reps : List Nat} {k a : Nat} {l : List Nat}
    (h : reps.drop k = a :: l) : k < reps.length ∧ reps.getD k 0 = a ∧ reps.drop (k + 1) = l := by
  have hk : k < reps.length := by
    rcases Nat.lt_or_ge k reps.length with hk | hk
    · exact hk
    · rw [List.drop_of_length_le hk] at h
      cases h
  rw [List.drop_eq_getElem_cons hk] at h
  obtain ⟨h1, h2⟩ := List.cons.inj h
  refine ⟨hk, ?_, h2⟩
  simp [List.getD_eq_getElem?_getD, hk, h1]

private theorem rLoop_inv {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} :
    ∀ (l : List Nat) (oc : Array OE) (k : Nat), reps.drop k = l → OGI n gens reps oc →
      ∃ oc' k', Id.run (forIn l (oc, k) (rBody n gens)) = (oc', k') ∧
        OGI n gens reps oc' ∧ oExt oc oc' ∧ ∀ z ∈ l, z < n → (oc'[z]!).1 ≠ 0 := by
  intro l
  induction l with
  | nil =>
    intro oc k _ hg
    exact ⟨oc, k, rfl, hg, oext_refl oc, fun z hz => absurd hz List.not_mem_nil⟩
  | cons a l ih =>
    intro oc k hdrop hg
    obtain ⟨hklt, hroot, hdrop'⟩ := drop_cons_facts hdrop
    rw [List.forIn_cons]
    by_cases hc : (decide (a < n) && (oc[a]!).1 == 0) = true
    · obtain ⟨ha_lt, ha0⟩ := gcond_iff.1 hc
      have hk1 : k + 1 ≠ 0 := Nat.succ_ne_zero k
      have hkl1 : k + 1 ≤ reps.length := hklt
      have hsz : a < oc.size := by rw [hg.sz]; exact ha_lt
      have hext1 : oExt oc (oc.set! a (k + 1, a, 0, 1)) := oext_set _ ha0
      have hget_a : (oc.set! a (k + 1, a, 0, 1))[a]! = (k + 1, a, 0, 1) :=
        Array.getElem!_set!_self oc a _ hsz
      have hq0 : OQI n gens reps (k + 1) (oc.set! a (k + 1, a, 0, 1)) #[a] 0 := by
        refine ⟨?_, ?_, ?_, ?_, Nat.zero_le _, ?_⟩
        · rw [Array.size_set!, hg.sz]
        · intro w
          by_cases hwa : a = w
          · subst hwa
            exact recOK_root hkl1 hget_a (by simpa using hroot.symm)
          · by_cases h0 : (oc[w]!).1 = 0
            · exact recOK_zero (by rw [Array.getElem!_set!_ne oc a w _ hwa]; exact h0)
            · exact recOK_ext hext1 h0 (hg.rk w)
        · intro z hz
          have hz' : z = a := by simpa using hz
          subst hz'
          exact ⟨ha_lt, by rw [hget_a]⟩
        · simp
        · intro z hz
          by_cases hza : a = z
          · subst hza
            left
            simp
          · rw [Array.getElem!_set!_ne oc a z _ hza] at hz
            right
            exact oProc_mono hext1 (hg.closed z hz)
      obtain ⟨oc2, q2, h2, e2, hqf, hhf, hext2⟩ :=
        qLoop_inv hk1 hkl1 (List.range' 0 n) _ #[a] 0 hq0 (by simp)
      have hgi : OGI n gens reps oc2 := by
        refine ⟨hqf.sz, hqf.rk, fun x hx => ?_⟩
        rcases hqf.pend x hx with h | h
        · rw [List.drop_of_length_le (by simp [hhf])] at h
          exact absurd h List.not_mem_nil
        · exact h
      obtain ⟨oc3, k3, e3, hg3, hext3, hz3⟩ := ih oc2 (k + 1) hdrop' hgi
      have hstep : rBody n gens a (oc, k) = pure (ForInStep.yield
          ((Id.run (forIn (List.range' 0 n) (oc.set! a (k + 1, a, 0, 1), #[a], 0)
            (qBody n gens (k + 1)))).1, k + 1)) := by
        simp only [rBody, hc, ↓reduceIte] <;> rfl
      refine ⟨oc3, k3, ?_, hg3, oext_trans hext1 (oext_trans hext2 hext3), ?_⟩
      · rw [hstep, e2]
        exact e3
      · intro z hz hzn
        rcases List.mem_cons.1 hz with hza | hz
        · rw [hza]
          have h1 : (oc2[a]!).1 ≠ 0 := by
            have hm : ((oc.set! a (k + 1, a, 0, 1))[a]!).1 ≠ 0 := by rw [hget_a]; exact hk1
            exact oext_mk hext2 hm
          exact oext_mk hext3 h1
        · exact hz3 z hz hzn
    · have hstep : rBody n gens a (oc, k) = pure (ForInStep.yield (oc, k + 1)) := by
        unfold rBody
        exact if_neg hc
      obtain ⟨oc3, k3, e3, hg3, hext3, hz3⟩ := ih oc (k + 1) hdrop' hg
      refine ⟨oc3, k3, ?_, hg3, hext3, ?_⟩
      · rw [hstep]; exact e3
      · intro z hz hzn
        rcases List.mem_cons.1 hz with hza | hz
        · rw [hza] at hzn ⊢
          have : (oc[a]!).1 ≠ 0 := fun h0 => hc (gcond_iff.2 ⟨hzn, h0⟩)
          exact oext_mk hext3 this
        · exact hz3 z hz hzn

private theorem orbitCert_gi (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) :
    OGI n gens reps (orbitCert n gens reps) ∧
      ∀ z ∈ reps, z < n → ((orbitCert n gens reps)[z]!).1 ≠ 0 := by
  have hz : ∀ w : Nat,
      ((Array.replicate n ((0 : Nat), (0 : Nat), (0 : Nat), (0 : Nat)))[w]!).1 = 0 := by
    intro w
    by_cases hw : w < n
    · rw [getElem!_pos _ _ (by simpa using hw)]
      simp
    · rw [getElem!_neg _ _ (by simpa using hw)]
      rfl
  have h0 : OGI n gens reps (Array.replicate n (0, 0, 0, 0)) :=
    ⟨by simp, fun w => recOK_zero (hz w), fun x hx => absurd (hz x) hx⟩
  obtain ⟨oc', k', e, hg, -, hzm⟩ :=
    rLoop_inv reps (Array.replicate n (0, 0, 0, 0)) 0 List.drop_zero h0
  rw [orbitCert_eq_loop, e]
  exact ⟨hg, hzm⟩

theorem orbitCert_size (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) :
    (orbitCert n gens reps).size = n :=
  (orbitCert_gi n gens reps).1.sz

theorem orbitCert_recOK (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) :
    ∀ w < n, orbitRecOK gens reps (orbitCert n gens reps) w = true :=
  fun w _ => (orbitCert_gi n gens reps).1.rk w

theorem orbitCert_rep {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {r : Nat}
    (hr : r ∈ reps) (hrn : r < n) : ((orbitCert n gens reps)[r]!).1 ≠ 0 :=
  (orbitCert_gi n gens reps).2 r hr hrn

theorem orbitCert_closed {n : Nat} {gens : Array (Array Nat)} {reps : List Nat} {x g : Nat}
    (hx : x < n) (hxm : ((orbitCert n gens reps)[x]!).1 ≠ 0) (hg : g < gens.size)
    (hy : (gens[g]!)[x]! < n) : ((orbitCert n gens reps)[(gens[g]!)[x]!]!).1 ≠ 0 :=
  (orbitCert_gi n gens reps).1.closed x hxm g hg hy

theorem colMatch_lt {n : Nat} {c src : Array Nat} {v : Nat} (hv : v < n)
    (h : ∃ w < n, c[w]! = src[v]!) :
    (colMatch n c src)[v]! < n ∧ c[(colMatch n c src)[v]!]! = src[v]! := by
  rw [colMatch_getElem hv]
  exact (cmInv_final n c src[v]!).1 h

theorem colMatch_eq_n {n : Nat} {c src : Array Nat} {v : Nat} (hv : v < n)
    (h : ∀ w < n, c[w]! ≠ src[v]!) : (colMatch n c src)[v]! = n := by
  rw [colMatch_getElem hv]
  exact (cmInv_final n c src[v]!).2 fun ⟨w, hw, e⟩ => h w hw e

end CFSG.KC.Fi22Snd

end
