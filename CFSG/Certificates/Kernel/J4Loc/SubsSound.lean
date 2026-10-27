module

public import CFSG.Certificates.Kernel.J4Loc.TrioSound
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.J4Loc.Native

public section

namespace CFSG.KS.J4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KC.Loop CFSG.Sporadic.J4.QT

theorem xor_xor_cancel (a v : ℕ) : a ^^^ v ^^^ v = a :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases v.testBit i <;> rfl

theorem xor_cancel_xor (a v : ℕ) : a ^^^ (a ^^^ v) = v :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases v.testBit i <;> rfl

theorem xor_xor_right (x y v : ℕ) : x ^^^ (y ^^^ v) = x ^^^ y ^^^ v :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases v.testBit i <;> rfl

theorem xor_xor_left (x y v : ℕ) : x ^^^ v ^^^ y = x ^^^ y ^^^ v :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases v.testBit i <;> rfl

theorem xor_xor_both (x y v : ℕ) : x ^^^ v ^^^ (y ^^^ v) = x ^^^ y :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases x.testBit i <;> cases y.testBit i <;> cases v.testBit i <;> rfl

theorem xor_xor_swap (a b c d : ℕ) : a ^^^ b ^^^ (c ^^^ d) = a ^^^ c ^^^ (b ^^^ d) :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> cases d.testBit i <;> rfl

theorem xorL_eq (v : ℕ) : ∀ l : List ℕ, xorL v l = l.map (· ^^^ v)
  | [] => rfl
  | x :: l => by
    change Nat.xor x v :: xorL v l = (x ^^^ v) :: l.map (· ^^^ v)
    rw [xorL_eq v l]
    rfl

theorem appK_eq (l' : List ℕ) : ∀ l : List ℕ, appK l l' = l ++ l'
  | [] => rfl
  | x :: l => by
    change x :: appK l l' = _
    rw [appK_eq l' l]
    rfl

theorem lenK_len : ∀ l : List ℕ, lenK l = l.length
  | [] => rfl
  | _ :: l => by
    change Nat.succ (lenK l) = _
    rw [lenK_len l]
    rfl

theorem getN_zero_getD : ∀ (l : List ℕ) (i : ℕ), getN 0 l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_zero_getD l i

theorem blkL_eq : ∀ (l : List (List (List ℕ))) (i : ℕ), blkL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => blkL_eq l i

theorem allL_of {f : ℕ → Bool} : ∀ {l : List ℕ}, (∀ x ∈ l, f x = true) → allL l f = true
  | [], _ => rfl
  | x :: l, h => by
    change andB (f x) (allL l f) = true
    rw [h x List.mem_cons_self, allL_of fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem anyK_spec {f : ℕ → Bool} : ∀ {n : ℕ}, anyK n f = true → ∃ i < n, f i = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    rcases orB_true h with h | h
    · exact ⟨n, Nat.lt_succ_self n, h⟩
    · obtain ⟨i, hi, h⟩ := anyK_spec h
      exact ⟨i, by omega, h⟩

theorem eqB_spec {a b : Bool} (h : eqB a b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem subK_spec {a b : ℕ} (h : subK a b = true) : ∀ x, a.testBit x = true → b.testBit x = true := by
  intro x hx
  have e : a &&& b = a := Nat.eq_of_beq_eq_true h
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at hx
  exact hx.2

theorem subK_of {a b : ℕ} (h : ∀ x, a.testBit x = true → b.testBit x = true) : subK a b = true := by
  have e : a &&& b = a := Nat.eq_of_testBit_eq fun x => by
    rw [Nat.testBit_and]
    cases ha : a.testBit x
    · rfl
    · rw [h x ha]
      rfl
  change Nat.beq (a &&& b) a = true
  rw [e]
  exact Nat.beq_refl a

theorem lor_shift_eq (acc x : ℕ) : Nat.lor acc (Nat.shiftLeft 1 x) = acc ||| 2 ^ x := by
  change acc |||1 <<< x = _
  rw [Nat.one_shiftLeft]

theorem nodupFrom_spec : ∀ (l : List ℕ) (acc : ℕ), nodupFrom l acc = true →
    l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: l, acc, h => by
    change andB (notB (bitB acc x)) (nodupFrom l (Nat.lor acc (Nat.shiftLeft 1 x))) = true at h
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨hnd, hl⟩ := nodupFrom_spec l _ h2
    rw [notB_eq, bitB_eq, Bool.not_eq_true'] at h1
    rw [lor_shift_eq] at hl
    refine ⟨List.nodup_cons.2 ⟨fun hx => ?_, hnd⟩, fun y hy => ?_⟩
    · have := hl x hx
      rw [Nat.testBit_or, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact absurd this (by decide)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · have := hl y hy
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

theorem mem_keyK_iff {K : ℕ} {l : List ℕ} (hK : K = keyK l) (x : ℕ) : K.testBit x = true ↔ x ∈ l := by
  rw [hK, mem_keyK]

theorem spanK_nil : spanK [] = [0] := rfl

theorem spanK_cons (v : ℕ) (b : List ℕ) : spanK (v :: b) = spanK b ++ (spanK b).map (· ^^^ v) := by
  change appK (spanK b) (xorL v (spanK b)) = _
  rw [appK_eq, xorL_eq]

theorem mem_spanK_cons {x v : ℕ} {b : List ℕ} :
    x ∈ spanK (v :: b) ↔ x ∈ spanK b ∨ ∃ y ∈ spanK b, y ^^^ v = x := by
  rw [spanK_cons, List.mem_append, List.mem_map]

theorem length_spanK : ∀ b : List ℕ, (spanK b).length = 2 ^ b.length
  | [] => rfl
  | v :: b => by
    rw [spanK_cons, List.length_append, List.length_map, length_spanK b, List.length_cons,
      Nat.pow_succ]
    omega

theorem zero_mem_spanK : ∀ b : List ℕ, 0 ∈ spanK b
  | [] => List.mem_singleton.2 rfl
  | v :: b => mem_spanK_cons.2 (Or.inl (zero_mem_spanK b))

theorem mem_spanK_of_mem : ∀ {b : List ℕ} {v : ℕ}, v ∈ b → v ∈ spanK b
  | [], _, h => absurd h List.not_mem_nil
  | w :: b, v, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_spanK_cons.2 (Or.inr ⟨0, zero_mem_spanK b, Nat.zero_xor v⟩)
    · exact mem_spanK_cons.2 (Or.inl (mem_spanK_of_mem h))

theorem xor_mem_spanK : ∀ {b : List ℕ} {x y : ℕ}, x ∈ spanK b → y ∈ spanK b → x ^^^ y ∈ spanK b
  | [], x, y, hx, hy => by
    rw [spanK_nil, List.mem_singleton] at hx hy ⊢
    rw [hx, hy]
    rfl
  | v :: b, x, y, hx, hy => by
    rcases mem_spanK_cons.1 hx with hx1 | ⟨x', hx1, rfl⟩ <;>
      rcases mem_spanK_cons.1 hy with hy1 | ⟨y', hy1, rfl⟩
    · exact mem_spanK_cons.2 (Or.inl (xor_mem_spanK hx1 hy1))
    · exact mem_spanK_cons.2
        (Or.inr ⟨x ^^^ y', xor_mem_spanK hx1 hy1, (xor_xor_right x y' v).symm⟩)
    · exact mem_spanK_cons.2
        (Or.inr ⟨x' ^^^ y, xor_mem_spanK hx1 hy1, (xor_xor_left x' y v).symm⟩)
    · rw [xor_xor_both]
      exact mem_spanK_cons.2 (Or.inl (xor_mem_spanK hx1 hy1))

theorem spanK_induct {S : ℕ → Prop} (h0 : S 0) (hx : ∀ x y, S x → S y → S (x ^^^ y)) :
    ∀ (b : List ℕ), (∀ v ∈ b, S v) → ∀ c ∈ spanK b, S c
  | [], _, c, hc => by
    rw [spanK_nil, List.mem_singleton] at hc
    rw [hc]
    exact h0
  | v :: b, hb, c, hc => by
    have ih := spanK_induct h0 hx b fun w hw => hb w (List.mem_cons_of_mem _ hw)
    rcases mem_spanK_cons.1 hc with hc | ⟨y, hy, rfl⟩
    · exact ih c hc
    · exact hx _ _ (ih y hy) (hb v List.mem_cons_self)

theorem rowsXor_induct {S : ℕ → Prop} (h0 : S 0) (hx : ∀ x y, S x → S y → S (x ^^^ y))
    (r : ℕ → ℕ) (c : ℕ) : ∀ m, (∀ j < m, S (r j)) → S (rowsXor r m c)
  | 0, _ => by rw [rowsXor_zero]; exact h0
  | m + 1, h => by
    rw [rowsXor_succ]
    refine hx _ _ (rowsXor_induct h0 hx r c m fun j hj => h j (by omega)) ?_
    split_ifs
    · exact h m (Nat.lt_succ_self m)
    · exact h0

theorem unit_induct {S : ℕ → Prop} (h0 : S 0) (hx : ∀ x y, S x → S y → S (x ^^^ y))
    (hu : ∀ j < 11, S (2 ^ j)) {c : ℕ} (hc : c < 2048) : S c := by
  have e : rowsXor (fun j => 2 ^ j) 11 c = c := by
    rw [rowsXor_pow_two, Nat.mod_eq_of_lt (by simpa using hc)]
  rw [← e]
  exact rowsXor_induct h0 hx _ c 11 hu

theorem mem_foldl_span (x : ℕ) : ∀ (b acc : List ℕ),
    x ∈ b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc ↔
      ∃ a ∈ acc, ∃ y ∈ spanK b, x = a ^^^ y
  | [], acc => by
    simp only [List.foldl_nil, spanK_nil, List.mem_singleton, exists_eq_left, Nat.xor_zero]
    exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨a, ha, e⟩ => e ▸ ha⟩
  | v :: b, acc => by
    rw [List.foldl_cons, mem_foldl_span x b]
    constructor
    · rintro ⟨a', ha', y, hy, rfl⟩
      rcases List.mem_append.1 ha' with ha' | ha'
      · exact ⟨a', ha', y, mem_spanK_cons.2 (Or.inl hy), rfl⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
        refine ⟨a, ha, y ^^^ v, mem_spanK_cons.2 (Or.inr ⟨y, hy, rfl⟩), ?_⟩
        rw [xor_xor_left, Nat.xor_assoc]
    · rintro ⟨a, ha, y, hy, rfl⟩
      rcases mem_spanK_cons.1 hy with hy | ⟨y', hy', rfl⟩
      · exact ⟨a, List.mem_append_left _ ha, y, hy, rfl⟩
      · refine ⟨a ^^^ v, List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩), y', hy', ?_⟩
        rw [xor_xor_left, Nat.xor_assoc]

theorem length_foldl_span : ∀ (b acc : List ℕ),
    (b.foldl (fun acc v => acc ++ acc.map (· ^^^ v)) acc).length = acc.length * 2 ^ b.length
  | [], acc => by simp
  | v :: b, acc => by
    rw [List.foldl_cons, length_foldl_span b, List.length_append, List.length_map,
      List.length_cons, Nat.pow_succ]
    ring

theorem nodup_of_mem_length {l l' : List ℕ} (hl' : l'.Nodup) (hmem : ∀ x, x ∈ l ↔ x ∈ l')
    (hlen : l.length = l'.length) : l.Nodup := by
  classical
  have e : l.toFinset = l'.toFinset := by
    ext x
    simp only [List.mem_toFinset, hmem]
  have h1 : l.dedup.length = l.length := by
    rw [← List.card_toFinset, e, List.toFinset_card_of_nodup hl', hlen]
  rw [← List.Sublist.eq_of_length (List.dedup_sublist l) h1]
  exact List.nodup_dedup l

theorem spanS_spec (b : List ℕ) :
    (∀ x, x ∈ CFSG.Quasithin.J4Loc.spanS b ↔ x ∈ spanK b) ∧
      (CFSG.Quasithin.J4Loc.spanS b).length = 2 ^ b.length ∧
      ((spanK b).Nodup → (CFSG.Quasithin.J4Loc.spanS b).Pairwise (· < ·)) := by
  have hmem : ∀ x, x ∈ CFSG.Quasithin.J4Loc.spanS b ↔ x ∈ spanK b := by
    intro x
    unfold CFSG.Quasithin.J4Loc.spanS CFSG.Quasithin.J4Loc.srt
    rw [List.mem_mergeSort, mem_foldl_span]
    simp
  have hlen : (CFSG.Quasithin.J4Loc.spanS b).length = 2 ^ b.length := by
    unfold CFSG.Quasithin.J4Loc.spanS CFSG.Quasithin.J4Loc.srt
    rw [List.length_mergeSort, length_foldl_span]
    simp
  refine ⟨hmem, hlen, fun hnd => ?_⟩
  have hnd' := nodup_of_mem_length hnd hmem (by rw [hlen, length_spanK])
  have hle : (CFSG.Quasithin.J4Loc.spanS b).Pairwise (fun a c => decide (a ≤ c) = true) := by
    unfold CFSG.Quasithin.J4Loc.spanS CFSG.Quasithin.J4Loc.srt
    exact List.pairwise_mergeSort (fun a c d h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a c => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _
  exact (hle.and hnd').imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (of_decide_eq_true h1) h2

theorem subOK_spec {SB : List (List ℕ)} {SBK : List ℕ} {KT KIT : List (List ℕ)} {b : ℕ}
    (h : subOK SB SBK KT KIT b = true) :
    getN 0 SBK b = keyK (spanK (rowL SB b)) ∧ (spanK (rowL SB b)).Nodup ∧
      ∀ v ∈ rowL SB b, ∀ i < 4, actK (rowL KT i) v ∈ spanK (rowL SB b) ∧
        actK (rowL KIT i) v ∈ spanK (rowL SB b) := by
  unfold subOK at h
  rw [strictB_eq] at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  have hK : getN 0 SBK b = keyK (spanK (rowL SB b)) := Nat.eq_of_beq_eq_true h1
  refine ⟨hK, (nodupFrom_spec _ 0 h2).1, fun v hv i hi => ?_⟩
  obtain ⟨h5, h6⟩ := andB_true (allR_spec (allL_spec h3 v hv) i hi)
  rw [bitB_eq, mem_keyK_iff hK] at h5 h6
  exact ⟨h5, h6⟩

theorem chainOK_spec {SB : List (List ℕ)} {SBK : List ℕ} {KT : List (List ℕ)} {m b : ℕ}
    (h : chainOK SB SBK KT m b = true) {v : ℕ} (hv : v < 2048)
    (hvK : (getN 0 SBK b).testBit v = false)
    (hfix : ∀ i < 4, (getN 0 SBK b).testBit (actK (rowL KT i) v ^^^ v) = true) :
    ∃ T < m, (∀ x, (getN 0 SBK b).testBit x = true → (getN 0 SBK T).testBit x = true) ∧
      (getN 0 SBK T).testBit v = true ∧ (rowL SB T).length = (rowL SB b).length + 1 := by
  unfold chainOK at h
  rw [strictB_eq, strictB_eq] at h
  have h1 := CFSG.KS.allN_spec h v hv
  rcases orB_true h1 with h2 | h2
  · rw [bitB_eq, hvK] at h2
    exact absurd h2 Bool.false_ne_true
  rcases orB_true h2 with h3 | h3
  · have hall : allR 4 (fun i => bitB (getN 0 SBK b) (Nat.xor (actK (rowL KT i) v) v)) = true := by
      rw [allR_eq, List.all_eq_true]
      intro i hi
      rw [bitB_eq]
      exact hfix i (List.mem_range.1 hi)
    rw [notB_eq, hall] at h3
    exact absurd h3 Bool.false_ne_true
  obtain ⟨T, hT, h4⟩ := anyK_spec h3
  obtain ⟨h5, h6⟩ := andB_true h4
  obtain ⟨h6, h7⟩ := andB_true h6
  refine ⟨T, hT, subK_spec h5, by rw [← bitB_eq]; exact h6, ?_⟩
  rw [← lenK_len, ← lenK_len]
  exact Nat.eq_of_beq_eq_true h7

theorem partner_eq {S S' : Finset ℕ} {v : ℕ} (hS : ∀ x ∈ S, ∀ y ∈ S, x ^^^ y ∈ S) (hvS : v ∉ S)
    (hsub : S ⊆ S') (hv : v ∈ S') (hS' : ∀ x ∈ S', ∀ y ∈ S', x ^^^ y ∈ S')
    (hc : S'.card ≤ 2 * S.card) : ∀ y ∈ S', y ∈ S ∨ ∃ x ∈ S, y = x ^^^ v := by
  classical
  have hU : S ∪ S.image (· ^^^ v) ⊆ S' := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact hsub hy
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      exact hS' x (hsub hx) v hv
  have hdisj : Disjoint S (S.image (· ^^^ v)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
    apply hvS
    have := hS x hx _ hy
    rwa [xor_cancel_xor] at this
  have hinj : (S.image (· ^^^ v)).card = S.card :=
    Finset.card_image_of_injective _ fun a c h => by
      have := congrArg (· ^^^ v) h
      simpa only [xor_xor_cancel] using this
  have hcard : S'.card ≤ (S ∪ S.image (· ^^^ v)).card := by
    rw [Finset.card_union_of_disjoint hdisj, hinj]
    omega
  have heq := Finset.eq_of_subset_of_card_le hU hcard
  intro y hy
  rw [← heq] at hy
  rcases Finset.mem_union.1 hy with hy | hy
  · exact Or.inl hy
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Or.inr ⟨x, hx, rfl⟩

theorem actT_lin (t : List ℕ) (x y : ℕ) : actT t (x ^^^ y) ^^^ (x ^^^ y) =
    (actT t x ^^^ x) ^^^ (actT t y ^^^ y) := by
  rw [actT_xor, xor_xor_swap]

theorem actT_mem_spanK {t b : List ℕ} (h : ∀ v ∈ b, actT t v ∈ spanK b) :
    ∀ c ∈ spanK b, actT t c ∈ spanK b := by
  have h0 : actT t 0 ∈ spanK b := by
    rw [actT_zero]
    exact zero_mem_spanK b
  exact spanK_induct (S := fun c => actT t c ∈ spanK b) h0
    (fun x y (hx : actT t x ∈ spanK b) (hy : actT t y ∈ spanK b) =>
      (by rw [actT_xor]; exact xor_mem_spanK hx hy : actT t (x ^^^ y) ∈ spanK b)) b h

theorem compT_self_iff {t : List ℕ} (ht : t.length = 11) :
    compT t t = idT ↔ ∀ j < 11, actT t (t.getD j 0) = 2 ^ j := by
  constructor
  · intro h j hj
    have : (compT t t).getD j 0 = idT.getD j 0 := by rw [h]
    rw [getD_compT, idT_getD hj] at this
    exact this
  · intro h
    apply List.ext_getElem
    · simp [compT, idT, ht]
    · intro j h1 h2
      have hj : j < 11 := by simpa [compT, ht] using h1
      rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2, getD_compT, idT_getD hj,
        h j hj]

theorem invK_iff {t : List ℕ} (ht : t.length = 11) : invK t = true ↔ compT t t = idT := by
  rw [compT_self_iff ht]
  constructor
  · intro h j hj
    have e := Nat.eq_of_beq_eq_true (allR_spec h j hj)
    rw [getN_zero_getD, actK_eq_actT ht] at e
    rw [e]
    exact Nat.one_shiftLeft j
  · intro h
    rw [invK, allR_eq, List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [getN_zero_getD, actK_eq_actT ht, h j hj']
    have e : Nat.shiftLeft 1 j = 2 ^ j := Nat.one_shiftLeft j
    rw [e]
    exact Nat.beq_refl _

theorem inBK_iff {t b : List ℕ} {K : ℕ} (ht : t.length = 11)
    (hK : ∀ x, K.testBit x = true ↔ x ∈ spanK b) :
    inBK t b K = true ↔ (∀ c ∈ spanK b, actT t c = c) ∧ ∀ c < 2048, actT t c ^^^ c ∈ spanK b := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := andB_true h
    have hfix : ∀ c ∈ spanK b, actT t c = c :=
      spanK_induct (S := fun c => actT t c = c) (actT_zero t)
        (fun x y (hx : actT t x = x) (hy : actT t y = y) =>
          (by rw [actT_xor, hx, hy] : actT t (x ^^^ y) = x ^^^ y)) b
        (fun v hv => by
          have := Nat.eq_of_beq_eq_true (allL_spec h1 v hv)
          rwa [actK_eq_actT ht] at this)
    refine ⟨hfix, fun c hc => ?_⟩
    have hu : ∀ j < 11, actT t (2 ^ j) ^^^ 2 ^ j ∈ spanK b := by
      intro j hj
      have := allR_spec h2 j hj
      rw [bitB_eq, hK, actK_eq_actT ht] at this
      have e : Nat.shiftLeft 1 j = 2 ^ j := Nat.one_shiftLeft j
      rw [e] at this
      exact this
    have h0 : actT t 0 ^^^ 0 ∈ spanK b := by
      rw [actT_zero]
      exact zero_mem_spanK b
    exact unit_induct (S := fun c => actT t c ^^^ c ∈ spanK b) h0
      (fun x y (hx : actT t x ^^^ x ∈ spanK b) (hy : actT t y ^^^ y ∈ spanK b) =>
        (by rw [actT_lin]; exact xor_mem_spanK hx hy : actT t (x ^^^ y) ^^^ (x ^^^ y) ∈ spanK b))
      hu hc
  · rintro ⟨h1, h2⟩
    change andB (allL b fun v => Nat.beq (actK t v) v)
      (allR 11 fun j => bitB K (Nat.xor (actK t (Nat.shiftLeft 1 j)) (Nat.shiftLeft 1 j))) = true
    have e : ∀ j, Nat.shiftLeft 1 j = 2 ^ j := fun j => Nat.one_shiftLeft j
    have hl : allL b (fun v => Nat.beq (actK t v) v) = true := allL_of fun v hv => by
      rw [actK_eq_actT ht, h1 v (mem_spanK_of_mem hv)]
      exact Nat.beq_refl v
    rw [hl, allR_eq]
    refine List.all_eq_true.2 fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [bitB_eq, hK, actK_eq_actT ht, e]
    exact h2 _ (Nat.pow_lt_pow_right (by decide) hj')

theorem strictN_eq_loop (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem rec_count_eq (q : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => ℕ) 0
    (fun e acc => strictN acc fun a => Bool.rec (motive := fun _ => ℕ) a (Nat.succ a) (q e)) n =
      ((List.range n).filter q).length
  | 0 => rfl
  | n + 1 => by
    change strictN (Nat.rec (motive := fun _ => ℕ) 0
      (fun e acc => strictN acc fun a => Bool.rec (motive := fun _ => ℕ) a (Nat.succ a) (q e)) n)
      (fun a => Bool.rec (motive := fun _ => ℕ) a (Nat.succ a) (q n)) = _
    rw [strictN_eq_loop, rec_count_eq q n, List.range_succ, List.filter_append, List.length_append]
    cases h : q n <;> simp [h]

set_option maxRecDepth 100000 in
theorem cntK_eq (TLB : List (List (List ℕ))) (IV : ℕ) (B : List ℕ) (K : ℕ) :
    cntK TLB IV B K =
      ((List.range 1024).filter fun e => andB (bitB IV e) (inBK (tabK TLB e) B K)).length := by
  have h := rec_count_eq (fun e => andB (bitB IV e) (inBK (tabK TLB e) B K)) (nat_lit 1024)
  exact h

theorem tabK_eq (TLB : List (List (List ℕ))) (e : ℕ) :
    tabK TLB e = (TLB.getD (e / 32) []).getD (e % 32) [] := by
  unfold tabK
  rw [rowL_eq, blkL_eq]
  rfl

theorem xOK_spec {SB : List (List ℕ)} {SBK : List ℕ} {TLB : List (List (List ℕ))} {IV TK N I0 b : ℕ}
    (h : xOK SB SBK TLB IV TK N I0 b = true) (hn : 4 ≤ (rowL SB b).length) :
    8 * cntK TLB IV (rowL SB b) (getN 0 SBK b) ≤ 2 ^ (rowL SB b).length ∧
      (8 * cntK TLB IV (rowL SB b) (getN 0 SBK b) = 2 ^ (rowL SB b).length →
        onlyIn TK N I0 (getN 0 SBK b) = true) := by
  unfold xOK at h
  rw [strictB_eq, strictB_eq] at h
  rw [← lenK_len] at hn ⊢
  rcases orB_true h with h1 | h1
  · have : lenK (rowL SB b) < 4 := lt_of_blt h1
    omega
  rw [strictB_eq] at h1
  obtain ⟨h2, h3⟩ := andB_true h1
  have e : Nat.shiftLeft 1 (lenK (rowL SB b)) = 2 ^ lenK (rowL SB b) := Nat.one_shiftLeft _
  rw [e] at h2 h3
  refine ⟨Nat.le_of_ble_eq_true h2, fun heq => ?_⟩
  rcases orB_true h3 with h4 | h4
  · rw [notB_eq, Bool.not_eq_true'] at h4
    exact absurd heq (Nat.ne_of_beq_eq_false h4)
  · exact h4

theorem onlyIn_spec {TK N I0 K : ℕ} (h : onlyIn TK N I0 K = true) {i : ℕ} (hi : i < N)
    (hsub : ∀ x ∈ octL (fld 80 TK i), K.testBit x = true) : i = I0 := by
  rcases orB_true (CFSG.KS.allN_spec h i hi) with h1 | h1
  · rw [notB_eq, subK_of fun x hx => hsub x ((mem_keyK x _).1 hx)] at h1
    exact absurd h1 Bool.false_ne_true
  · exact Nat.eq_of_beq_eq_true h1

theorem onlyAbove_spec {TK N I0 K : ℕ} (h : onlyAbove TK N I0 K = true) {i : ℕ} (hi : i < N)
    (hsub : ∀ x, K.testBit x = true → x ∈ octL (fld 80 TK i)) : i = I0 := by
  rcases orB_true (CFSG.KS.allN_spec h i hi) with h1 | h1
  · rw [notB_eq, subK_of fun x hx => (mem_keyK x _).2 (hsub x hx)] at h1
    exact absurd h1 Bool.false_ne_true
  · exact Nat.eq_of_beq_eq_true h1

theorem aboveOK_spec {SB : List (List ℕ)} {SBK : List ℕ} {TK N I0 b : ℕ}
    (h : aboveOK SB SBK TK N I0 b = true) (hn : 2 ≤ (rowL SB b).length) :
    onlyAbove TK N I0 (getN 0 SBK b) = true := by
  rcases orB_true h with h1 | h1
  · have : lenK (rowL SB b) < 2 := lt_of_blt h1
    rw [lenK_len] at this
    omega
  · exact h1

end CFSG.KS.J4Loc

end
