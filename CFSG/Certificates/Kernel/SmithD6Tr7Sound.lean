module

public import Certificates.Data.Kernel.SmithD6.Tr7K
public import CFSG.Certificates.Kernel.SmithD6IdSound
public import CFSG.Certificates.Kernel.PkTreeSound
public import CFSG.GF2Type.SmithTypeE.E7.TrCode

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KC.PkTree CFSG.GF2Type.SmithTypeE.DMod
  CFSG.GF2Type.SmithTypeE.E7

theorem lineOf_eq_pairK (x y : ℕ) : lineOf x y = lineIdx (tr7PairK x y).1 (tr7PairK x y).2 := rfl

theorem tvImg_eq (r a : ℕ) :
    tvImg r a = lineIdx (tr7PairImg (linePair r) (linePair a)).1
      (tr7PairImg (linePair r) (linePair a)).2 := rfl

section Lines

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
  lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hL

theorem tr7Line_facts {q : ℕ × ℕ} (h : tr7LineOK q = true) :
    lineIdx q.1 q.2 < 365211 ∧ linePair (lineIdx q.1 q.2) = q := by
  unfold tr7LineOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact hL _ _ h1 h2 h3

theorem tr7ImgsOK_sound : ∀ (ps : List (ℕ × ℕ)) (q : ℕ × ℕ), tr7ImgsOK ps q = true →
    (ps.map fun p => lineOf p.1 p.2).foldr (fun r acc => tvImg r acc) (lineIdx q.1 q.2) =
      lineIdx (tr7ImgChain ps q).1 (tr7ImgChain ps q).2 ∧ tr7LineOK (tr7ImgChain ps q) = true
  | [], q, h => ⟨rfl, by simpa [tr7ImgsOK, tr7ImgChain] using h⟩
  | p :: ps, q, h => by
    simp only [tr7ImgsOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨ih1, ih2⟩ := tr7ImgsOK_sound ps q h1
    refine ⟨?_, h3⟩
    rw [List.map_cons, List.foldr_cons, ih1, tvImg_eq, lineOf_eq_pairK,
      (tr7Line_facts hL h2).2, (tr7Line_facts hL ih2).2]
    rfl

theorem tr7RepImg_fix {j x y : ℕ} (h : tr7ImgOK (tr7RepLines j) (tr7PairK x y) = true) :
    tr7RepImg j (lineOf x y) = lineOf x y := by
  unfold tr7ImgOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have e := (tr7ImgsOK_sound hL _ _ h.1).1
  unfold tr7RepImg tr7RepIdx
  rw [lineOf_eq_pairK, e, h.2]

end Lines

theorem size_tr7Comp' (A B : Array ℕ) : (tr7Comp A B).size = 32 := by simp [tr7Comp]

theorem size_tr7IdCols' : tr7IdCols.size = 32 := by simp [tr7IdCols]

theorem size_foldr_cols' (L : List ℕ) :
    (L.foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols).size = 32 := by
  cases L with
  | nil => exact size_tr7IdCols'
  | cons k L => exact size_tr7Comp' _ _

theorem tr7Comp_getElem' (A B : Array ℕ) (m : Fin 32) :
    (tr7Comp A B)[m.val]! = applyCols A B[m.val]! := by
  unfold tr7Comp
  rw [getElem!_pos _ m.val (by simp), Array.getElem_ofFn]
  rfl

theorem tr7IdCols_getElem' (m : Fin 32) : tr7IdCols[m.val]! = 2 ^ m.val := by
  unfold tr7IdCols
  rw [getElem!_pos _ m.val (by simp), Array.getElem_ofFn]

theorem colsLin_tr7Comp' (A B : Array ℕ) (hA : A.size = 32) :
    colsLin (tr7Comp A B) = colsLin A ∘ₗ colsLin B := by
  refine linearMap_ext_single fun m => ?_
  rw [colsLin_single, LinearMap.comp_apply, colsLin_single, ← decode32_applyCols hA,
    tr7Comp_getElem']

theorem colsLin_tr7IdCols' : colsLin tr7IdCols = LinearMap.id := by
  refine linearMap_ext_single fun m => ?_
  rw [colsLin_single, LinearMap.id_apply, tr7IdCols_getElem', decode32_two_pow]

theorem decode32_applyCols_comp' (A B : Array ℕ) (hA : A.size = 32) (hB : B.size = 32) (x : ℕ) :
    decode32 (applyCols (tr7Comp A B) x) = decode32 (applyCols A (applyCols B x)) := by
  rw [decode32_applyCols (size_tr7Comp' A B), colsLin_tr7Comp' A B hA, LinearMap.comp_apply,
    decode32_applyCols hA, decode32_applyCols hB]

theorem foldr_cols_lt (L : List ℕ) {c : ℕ} (hc : c < 32) :
    (L.foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols)[c]! < 2 ^ 32 := by
  cases L with
  | nil =>
    rw [List.foldr_nil, tr7IdCols_getElem' ⟨c, hc⟩]
    exact Nat.pow_lt_pow_right (by norm_num) hc
  | cons k L =>
    rw [List.foldr_cons, tr7Comp_getElem' _ _ ⟨c, hc⟩]
    exact applyCols_tvCols_lt _ _

theorem applyCols_lt' {cols : Array ℕ} (hs : cols.size = 32) (h : ∀ c < 32, cols[c]! < 2 ^ 32)
    (x : ℕ) : applyCols cols x < 2 ^ 32 := by
  unfold applyCols
  exact foldl_applyCols_lt _ _ (fun m hm => h m (by rw [hs] at hm; exact hm)) _ le_rfl 0
    (by norm_num)

theorem applyCols_foldr_lt (L : List ℕ) (x : ℕ) :
    applyCols (L.foldr (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols) x < 2 ^ 32 :=
  applyCols_lt' (size_foldr_cols' L) (fun _ hc => foldr_cols_lt L hc) x

theorem applyCols_two_pow' {cols : Array ℕ} (hs : cols.size = 32)
    (h : ∀ c < 32, cols[c]! < 2 ^ 32) (m : Fin 32) : applyCols cols (2 ^ m.val) = cols[m.val]! := by
  apply eq_of_decode32_eq (applyCols_lt' hs h _) (h m.val m.2)
  rw [decode32_applyCols hs, decode32_two_pow, colsLin_single]

theorem tr7Lift_eq {k : ℕ} {q : ℕ × ℕ} {x : ℕ} (hl : linePair k = q)
    (h : id7VecOK q.1 q.2 x = true) (hx : x < 2 ^ 32) : tr7Lift q x = applyCols (tvCols k) x := by
  unfold tr7Lift
  rw [id7Vec_eq (u := q.1) (w := q.2) (by rw [hl]) h hx, Nat.xor_comm (applyCols _ _) x,
    ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

section Lines

variable (hL : ∀ u w, u < 4096 → w < 4096 → lineTree.memB (4096 * u + w) = true →
  lineIdx u w < 365211 ∧ linePair (lineIdx u w) = (u, w))
include hL

theorem tr7Chain_eq : ∀ (ps : List (ℕ × ℕ)) (x : ℕ), tr7ChainOK ps x = true → x < 2 ^ 32 →
    applyCols ((ps.map fun p => lineOf p.1 p.2).foldr (fun k acc => tr7Comp (tvCols k) acc)
      tr7IdCols) x = tr7Chain ps x
  | [], x, _, hx => by
    apply eq_of_decode32_eq (applyCols_foldr_lt [] x) hx
    rw [List.foldr_nil, decode32_applyCols size_tr7IdCols', colsLin_tr7IdCols']
    rfl
  | p :: ps, x, h, hx => by
    simp only [tr7ChainOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have ih := tr7Chain_eq ps x h1 hx
    have hl : linePair (lineOf p.1 p.2) = tr7PairK p.1 p.2 := (tr7Line_facts hL h2).2
    have hcl : tr7Chain ps x < 2 ^ 32 := ih ▸ applyCols_foldr_lt _ x
    have hR : tr7Chain (p :: ps) x = applyCols (tvCols (lineOf p.1 p.2)) (tr7Chain ps x) :=
      tr7Lift_eq hl h3 hcl
    apply eq_of_decode32_eq (applyCols_foldr_lt _ x) (by rw [hR]; exact applyCols_tvCols_lt _ _)
    rw [hR, List.map_cons, List.foldr_cons,
      decode32_applyCols_comp' _ _ (tvCols_size _) (size_foldr_cols' _), ih]

theorem tr7Cols32_eq {j : ℕ} (h : tr7RepOK j = true) : tr7Cols32 j = tr7ColsK j := by
  unfold tr7Cols32 tr7ColsK
  refine List.map_congr_left fun c hc => ?_
  have hc' := List.mem_range.1 hc
  congr 1
  have e : tr7RepCols j = ((tr7RepLines j).map fun p => lineOf p.1 p.2).foldr
      (fun k acc => tr7Comp (tvCols k) acc) tr7IdCols := rfl
  rw [e, ← applyCols_two_pow' (size_foldr_cols' _) (fun _ hc => foldr_cols_lt _ hc) ⟨c, hc'⟩]
  exact tr7Chain_eq hL _ _ (List.all_eq_true.1 h c hc) (Nat.pow_lt_pow_right (by norm_num) hc')

theorem tr7RepCols_apply {j x : ℕ} (h : tr7ChainOK (tr7RepLines j) x = true) (hx : x < 2 ^ 32) :
    applyCols (tr7RepCols j) x = tr7Chain (tr7RepLines j) x :=
  tr7Chain_eq hL _ _ h hx

end Lines

theorem xor_mod_two' (a b : ℕ) : (a ^^^ b) % 2 = (a % 2 + b % 2) % 2 := by
  have h := Nat.testBit_xor a b 0
  simp only [Nat.testBit_zero] at h
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one (a ^^^ b) with hc | hc <;> simp_all

theorem xor_div_two' (a b : ℕ) : (a ^^^ b) / 2 = a / 2 ^^^ b / 2 := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two, Nat.testBit_xor]

theorem tr7XorSel_zero : ∀ bs : List ℕ, tr7XorSel bs 0 = 0
  | [] => rfl
  | b :: bs => by rw [tr7XorSel_cons, tr7XorSel_zero bs]; simp

theorem xor_xor_xor_comm (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b, Nat.xor_comm b c, Nat.xor_assoc c, ← Nat.xor_assoc]

theorem tr7XorSel_xor : ∀ (bs : List ℕ) (a b : ℕ),
    tr7XorSel bs (a ^^^ b) = tr7XorSel bs a ^^^ tr7XorSel bs b
  | [], _, _ => by simp only [tr7XorSel_nil, Nat.xor_self]
  | x :: bs, a, b => by
    rw [tr7XorSel_cons, tr7XorSel_cons, tr7XorSel_cons, xor_div_two', tr7XorSel_xor bs,
      xor_xor_xor_comm, xor_mod_two']
    congr 1
    rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]

theorem tr7XorSel_comp (bs : List ℕ) : ∀ (M : List ℕ) (m : ℕ),
    tr7XorSel bs (tr7XorSel M m) = tr7XorSel (M.map (tr7XorSel bs)) m
  | [], _ => tr7XorSel_zero bs
  | r :: M, m => by
    rw [tr7XorSel_cons, List.map_cons, tr7XorSel_cons, tr7XorSel_xor, tr7XorSel_comp bs M]
    congr 1
    split
    · rfl
    · exact tr7XorSel_zero bs

theorem decode32_xorSel_map {f : ℕ → ℕ} {L : V →ₗ[ZMod 2] V} :
    ∀ (bs : List ℕ), (∀ b ∈ bs, decode32 (f b) = L (decode32 b)) → ∀ m,
      decode32 (tr7XorSel (bs.map f) m) = L (decode32 (tr7XorSel bs m))
  | [], _, m => by
    rw [List.map_nil, tr7XorSel_nil, decode32_zero, map_zero]
  | b :: bs, h, m => by
    rw [List.map_cons, tr7XorSel_cons, tr7XorSel_cons, decode32_xor, decode32_xor, map_add,
      decode32_xorSel_map bs (fun x hx => h x (List.mem_cons_of_mem _ hx)) (m / 2)]
    congr 1
    split
    · exact h b (List.mem_cons_self ..)
    · rw [decode32_zero, map_zero]

theorem map_eq_of_zip_all {P : ℕ → ℕ → Bool} {f g : ℕ → ℕ}
    (hP : ∀ b r, P b r = true → g r = f b) :
    ∀ (bs M : List ℕ), M.length = bs.length → (bs.zip M).all (fun e => P e.1 e.2) = true →
      M.map g = bs.map f
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: bs, r :: M, h, hall => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hall
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.map_cons, List.map_cons, hP b r hall.1, map_eq_of_zip_all hP bs M h hall.2]

theorem tr7Mat_mem {k : ℕ} {q : ℕ × ℕ} {bs M : List ℕ} (hl : linePair k = q)
    (h : tr7MatOK q bs M = true) {U : Submodule (ZMod 2) V}
    (hU : ∀ c, decode32 c ∈ U → decode32 (applyCols (tvCols k) c) ∈ U) (m : ℕ)
    (hm : decode32 (tr7XorSel bs m) ∈ U) : decode32 (tr7XorSel bs (tr7XorSel M m)) ∈ U := by
  unfold tr7MatOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  have hmap : M.map (tr7XorSel bs) = bs.map (applyCols (tvCols k)) := by
    refine map_eq_of_zip_all (P := fun b r => decide (b < 2 ^ 32) && id7VecOK q.1 q.2 b &&
      tr7XorSel bs r == tr7Lift q b) (fun b r hb => ?_) bs M hlen hall
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hb
    rw [hb.2, tr7Lift_eq hl hb.1.2 hb.1.1]
  rw [tr7XorSel_comp, hmap, decode32_xorSel_map (L := colsLin (tvCols k)) bs
    (fun b _ => decode32_applyCols (tvCols_size k) b), ← decode32_applyCols (tvCols_size k)]
  exact hU _ hm

section Forest

variable {bs : List ℕ} {Ms : List (List ℕ)} {U : Submodule (ZMod 2) V}
  (hM : ∀ g < Ms.length, ∀ m, decode32 (tr7XorSel bs m) ∈ U →
    decode32 (tr7XorSel bs (tr7XorSel (Ms.getD g []) m)) ∈ U)
include hM

omit hM in
theorem tr7RedK_mem : ∀ (E : List ℕ) (x : ℕ), (∀ b ∈ E, decode32 (tr7XorSel bs b) ∈ U) →
    (decode32 (tr7XorSel bs (tr7RedK E x)) ∈ U ↔ decode32 (tr7XorSel bs x) ∈ U)
  | [], _, _ => Iff.rfl
  | b :: E, x, h => by
    have hb := h b (List.mem_cons_self ..)
    have e : tr7RedK (b :: E) x = tr7RedK E (min x (x ^^^ b)) := rfl
    rw [e, tr7RedK_mem E _ (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    rcases le_total x (x ^^^ b) with hx | hx
    · rw [min_eq_left hx]
    · rw [min_eq_right hx, tr7XorSel_xor, decode32_xor]
      exact U.add_mem_iff_left hb

omit hM in
theorem mem_tr7Ins {r v : ℕ} : ∀ E : List ℕ, v ∈ tr7Ins r E → v = r ∨ v ∈ E
  | [], h => Or.inl (List.mem_singleton.1 h)
  | b :: E, h => by
    unfold tr7Ins at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inr (List.mem_cons.2 (Or.inl h))
      · rcases mem_tr7Ins E h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

omit hM in
theorem foldl_tr7Add_mem : ∀ (L S : List ℕ), (∀ v ∈ S, decode32 (tr7XorSel bs v) ∈ U) →
    (∀ v ∈ L, decode32 (tr7XorSel bs v) ∈ U) →
    ∀ v ∈ L.foldl tr7Add S, decode32 (tr7XorSel bs v) ∈ U
  | [], _, hS, _ => hS
  | w :: L, S, hS, hL => by
    rw [List.foldl_cons]
    refine foldl_tr7Add_mem L _ ?_ (fun v hv => hL v (List.mem_cons_of_mem _ hv))
    intro v hv
    unfold tr7Add at hv
    split at hv
    · exact hS v hv
    · rcases mem_tr7Ins S hv with rfl | hv
      · exact (tr7RedK_mem S w hS).2 (hL w (List.mem_cons_self ..))
      · exact hS v hv

theorem tr7Close_mem : ∀ (n : ℕ) (S : List ℕ), (∀ v ∈ S, decode32 (tr7XorSel bs v) ∈ U) →
    ∀ v ∈ tr7CloseK Ms n S, decode32 (tr7XorSel bs v) ∈ U
  | 0, S, hS => hS
  | n + 1, S, hS => by
    refine tr7Close_mem n _ (foldl_tr7Add_mem _ S hS ?_)
    intro w hw
    obtain ⟨s, hs, hw⟩ := List.mem_flatMap.1 hw
    obtain ⟨M, hMm, rfl⟩ := List.mem_map.1 hw
    obtain ⟨g, hg, rfl⟩ := List.getElem_of_mem hMm
    have := hM g hg s (hS s hs)
    rwa [List.getD_eq_getElem _ _ hg] at this

theorem tr7Root_mem {r tc n : ℕ} (h : tr7RedK (tr7CloseK Ms n [r]) tc = 0)
    (hr : decode32 (tr7XorSel bs r) ∈ U) : decode32 (tr7XorSel bs tc) ∈ U := by
  have hS := tr7Close_mem hM n [r] (by simpa using hr)
  refine (tr7RedK_mem _ tc hS).1 ?_
  rw [h, tr7XorSel_zero, decode32_zero]
  exact U.zero_mem

omit hM in
theorem tr7SelK_eq : ∀ (L : List ℕ) (m : ℕ), tr7SelK L m = tr7XorSel L m
  | [], _ => rfl
  | b :: L, m => by
    rw [tr7XorSel_cons, ← tr7SelK_eq L (m / 2)]
    change Nat.xor (Bool.rec 0 b (Nat.beq (Nat.land m 1) 1)) (tr7SelK L (Nat.shiftRight m 1)) = _
    have e1 : Nat.shiftRight m 1 = m / 2 := Nat.shiftRight_one m
    have e2 : Nat.land m 1 = m % 2 := Nat.and_one_is_mod m
    rw [e1, e2]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl

omit hM in
theorem tr7MemK_iff (x : ℕ) : ∀ rs : List ℕ, tr7MemK x rs = true ↔ x ∈ rs
  | [] => by simp [tr7MemK]
  | r :: rs => by
    rw [List.mem_cons, ← tr7MemK_iff x rs]
    change Bool.rec (tr7MemK x rs) true (Nat.beq x r) = true ↔ _
    cases h : Nat.beq x r
    · have : x ≠ r := fun e => by rw [e, Nat.beq_refl] at h; exact absurd h (by decide)
      simp [this]
    · simp [Nat.eq_of_beq_eq_true h]

theorem tr7Forest_mem {reps : List ℕ} {N hi D G t : ℕ} (hN : N ≤ 64 * hi)
    (hR : ∀ r ∈ reps, decode32 (tr7XorSel bs r) ∈ U → decode32 t ∈ U)
    (hF : pkTreeOK N hi 5 3 D G (Nat.blt 0) (fun x => tr7MemK x reps)
      (fun g => Nat.blt g Ms.length) (fun g y => tr7SelK (Ms.getD g []) y) = true) :
    ∀ m < N, 0 < m → decode32 (tr7XorSel bs m) ∈ U → decode32 t ∈ U := by
  intro m hm hm0
  obtain ⟨r, hr, hrm⟩ := pkTree_sound hF hN m hm (Nat.blt_eq.mpr hm0)
  clear hm hm0
  induction hrm with
  | refl => exact hR r ((tr7MemK_iff r reps).1 hr)
  | tail _ hst ih =>
    obtain ⟨g, hg, hp, -, -⟩ := hst
    intro hy
    exact ih (by rw [← hp, tr7SelK_eq]; exact hM g (Nat.blt_eq.mp hg) _ hy)

end Forest

end CFSG.KD.SmithD6

end
