module

public import Certificates.Data.DcSub
public import CFSG.Certificates.Kernel.DcKSound

namespace CFSG.KC.DcK

open CFSG.Quasithin.H13.LocDbl.DcNative CFSG.KC.E64F

theorem subK_img {n : Nat} {s : Array Nat} {f : Nat → Nat} (h : Good n s f) {p : Nat}
    (hp : p < n) : img s p = f p ∧ f p < n := h.2 p hp

theorem subK_strictInc : ∀ l : List Nat, l.Pairwise (· < ·) → strictInc l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h1 : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
    have h2 := subK_strictInc (b :: l) h.of_cons
    simp [strictInc, h1, h2]

theorem subK_distinctNat {l : List Nat} (h : l.Nodup) : distinctNat l = true := by
  unfold distinctNat
  apply subK_strictInc
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
  have hn : (l.mergeSort fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.mpr h
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => by simp at h1; omega

theorem subK_ptsArr_succ (G : Array (Array Nat)) (par lab : Array Nat) (M q : Nat) :
    ptsArr G par lab (M + 1) q = ptsStep G par lab q (ptsArr G par lab M q) M := by
  simp [ptsArr, List.range_succ, List.foldl_append]

theorem subK_ptsArr_size (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat) :
    ∀ M, (ptsArr G par lab M q).size = M
  | 0 => rfl
  | M + 1 => by
    rw [subK_ptsArr_succ]
    simp [ptsStep, subK_ptsArr_size G par lab q M]

theorem subK_ptsArr_getD_le (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat)
    {k M : Nat} (hk : k < M) : ∀ N, M ≤ N →
      (ptsArr G par lab N q).getD k 0 = (ptsArr G par lab M q).getD k 0 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih =>
    rw [subK_ptsArr_succ, ← ih]
    have hs := subK_ptsArr_size G par lab q N
    simp only [ptsStep, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
    rw [if_neg (by omega)]

theorem subK_ptsArr_getD (G : Array (Array Nat)) (par lab : Array Nat) (q : Nat)
    {k N : Nat} (hk : k < N) : (ptsArr G par lab N q).getD k 0 =
      if k = 0 then q else img (G.getD (lab.getD k 0) #[]) ((ptsArr G par lab k q).getD (par.getD k 0) 0) := by
  rw [subK_ptsArr_getD_le G par lab q (Nat.lt_succ_self k) N hk, subK_ptsArr_succ]
  have hs := subK_ptsArr_size G par lab q k
  simp only [ptsStep, Array.getD_eq_getD_getElem?, Array.getElem?_push, hs]
  simp

theorem subK_elemK {n : Nat} {B : List Nat} {G : Nat → Nat → Nat} {m : Nat}
    {E : EnumK} {k : Nat} (h : elemK n B G m E k = true) :
    (k = 0 → E.row 0 = B) ∧
    (k ≠ 0 → E.par k < k ∧ E.lab k < m ∧ E.row k = (E.row (E.par k)).map (G (E.lab k))) ∧
    (∀ t < m, E.tgt k t < E.N ∧ (E.row k).map (G t) = E.row (E.tgt k t)) ∧
    E.sig k < E.N ∧ E.sinv (E.sig k) = k ∧ E.sinv k < E.N ∧ E.sig (E.sinv k) = k ∧
    (E.N ≤ k + 1 ∨ E.skey n B.length k < E.skey n B.length (k + 1)) := by
  unfold elemK at h
  by_cases hk : k = 0
  · subst hk
    simp only [beq_self_eq_true, if_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩ := h
    exact ⟨fun _ => h1, fun h0 => absurd rfl h0, h2, h3, h4, h5, h6, h7⟩
  · have hk' : (k == 0) = false := by simp [hk]
    simp only [hk', Bool.false_eq_true, if_false, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      List.mem_range, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hl⟩, hr⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩ := h
    exact ⟨fun h0 => absurd h0 hk, fun _ => ⟨hp, hl, hr⟩, h2, h3, h4, h5, h6, h7⟩

section Keys

variable {n : Nat} {B : List Nat} {Lm : Nat → Nat → Nat} {m : Nat} {E : EnumK}

theorem subK_skey_lt (he : ∀ k < E.N, elemK n B Lm m E k = true) {a : Nat} :
    ∀ b, a < b → b < E.N → E.skey n B.length a < E.skey n B.length b := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro hb
    rcases (subK_elemK (he a (by omega))).2.2.2.2.2.2.2 with h | h
    · omega
    · exact h
  | succ b hab ih =>
    intro hb
    refine Nat.lt_trans (ih (by omega)) ?_
    rcases (subK_elemK (he b (by omega))).2.2.2.2.2.2.2 with h | h
    · omega
    · exact h

theorem subK_key_skey (he : ∀ k < E.N, elemK n B Lm m E k = true) {k : Nat}
    (hk : k < E.N) : E.key n B.length k = E.skey n B.length (E.sinv k) ∧ E.sinv k < E.N := by
  have h := subK_elemK (he k hk)
  refine ⟨?_, h.2.2.2.2.2.1⟩
  unfold EnumK.skey
  rw [h.2.2.2.2.2.2.1]

theorem subK_key_inj (he : ∀ k < E.N, elemK n B Lm m E k = true) {k k' : Nat}
    (hk : k < E.N) (hk' : k' < E.N) (h : E.key n B.length k = E.key n B.length k') : k = k' := by
  obtain ⟨e1, l1⟩ := subK_key_skey he hk
  obtain ⟨e2, l2⟩ := subK_key_skey he hk'
  rw [e1, e2] at h
  rcases Nat.lt_trichotomy (E.sinv k) (E.sinv k') with c | c | c
  · exact absurd h (Nat.ne_of_lt (subK_skey_lt he _ c l2))
  · rw [← (subK_elemK (he k hk)).2.2.2.2.2.2.1, ← (subK_elemK (he k' hk')).2.2.2.2.2.2.1, c]
  · exact absurd h.symm (Nat.ne_of_lt (subK_skey_lt he _ c l1))

theorem subK_keys_nodup (he : ∀ k < E.N, elemK n B Lm m E k = true) :
    ((List.range E.N).map (E.key n B.length)).Nodup := by
  refine List.nodup_range.map_on fun x hx y hy h => ?_
  exact subK_key_inj he (List.mem_range.mp hx) (List.mem_range.mp hy) h

end Keys

section Rec

variable {n : Nat} {B : List Nat} {G : Array (Array Nat)} {Lm : Nat → Nat → Nat} {m : Nat}
  {E : EnumK} {par lab : Array Nat}

theorem subK_hpl (he : ∀ k < E.N, elemK n B Lm m E k = true) :
    ∀ k < E.N, k ≠ 0 → E.par k < k ∧ E.lab k < m := fun k hk h0 =>
  let h := (subK_elemK (he k hk)).2.1 h0
  ⟨h.1, h.2.1⟩

theorem subK_pts (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hpl : ∀ k < E.N, k ≠ 0 → E.par k < k ∧ E.lab k < m)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k)
    {q : Nat} (hq : q < n) : ∀ k < E.N, (ptsArr G par lab E.N q).getD k 0 < n ∧
      (ptsArr G par lab E.N q).getD k 0 =
        if k = 0 then q else Lm (E.lab k) ((ptsArr G par lab E.N q).getD (E.par k) 0) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [subK_ptsArr_getD G par lab q hk]
    by_cases h0 : k = 0
    · simp [h0, hq]
    · obtain ⟨hp, hl⟩ := hpl k hk h0
      rw [hpar k hk, hlab k hk, ← subK_ptsArr_getD_le G par lab q hp E.N hk.le]
      have ih' := (ih (E.par k) hp (by omega)).1
      have := subK_img (hG _ hl) ih'
      simp only [h0, if_false]
      exact ⟨by rw [this.1]; exact this.2, this.1⟩

theorem subK_rowOf (P : Nat → Array Nat) (k : Nat) :
    rowOf (B.map P) k = B.map fun b => (P b).getD k 0 := by
  simp [rowOf, List.map_map, Function.comp_def]

theorem subK_rec_row (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    ∀ k < E.N, rowOf (B.map (ptsArr G par lab E.N)) k = E.row k := by
  have hpl := subK_hpl he
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [subK_rowOf]
    by_cases h0 : k = 0
    · subst h0
      rw [(subK_elemK (he 0 hk)).1 rfl]
      refine (List.map_congr_left fun q hq => ?_).trans (List.map_id' B)
      rw [(subK_pts hG hpl hpar hlab (hB q hq) 0 hk).2]
      simp
    · obtain ⟨hp, -, hr⟩ := (subK_elemK (he k hk)).2.1 h0
      rw [hr, ← ih (E.par k) hp (by omega), subK_rowOf, List.map_map]
      refine List.map_congr_left fun q hq => ?_
      rw [(subK_pts hG hpl hpar hlab (hB q hq) k hk).2]
      simp [h0]

theorem subK_rec_lt (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    ∀ k < E.N, ∀ x ∈ E.row k, x < n := by
  intro k hk x hx
  rw [← subK_rec_row hG hB he hpar hlab k hk, subK_rowOf] at hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  exact (subK_pts hG (subK_hpl he) hpar hlab (hB b hb) k hk).1

theorem subK_rec_keys (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    rowKeys n B G par lab E.N = (List.range E.N).map (E.key n B.length) := by
  unfold rowKeys
  refine List.map_congr_left fun k hk => ?_
  have := subK_rec_row hG hB he hpar hlab k (List.mem_range.mp hk)
  unfold rowOf at this
  simp only [EnumK.key, this]

theorem subK_rec_enumOK (hGs : G.size = m)
    (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    enumOK E.N G par lab = true := by
  unfold enumOK
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq]
  intro k hk
  by_cases h0 : k = 0
  · exact Or.inl h0
  · have := subK_hpl he k hk h0
    rw [hpar k hk, hlab k hk, hGs]
    exact Or.inr this

theorem subK_rec_distinct (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    distinctNat (rowKeys n B G par lab E.N) = true := by
  rw [subK_rec_keys hG hB he hpar hlab]
  exact subK_distinctNat (subK_keys_nodup he)

theorem subK_rec_closed (hG : ∀ t < m, Good n (G.getD t #[]) (Lm t))
    (hGs : G.size = m) (hB : ∀ b ∈ B, b < n) (he : ∀ k < E.N, elemK n B Lm m E k = true)
    (hpar : ∀ k < E.N, par.getD k 0 = E.par k) (hlab : ∀ k < E.N, lab.getD k 0 = E.lab k) :
    closedOK n B G par lab E.N = true := by
  have hrow := subK_rec_row hG hB he hpar hlab
  have hlt := subK_rec_lt hG hB he hpar hlab
  unfold closedOK
  have hM : ((List.range E.N).map fun k =>
      (keyNat n B.length (rowOf (B.map (ptsArr G par lab E.N)) k), k)) =
      (List.range E.N).map fun k => (E.key n B.length k, k) := by
    refine List.map_congr_left fun k hk => ?_
    rw [hrow k (List.mem_range.mp hk)]; rfl
  simp only []
  rw [hM]
  have hdist : ((List.range E.N).map fun k => (E.key n B.length k, k)).Pairwise
      (fun a b => (a.1 == b.1) = false) := by
    rw [List.pairwise_map]
    refine List.nodup_range.imp_of_mem fun {a b} ha hb hab => ?_
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    exact hab (subK_key_inj he (List.mem_range.mp ha) (List.mem_range.mp hb) h)
  simp only [List.all_eq_true, List.mem_range]
  intro k hk t ht
  rw [hGs] at ht
  obtain ⟨htg, hrt⟩ := (subK_elemK (he k hk)).2.2.1 t ht
  have hmap : (rowOf (B.map (ptsArr G par lab E.N)) k).map (img (G.getD t #[])) =
      E.row (E.tgt k t) := by
    rw [hrow k hk, ← hrt]
    exact List.map_congr_left fun x hx => (subK_img (hG t ht) (hlt k hk x hx)).1
  have hget : (Std.HashMap.ofList ((List.range E.N).map fun k => (E.key n B.length k, k))).get?
      (keyNat n B.length (E.row (E.tgt k t))) = some (E.tgt k t) := by
    rw [Std.HashMap.get?_eq_getElem?]
    exact Std.HashMap.getElem?_ofList_of_mem (k := E.key n B.length (E.tgt k t)) (by simp [EnumK.key])
      hdist (List.mem_map.mpr ⟨E.tgt k t, List.mem_range.mpr htg, rfl⟩)
  unfold closedStep
  rw [hmap, hget]
  simp [htg, hrow _ htg]

end Rec

theorem subK_getD_toArray (f : Nat → Nat) {N k : Nat} (hk : k < N) :
    ((List.range N).map f).toArray.getD k 0 = f k := by
  simp [Array.getD_eq_getD_getElem?, hk]

public theorem subEnumOK_of_elemK {n cap : Nat} {B : List Nat} {G : Array (Array Nat)}
    {L : Nat → Nat → Nat} {E : EnumK} (hG : ∀ t < G.size, Good n (G.getD t #[]) (L t))
    (hm : 0 < G.size) (hd : enumHd n B cap E = true)
    (he : ∀ k < E.N, elemK n B L G.size E k = true) :
    subEnumOK n B E.N cap G = true := by
  have hd' : 0 < E.N ∧ E.N ≤ cap ∧ ∀ b ∈ B, b < n := by
    simpa [enumHd, and_assoc] using hd
  have hb := bfsEnumL_of_elemK hG hm hd he
  have hpar : ∀ k < E.N, ((List.range E.N).map E.par).toArray.getD k 0 = E.par k :=
    fun k hk => subK_getD_toArray E.par hk
  have hlab : ∀ k < E.N, ((List.range E.N).map E.lab).toArray.getD k 0 = E.lab k :=
    fun k hk => subK_getD_toArray E.lab hk
  unfold subEnumOK
  rw [hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨subK_rec_enumOK rfl he hpar hlab, subK_rec_distinct hG hd'.2.2 he hpar hlab⟩,
    subK_rec_closed hG rfl hd'.2.2 he hpar hlab⟩, hd'.1⟩

end CFSG.KC.DcK
