module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.KS.Tbl

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

variable {n : Nat}

theorem getElem!_set! {α : Type} [Inhabited α] (a : Array α) (k r : Nat) (v : α)
    (hr : r < a.size) : (a.set! k v)[r]! = if k = r then v else a[r]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (a.setIfInBounds k v) r (by simpa using hr),
    Array.getElem_setIfInBounds hr, getElem!_pos a r hr]

theorem invT_eq_foldl (n : Nat) (P : Table) :
    invT n P = (List.range' 0 n).foldl (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i))
      (Array.replicate n 0) := by
  unfold invT
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rfl

theorem foldl_set_inv {P : Table} {g : Equiv.Perm (Fin n)} (hP : Rep n P g) :
    ∀ (m s : Nat) (a : Array UInt32), a.size = n → s + m ≤ n →
      (∀ i < s, (a[ap P i]!).toNat = i % 2 ^ 32) →
      ((List.range' s m).foldl (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i)) a).size = n ∧
        ∀ i < s + m, (((List.range' s m).foldl
          (fun r i => r.set! (P[i]!).toNat (UInt32.ofNat i)) a)[ap P i]!).toNat = i % 2 ^ 32 := by
  intro m
  induction m with
  | zero =>
    intro s a ha _ hi
    exact ⟨ha, fun i h => hi i (by omega)⟩
  | succ m ih =>
    intro s a ha hsm hi
    rw [List.range'_succ, List.foldl_cons]
    have hs : ap P s < n := by rw [hP s (by omega)]; exact idx_lt g (by omega)
    have hsz : (a.set! (P[s]!).toNat (UInt32.ofNat s)).size = n := by simp [ha]
    rw [show s + (m + 1) = s + 1 + m by omega]
    refine ih (s + 1) _ hsz (by omega) fun i hi' => ?_
    have hPi : ap P i < n := by rw [hP i (by omega)]; exact idx_lt g (by omega)
    rw [getElem!_set! _ _ _ _ (by rw [ha]; exact hPi)]
    change (if ap P s = ap P i then UInt32.ofNat s else a[ap P i]!).toNat = i % 2 ^ 32
    by_cases e : ap P s = ap P i
    · rw [ite_eq_left e]
      have hsi : s = i := by
        rw [hP s (by omega), hP i (by omega)] at e
        have := congrArg (idx n g⁻¹) e
        rwa [idx_inv_idx, idx_inv_idx] at this
      rw [← hsi, UInt32.toNat_ofNat']
    · rw [ite_eq_right e]
      exact hi i (by
        rcases Nat.lt_or_ge i s with h | h
        · exact h
        · exact absurd (by rw [show i = s by omega]) e)

theorem invT_rep (hn : n < 2 ^ 32) {P : Table} {g : Equiv.Perm (Fin n)} (hP : Rep n P g) :
    Rep n (invT n P) g⁻¹ := by
  obtain ⟨-, h2⟩ := foldl_set_inv hP n 0 (Array.replicate n 0) (by simp) (by omega)
    (fun i hi => absurd hi (Nat.not_lt_zero _))
  intro j hj
  have hi := idx_lt g⁻¹ hj
  have e : ap P (idx n g⁻¹ j) = j := by rw [hP _ hi, idx_idx_inv]
  have := h2 (idx n g⁻¹ j) (by omega)
  rw [e, ← invT_eq_foldl, Nat.mod_eq_of_lt (hi.trans hn)] at this
  exact this

theorem invT_size (n : Nat) (P : Table) : (invT n P).size = n := by
  rw [invT_eq_foldl]
  have : ∀ (l : List Nat) (a : Array UInt32), (l.foldl (fun r i => r.set! (P[i]!).toNat
      (UInt32.ofNat i)) a).size = a.size := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons x l ih => intro a; rw [List.foldl_cons, ih]; simp
  rw [this]
  simp

theorem invOK_invT (hn : n < 2 ^ 32) {P : Table} {g : Equiv.Perm (Fin n)} (hP : Rep n P g) :
    invOK n P (invT n P) = true := by
  have hR := invT_rep hn hP
  unfold invOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hP i hi, hR _ (idx_lt g hi), idx_inv_idx]

theorem toTable_ext {g : Equiv.Perm (Fin n)} {T : Table} (hn : n < 2 ^ 32) (hs : T.size = n)
    (hT : Rep n T g) : T = toTable g := by
  apply Array.ext (by simp [toTable, hs])
  intro i h1 h2
  have hi : i < n := by omega
  have e := hT i hi
  rw [← rep_toTable hn g i hi] at e
  unfold ap at e
  rw [getElem!_pos T i h1, getElem!_pos (toTable g) i h2] at e
  exact UInt32.toNat_inj.1 e

theorem size_toTable (g : Equiv.Perm (Fin n)) : (toTable g).size = n := by simp [toTable]

theorem compT_eq_toTable (hn : n < 2 ^ 32) {P Q : Table} {g h : Equiv.Perm (Fin n)}
    (hP : Rep n P g) (hQ : Rep n Q h) : compT n P Q = toTable (g * h) :=
  toTable_ext hn (by simp [compT]) (Rep.compT hP hQ)

theorem conjT_eq_toTable (hn : n < 2 ^ 32) {g gi x : Table} {gg xg : Equiv.Perm (Fin n)}
    (hg : Rep n g gg) (hgi : Rep n gi gg⁻¹) (hx : Rep n x xg) :
    conjT n g gi x = toTable (gg * xg * gg⁻¹) :=
  toTable_ext hn (by simp [conjT, compT]) (rep_conjT hg hgi hx)

theorem digits_inj (hn : 0 < n) : ∀ (a b : List Nat), a.length = b.length → (∀ x ∈ a, x < n) →
    (∀ x ∈ b, x < n) → a.foldr (fun x acc => x + n * acc) 0 = b.foldr (fun x acc => x + n * acc) 0 →
      a = b
  | [], [], _, _, _, _ => rfl
  | x :: a, y :: b, hl, ha, hb, e => by
    simp only [List.foldr_cons] at e
    have hx := ha x List.mem_cons_self
    have hy := hb y List.mem_cons_self
    have e1 : x = y := by
      have := congrArg (· % n) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
      exact this
    have e2 := congrArg (· / n) e
    simp only [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy,
      Nat.zero_add] at e2
    rw [e1, digits_inj hn a b (by simpa using hl) (fun z hz => ha z (List.mem_cons_of_mem _ hz))
      (fun z hz => hb z (List.mem_cons_of_mem _ hz)) e2]

theorem key_eq_foldr (n : Nat) (T : Table) :
    key n T = ((List.range n).map (ap T)).foldr (fun x acc => x + n * acc) 0 := by
  rw [key, List.foldr_map]

theorem key_inj {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h)
    (e : key n S = key n T) : g = h := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Equiv.ext fun x => x.elim0
  rw [key_eq_foldr, key_eq_foldr] at e
  have hd := digits_inj hn _ _ (by simp) (by
      simp only [List.mem_map, List.mem_range]
      rintro x ⟨i, hi, rfl⟩
      rw [hS i hi]
      exact idx_lt g hi) (by
      simp only [List.mem_map, List.mem_range]
      rintro x ⟨i, hi, rfl⟩
      rw [hT i hi]
      exact idx_lt h hi) e
  apply Equiv.ext
  intro x
  apply Fin.ext
  have := congrArg (·[x.val]?) hd
  simp only [List.getElem?_map, List.getElem?_range x.isLt, Option.map_some, Option.some.injEq]
    at this
  rw [hS x x.isLt, hT x x.isLt, idx_of_lt _ x.isLt, idx_of_lt _ x.isLt] at this
  exact this

theorem strictlyIncreasing_of_pairwise : ∀ {l : List Nat}, l.Pairwise (· < ·) →
    strictlyIncreasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    simp only [strictlyIncreasing, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, strictlyIncreasing_of_pairwise
      (List.Pairwise.of_cons h)⟩

theorem keysDistinct_of_nodup {Ts : List Table} (h : (Ts.map (key n)).Nodup) :
    keysDistinct n Ts = true := by
  unfold keysDistinct
  apply strictlyIncreasing_of_pairwise
  have hs := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (Ts.map (key n))
  have hnd := (List.mergeSort_perm (Ts.map (key n)) (fun a b : Nat => decide (a ≤ b))).nodup_iff.2 h
  refine (hs.and (List.nodup_iff_pairwise_ne.1 hnd)).imp fun ⟨h1, h2⟩ => ?_
  simp only [decide_eq_true_eq] at h1
  omega

theorem tblEq_iff_eq {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h := by
  rw [tblEq_iff]
  constructor
  · intro e
    apply Equiv.ext
    intro x
    apply Fin.ext
    have := e x x.isLt
    rw [hS x x.isLt, hT x x.isLt, idx_of_lt _ x.isLt, idx_of_lt _ x.isLt] at this
    exact this
  · rintro rfl i hi
    rw [hS i hi, hT i hi]

theorem oddWitnessOK_of (hn : n < 2 ^ 32) {K : List Table} {L : List (Equiv.Perm (Fin n))}
    (hK : List.Forall₂ (Rep n) K L) {m : Nat}
    (h : ∀ x ∈ L, x = 1 ∨ x ^ m ≠ 1 ∨ (∃ y ∈ L, (x * y * x * y⁻¹) ^ m ≠ 1) ∨
      ∃ y ∈ L, ∃ z ∈ L, (x * y * x * y⁻¹ * z * x * z⁻¹) ^ m ≠ 1) :
    oddWitnessOK n m K = true := by
  unfold oddWitnessOK
  rw [List.all_eq_true]
  intro X hX
  obtain ⟨x, hx, hXx⟩ := CFSG.Sporadic.Schreier.exists_mem_of_forall₂_right hK X hX
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, Bool.and_eq_true]
  rcases h x hx with h1 | h1 | ⟨y, hy, h1⟩ | ⟨y, hy, z, hz, h1⟩
  · exact Or.inl (Or.inl (Or.inl ((tblEq_iff_eq hXx (Rep.idT hn)).2 h1)))
  · refine Or.inl (Or.inl (Or.inr ?_))
    cases hp : powFixW n [X] m
    · rfl
    · exact absurd (by simpa using (powFixW_iff perm_faithful (.cons hXx .nil) m).1 hp) h1
  · obtain ⟨Y, hY, hYy⟩ := CFSG.Sporadic.Schreier.exists_mem_of_forall₂_left hK y hy
    refine Or.inl (Or.inr ⟨Y, hY, invOK_invT hn hYy, ?_⟩)
    have hw : List.Forall₂ (Rep n) [X, Y, X, invT n Y] [x, y, x, y⁻¹] :=
      .cons hXx (.cons hYy (.cons hXx (.cons (invT_rep hn hYy) .nil)))
    cases hp : powFixW n [X, Y, X, invT n Y] m
    · rfl
    · exact absurd (by simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using
        (powFixW_iff perm_faithful hw m).1 hp) (by simpa only [mul_assoc] using h1)
  · obtain ⟨Y, hY, hYy⟩ := CFSG.Sporadic.Schreier.exists_mem_of_forall₂_left hK y hy
    obtain ⟨Z, hZ, hZz⟩ := CFSG.Sporadic.Schreier.exists_mem_of_forall₂_left hK z hz
    refine Or.inr ⟨Y, hY, invOK_invT hn hYy, Z, hZ, invOK_invT hn hZz, ?_⟩
    have hw : List.Forall₂ (Rep n) [X, Y, X, invT n Y, Z, X, invT n Z]
        [x, y, x, y⁻¹, z, x, z⁻¹] :=
      .cons hXx (.cons hYy (.cons hXx (.cons (invT_rep hn hYy) (.cons hZz (.cons hXx
        (.cons (invT_rep hn hZz) .nil))))))
    cases hp : powFixW n [X, Y, X, invT n Y, Z, X, invT n Z] m
    · rfl
    · exact absurd (by simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using
        (powFixW_iff perm_faithful hw m).1 hp) (by simpa only [mul_assoc] using h1)

end CFSG.KS.Tbl

end
