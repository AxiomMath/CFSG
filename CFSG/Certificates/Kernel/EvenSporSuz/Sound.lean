module

public import Certificates.Data.Kernel.EvenSporSuz.Defs
import all Init.Data.String.Slice
import all Init.Data.String.Search

public section

namespace CFSG.KC.EvenSporSuz

open CFSG.EvenSporadicStandard.TwoSuz

@[expose] def packF : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + 64 * packF n (fun k => f (k + 1))

@[expose] def sumF : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, g => g 0 + sumF n (fun j => g (j + 1))

theorem map_range_succ {α : Type} (n : ℕ) (f : ℕ → α) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun k => f (k + 1)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

theorem packL_range (n : ℕ) (f : ℕ → ℕ) : packL ((List.range n).map f) = packF n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [map_range_succ, packL, packF, ih]

theorem packF_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ k < n, f k = g k) : packF n f = packF n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [packF]
    rw [h 0 (by omega), ih (fun k hk => h (k + 1) (by omega))]

theorem packF_zero (n : ℕ) : packF n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [packF, ih]

theorem packF_add (n : ℕ) (f g : ℕ → ℕ) :
    packF n f + packF n g = packF n (fun k => f k + g k) := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [packF]
    rw [← ih]
    ring

theorem packF_mul (n c : ℕ) (f : ℕ → ℕ) : c * packF n f = packF n (fun k => c * f k) := by
  induction n generalizing f with
  | zero => simp [packF]
  | succ n ih =>
    simp only [packF]
    rw [← ih]
    ring

theorem sumF_le {n c : ℕ} {g : ℕ → ℕ} (h : ∀ j < n, g j ≤ c) : sumF n g ≤ n * c := by
  induction n generalizing g with
  | zero => simp [sumF]
  | succ n ih =>
    simp only [sumF]
    have h0 := h 0 (by omega)
    have h1 := ih (g := fun j => g (j + 1)) (fun j hj => h (j + 1) (by omega))
    rw [Nat.succ_mul]
    omega

theorem accRow_packF (n m : ℕ) (a : ℕ → ℕ) (b : ℕ → ℕ → ℕ) (ha : ∀ j < m, a j < 64) :
    accRow (packF m a) ((List.range m).map fun j => packF n (b j)) =
      packF n (fun k => sumF m (fun j => a j * b j k)) := by
  induction m generalizing a b with
  | zero => simp [accRow, sumF, packF_zero]
  | succ m ih =>
    rw [map_range_succ]
    simp only [accRow, packF]
    have h0 := ha 0 (by omega)
    have e1 : (a 0 + 64 * packF m (fun k => a (k + 1))) % 64 = a 0 := by omega
    have e2 : (a 0 + 64 * packF m (fun k => a (k + 1))) / 64 = packF m (fun k => a (k + 1)) := by
      omega
    rw [e1, e2, ih (fun k => a (k + 1)) (fun j k => b (j + 1) k)
      (fun j hj => ha (j + 1) (by omega))]
    simp only [sumF]
    rw [packF_mul, packF_add]

theorem redGo_packF (n : ℕ) (f : ℕ → ℕ) (h : ∀ k < n, f k < 64) :
    redGo n (packF n f) = packF n (fun k => f k % 3) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [redGo, packF]
    have h0 := h 0 (by omega)
    have e1 : (f 0 + 64 * packF n (fun k => f (k + 1))) % 64 = f 0 := by omega
    have e2 : (f 0 + 64 * packF n (fun k => f (k + 1))) / 64 = packF n (fun k => f (k + 1)) := by
      omega
    rw [e1, e2, ih _ (fun k hk => h (k + 1) (by omega))]

theorem packF_inj {n : ℕ} {f g : ℕ → ℕ} (hf : ∀ k < n, f k < 64) (hg : ∀ k < n, g k < 64)
    (h : packF n f = packF n g) : ∀ k < n, f k = g k := by
  induction n generalizing f g with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [packF] at h
    have hf0 := hf 0 (by omega)
    have hg0 := hg 0 (by omega)
    have e0 : f 0 = g 0 := by omega
    have e1 : packF n (fun k => f (k + 1)) = packF n (fun k => g (k + 1)) := by omega
    intro k hk
    rcases k with _ | k
    · exact e0
    · exact ih (fun k hk => hf (k + 1) (by omega)) (fun k hk => hg (k + 1) (by omega)) e1 k
        (by omega)

theorem foldl_range_sum (n c : ℕ) (g : ℕ → ℕ) :
    (List.range n).foldl (fun s j => s + g j) c = c + sumF n g := by
  induction n generalizing c g with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    rw [show (fun s j => s + g (Nat.succ j)) = (fun s j => s + (fun k => g (k + 1)) j) from rfl,
      ih, sumF]
    omega

theorem getD_lt {A : Array ℕ} (h : canonB A = true) (p : ℕ) : A.getD p 0 < 3 := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  rw [Array.getD_eq_getD_getElem?]
  by_cases hp : p < A.size
  · rw [Array.getElem?_eq_getElem hp, Option.getD_some]
    exact h.2 p hp
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
    omega

theorem size_eq {A : Array ℕ} (h : canonB A = true) : A.size = 144 := by
  simp only [canonB, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem mulM_getD (A B : Array ℕ) {i k : ℕ} (hi : i < 12) (hk : k < 12) :
    (mulM A B).getD (12 * i + k) 0 =
      sumF 12 (fun j => A.getD (12 * i + j) 0 * B.getD (12 * j + k) 0) % 3 := by
  have hp : 12 * i + k < 144 := by omega
  rw [mulM, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [hp, dite_true, Option.getD_some]
  have h1 : (12 * i + k) / 12 = i := by omega
  have h2 : (12 * i + k) % 12 = k := by omega
  rw [h1, h2, foldl_range_sum, Nat.zero_add]

theorem rowsOf_eq (A : Array ℕ) :
    rowsOf A = (List.range 12).map fun i => packF 12 (fun k => A.getD (12 * i + k) 0) := by
  simp only [rowsOf, packL_range]

theorem rowsOf_mulM {A B : Array ℕ} (hA : canonB A = true) (hB : canonB B = true) :
    rowsOf (mulM A B) = mulR (rowsOf A) (rowsOf B) := by
  rw [mulR, rowsOf_eq, rowsOf_eq A, List.map_map, rowsOf_eq B]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 12 := List.mem_range.1 hi
  simp only [Function.comp]
  rw [accRow_packF 12 12 _ (fun j k => B.getD (12 * j + k) 0)
      (fun j _ => by have := getD_lt hA (12 * i + j); omega),
    redGo_packF 12 _ (fun k _ => by
      have := sumF_le (n := 12) (c := 4)
        (g := fun j => A.getD (12 * i + j) 0 * B.getD (12 * j + k) 0) (fun j _ => by
          have h1 := getD_lt hA (12 * i + j)
          have h2 := getD_lt hB (12 * j + k)
          have : A.getD (12 * i + j) 0 * B.getD (12 * j + k) 0 ≤ 2 * 2 :=
            Nat.mul_le_mul (by omega) (by omega)
          omega)
      omega)]
  exact packF_congr fun k hk => mulM_getD A B hi hk

theorem rowsOf_inj {A B : Array ℕ} (hA : canonB A = true) (hB : canonB B = true)
    (h : rowsOf A = rowsOf B) : A = B := by
  have hrow : ∀ i < 12, ∀ k < 12, A.getD (12 * i + k) 0 = B.getD (12 * i + k) 0 := by
    intro i hi
    have e := congrArg (fun l => l.getD i 0) h
    simp only [rowsOf_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some] at e
    exact packF_inj (fun k _ => by have := getD_lt hA (12 * i + k); omega)
      (fun k _ => by have := getD_lt hB (12 * i + k); omega) e
  have hall : ∀ p < 144, A.getD p 0 = B.getD p 0 := by
    intro p hp
    have := hrow (p / 12) (by omega) (p % 12) (by omega)
    rwa [show 12 * (p / 12) + p % 12 = p by omega] at this
  have hsA := size_eq hA
  have hsB := size_eq hB
  refine Array.ext (hsA.trans hsB.symm) fun p h1 h2 => ?_
  have := hall p (by omega)
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2] at this
  simpa using this

theorem beq_rows {A B : Array ℕ} (hA : canonB A = true) (hB : canonB B = true) :
    (A == B) = (rowsOf A == rowsOf B) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => h ▸ rfl, rowsOf_inj hA hB⟩

theorem rowsOf_oneM : rowsOf oneM = oneR := by decide +kernel

theorem canonB_powM (A : Array ℕ) : ∀ n, canonB (powM A n) = true
  | 0 => canonB_oneM
  | _ + 1 => canonB_mulM _ _

theorem rowsOf_powM {A : Array ℕ} (hA : canonB A = true) :
    ∀ n, rowsOf (powM A n) = powR (rowsOf A) n
  | 0 => rowsOf_oneM
  | n + 1 => by
    rw [powM, powR, rowsOf_mulM (canonB_powM A n) hA, rowsOf_powM hA n]

theorem canonB_invM' (A : Array ℕ) : canonB (invM' A) = true := by
  unfold invM'
  cases (List.range 100).find? fun k => powM A (k + 1) == oneM with
  | none => rw [Option.elim_none]; exact canonB_oneM
  | some k => rw [Option.elim_some]; exact canonB_powM A k

theorem rowsOf_invM' {A : Array ℕ} (hA : canonB A = true) : rowsOf (invM' A) = invR (rowsOf A) := by
  unfold invM' invR
  have hp : (fun k => powM A (k + 1) == oneM) = (fun k => powR (rowsOf A) (k + 1) == oneR) := by
    funext k
    rw [beq_rows (canonB_powM A _) canonB_oneM, rowsOf_powM hA, rowsOf_oneM]
  rw [hp]
  cases (List.range 100).find? fun k => powR (rowsOf A) (k + 1) == oneR with
  | none => rw [Option.elim_none, Option.elim_none]; exact rowsOf_oneM
  | some k => rw [Option.elim_some, Option.elim_some]; exact rowsOf_powM hA k

@[expose] def CanonGS (G : GenSys) : Prop :=
  (∀ i, canonB (G.mats.getD i oneM) = true) ∧ ∀ i, canonB (G.invs.getD i oneM) = true

theorem rowsOf_getD (a : Array (Array ℕ)) (i : ℕ) :
    rowsOf (a.getD i oneM) = (a.toList.map rowsOf).getD i oneR := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_map,
    Array.getElem?_toList]
  cases a[i]? with
  | none => rw [Option.map_none, Option.getD_none, Option.getD_none]; exact rowsOf_oneM
  | some x => rw [Option.map_some, Option.getD_some, Option.getD_some]

theorem canonB_getD {a : Array (Array ℕ)} (h : ∀ x ∈ a, canonB x = true) (i : ℕ) :
    canonB (a.getD i oneM) = true := by
  rw [Array.getD_eq_getD_getElem?]
  cases hx : a[i]? with
  | none => rw [Option.getD_none]; exact canonB_oneM
  | some x => rw [Option.getD_some]; exact h x (Array.mem_of_getElem? hx)

theorem canonB_letter {G : GenSys} (hG : CanonGS G) (c : ℕ) : canonB (G.letter c) = true := by
  unfold GenSys.letter
  split
  · exact hG.1 _
  · exact hG.2 _

theorem rowsOf_letter (G : GenSys) (c : ℕ) :
    rowsOf (G.letter c) = letterR (G.mats.toList.map rowsOf) (G.invs.toList.map rowsOf) c := by
  unfold GenSys.letter letterR
  split <;> exact rowsOf_getD _ _

theorem canonB_eval (G : GenSys) (w : List ℕ) : canonB (G.eval w) = true := by
  unfold GenSys.eval
  suffices ∀ (w : List ℕ) (acc : Array ℕ), canonB acc = true →
      canonB (w.foldl (fun acc c => mulM acc (G.letter c)) acc) = true from this w _ canonB_oneM
  intro w
  induction w with
  | nil => exact fun _ h => h
  | cons c w ih =>
    intro acc _
    rw [List.foldl_cons]
    exact ih _ (canonB_mulM _ _)

theorem rowsOf_eval {G : GenSys} (hG : CanonGS G) (w : List ℕ) :
    rowsOf (G.eval w) = evalR (G.mats.toList.map rowsOf) (G.invs.toList.map rowsOf) w := by
  unfold GenSys.eval evalR
  suffices ∀ (w : List ℕ) (acc : Array ℕ), canonB acc = true →
      rowsOf (w.foldl (fun acc c => mulM acc (G.letter c)) acc) =
        w.foldl (fun acc c => mulR acc (letterR (G.mats.toList.map rowsOf)
          (G.invs.toList.map rowsOf) c)) (rowsOf acc) by
    rw [this w _ canonB_oneM, rowsOf_oneM]
  intro w
  induction w with
  | nil => exact fun _ _ => rfl
  | cons c w ih =>
    intro acc hacc
    rw [List.foldl_cons, List.foldl_cons, ih _ (canonB_mulM _ _),
      rowsOf_mulM hacc (canonB_letter hG c), rowsOf_letter]

theorem valid_eq {G : GenSys} (hG : CanonGS G) :
    G.valid = validR (G.mats.toList.map rowsOf) (G.invs.toList.map rowsOf) := by
  have h1 : ∀ i, (mulM (G.mats.getD i oneM) (G.invs.getD i oneM) == oneM) =
      (mulR ((G.mats.toList.map rowsOf).getD i oneR) ((G.invs.toList.map rowsOf).getD i oneR)
        == oneR) := fun i => by
    rw [beq_rows (canonB_mulM _ _) canonB_oneM, rowsOf_mulM (hG.1 i) (hG.2 i), rowsOf_getD,
      rowsOf_getD, rowsOf_oneM]
  have h2 : ∀ i, (mulM (G.invs.getD i oneM) (G.mats.getD i oneM) == oneM) =
      (mulR ((G.invs.toList.map rowsOf).getD i oneR) ((G.mats.toList.map rowsOf).getD i oneR)
        == oneR) := fun i => by
    rw [beq_rows (canonB_mulM _ _) canonB_oneM, rowsOf_mulM (hG.2 i) (hG.1 i), rowsOf_getD,
      rowsOf_getD, rowsOf_oneM]
  simp only [GenSys.valid, validR, h1, h2, List.length_map, Array.length_toList]

open String CFSG.KC.Str

theorem ne_underscore' {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

theorem slice_toNat {u : Slice} {ds : List Char} (hu : u.copy.toList = ds) (hne : ds ≠ [])
    (hd : ∀ c ∈ ds, c.isDigit = true) : u.toNat? = some (decVal ds) := by
  simp only [Slice.toNat?, Slice.isNat]
  simp only [Slice.forIn_eq_forIn_toList, Slice.foldl_eq_foldl_toList, hu]
  rw [forIn_yield (y := ((none : Option Bool), true)) ds]
  · simp only [hne, ↓reduceIte]
    split
    · exact congrArg some (foldl_congr _ _ ds 0 fun x hx n => by simp [ne_underscore' (hd x hx)])
    · rename_i h
      exact absurd rfl h
  · intro c hc x
    simp [ne_underscore' (hd c hc), hd c hc]
    rfl

theorem digitsK_iff {p : List Char} (h : digitsK p = true) :
    p ≠ [] ∧ ∀ c ∈ p, c.isDigit = true := by
  simp only [digitsK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact h

theorem toNat?_ofList {p : List Char} (h : digitsK p = true) :
    (String.ofList p).toNat? = some (decVal p) := by
  obtain ⟨hne, hd⟩ := digitsK_iff h
  exact slice_toNat (by rw [copy_toSlice, toList_ofList]) hne hd

theorem toInt?_ofList {p : List Char} (h : digitsK p = true) :
    (String.ofList p).toInt? = some (decVal p : ℤ) := by
  rw [← String.toInt?_toSlice]
  apply String.Slice.toInt?_eq_some_of_toNat?_eq_some
  obtain ⟨hne, hd⟩ := digitsK_iff h
  exact slice_toNat (by rw [copy_toSlice, toList_ofList]) hne hd

theorem toInt?_ofList_neg {p : List Char} (h : digitsK p = true) :
    (String.ofList ('-' :: p)).toInt? = some (-(decVal p : ℤ)) := by
  rw [← String.toInt?_toSlice, String.Slice.toInt?_eq_of_eq_minus_append (t := String.ofList p)]
  · rw [toNat?_ofList h]
    rfl
  · rw [copy_toSlice, ← toList_inj, toList_append, toList_ofList, toList_ofList]
    simp

theorem ofList_ne_empty {p : List Char} (h : p ≠ []) : String.ofList p ≠ "" := by
  intro e
  have := congrArg String.toList e
  rw [toList_ofList] at this
  exact h (by simpa using this)

theorem space_eq : (" " : String) = String.singleton ' ' := by rw [String.singleton_eq_ofList]

theorem colon_eq : (":" : String) = String.singleton ':' := by rw [String.singleton_eq_ofList]

theorem nl_eq : ("\n" : String) = String.singleton '\n' := by rw [String.singleton_eq_ofList]

theorem filterMap_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = some (g x)) → l.filterMap f = l.map g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, h x (by simp), List.map_cons,
      filterMap_some f g l fun y hy => h y (by simp [hy])]

theorem parseNats_ofList (L : List Char) (h : (L.splitOn ' ').all digitsK = true) :
    parseNats (String.ofList L) = natsK L := by
  unfold parseNats natsK
  rw [space_eq, splitOn_ofList, List.filterMap_map]
  exact filterMap_some _ _ _ fun p hp => toNat?_ofList (List.all_eq_true.1 h p hp)

theorem tok_ne_nil {p : List Char} (h : tokK p = true) : p ≠ [] := by
  rintro rfl
  simp [tokK] at h

theorem tokLetters_eq {p : List Char} (h : tokK p = true) :
    (match (String.ofList p).splitOn ":" with
      | [g, e] =>
        match g.toNat?, e.toInt? with
        | some g, some e =>
          if 0 ≤ e then List.replicate e.toNat (2 * g) else List.replicate (-e).toNat (2 * g + 1)
        | _, _ => []
      | _ => []) = tokLetters p := by
  rw [colon_eq, splitOn_ofList]
  unfold tokK at h
  unfold tokLetters
  split at h
  · rename_i g e hs
    rw [hs]
    simp only [List.map_cons, List.map_nil, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
    obtain ⟨hg, he | ⟨he1, he2⟩⟩ := h
    · rw [toNat?_ofList hg, toInt?_ofList he]
      have hne : e.head? ≠ some '-' := by
        obtain ⟨hne, hd⟩ := digitsK_iff he
        cases e with
        | nil => exact absurd rfl hne
        | cons c cs =>
          intro hc
          simp only [List.head?_cons, Option.some.injEq] at hc
          subst hc
          exact absurd (hd '-' (by simp)) (by decide)
      simp [hne]
    · cases e with
      | nil => simp at he1
      | cons c t =>
        simp only [List.head?_cons, Option.some.injEq] at he1
        subst he1
        simp only [List.tail_cons] at he2
        rw [toNat?_ofList hg, toInt?_ofList_neg he2]
        simp only [List.head?_cons, ↓reduceIte, Left.nonneg_neg_iff]
        by_cases h0 : decVal t = 0
        · simp [h0]
        · have : ¬ ((decVal t : ℤ) ≤ 0) := by omega
          simp [this]
  · simp at h

theorem parseLetters_ofList (L : List Char) (h : (L.splitOn ' ').all tokK = true) :
    parseLetters (String.ofList L) = lettersK L := by
  unfold parseLetters lettersK
  rw [space_eq, splitOn_ofList, List.filter_map]
  have hf : List.filter ((fun p => decide (p ≠ "")) ∘ String.ofList) (L.splitOn ' ') =
      L.splitOn ' ' := by
    refine List.filter_eq_self.2 fun p hp => ?_
    simpa using ofList_ne_empty (tok_ne_nil (List.all_eq_true.1 h p hp))
  rw [hf, List.flatMap_map]
  refine List.flatMap_congr fun p hp => ?_
  exact tokLetters_eq (List.all_eq_true.1 h p hp)

theorem foldl_app (g : Char → ℕ) : ∀ (L : List String) (acc : Array ℕ),
    L.foldl (fun acc l => acc ++ (l.toList.map g).toArray) acc =
      acc ++ (L.flatMap fun l => l.toList.map g).toArray
  | [], acc => by simp
  | l :: L, acc => by
    rw [List.foldl_cons, foldl_app g L, List.flatMap_cons, Array.append_assoc]
    congr 1
    apply Array.toList_inj.1
    simp

theorem parseMats_ofList (cs : List Char) : parseMats (String.ofList cs) = matsK cs := by
  unfold parseMats matsK matL nonEmptyLines
  rw [nl_eq, splitOn_ofList, List.filter_map]
  have hf : ((fun l => decide (l ≠ "")) ∘ String.ofList) = fun l : List Char => !l.isEmpty := by
    funext l
    cases l with
    | nil => rfl
    | cons c l => simpa using ofList_ne_empty (List.cons_ne_nil c l)
  rw [hf]
  apply Array.toList_inj.1
  simp only [Array.toList_map, Array.toList_range, List.toList_toArray, List.length_map]
  refine List.map_congr_left fun k _ => ?_
  rw [foldl_app, Array.empty_append, ← List.map_drop, ← List.map_take, List.flatMap_map]
  simp only [toList_ofList]

theorem rowsOf_toArray (l : List ℕ) : rowsOf l.toArray = rowsL l := by
  unfold rowsOf rowsL
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem canonB_toArray {l : List ℕ} (h : (l.length == 144 && l.all (· < 3)) = true) :
    canonB l.toArray = true := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  unfold canonB
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨by simpa using h.1, fun i hi => ?_⟩
  simpa using h.2 _ (List.getElem_mem (by simpa using hi))

theorem matsK_getD (cs : List Char) {k : ℕ} (hk : k < (nonEmptyLines cs).length / 12) :
    (matsK cs).getD k oneM = (matL cs k).toArray := by
  unfold matsK
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hk]
  rfl

end CFSG.KC.EvenSporSuz
