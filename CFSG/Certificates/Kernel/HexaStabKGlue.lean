module

public import CFSG.Certificates.Kernel.N48KGlue
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabTests

public section

namespace CFSG.KC.HexaStabK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.N48K
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HeSylow
open CFSG.KLie.CT (anyN sumN andB orB notB pw2 bit)

theorem fld_pmk {n w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    PF.Fld w (pmk n w f) (fun i => if i < n then f i else 0) := by
  have hc := PF.clog_spec hn
  have h := PF.fld_pmkT n w f hf (clog n) 0
  have e : pmk n w f = pmkT n w f (clog n) 0 := by
    unfold pmk
    rw [PF.strictN_eqP]
  rw [e]
  refine PF.fld_congr h fun i => ?_
  by_cases hi : i < n
  · have h2 : i < 2 ^ clog n := by omega
    simp [hi, h2]
  · simp [hi]

theorem pg_pmk {n w i : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w)
    (hi : i < n) : pg w (mask w) (pmk n w f) i = f i := by
  rw [PF.pg_of_fld (fld_pmk hn hf) (by simp only [hi, ↓reduceIte]; exact hf i hi)]
  simp [hi]

theorem unpack_pmk {n w : Nat} {f : Nat → Nat} (hn : n < 16777216) (hf : ∀ x < n, f x < 2 ^ w) :
    unpack n w (pmk n w f) = Array.ofFn (n := n) fun x => f x.val := by
  unfold unpack
  congr 1
  funext x
  exact pg_pmk hn hf x.2

variable {w : Nat}

theorem translA_eq (hw : 64 < 2 ^ w) {v : Nat} (hv : v < 64) :
    translA v = unpack 64 w (translK w v) := by
  unfold translA translK
  rw [unpack_pmk (f := fun x => Nat.xor x v) (by norm_num) fun x hx => Nat.lt_trans
    (Nat.xor_lt_two_pow (n := 6) (by simpa using hx) (by simpa using hv)) hw]
  rfl

@[expose] noncomputable def linStep (imgs : List Nat) (v i acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (imgs.getD i 0)) (bit v i)

theorem linStep_eq (imgs : List Nat) (v i acc : Nat) :
    linStep imgs v i acc = if v.testBit i = true then acc ^^^ imgs[i]! else acc := by
  unfold linStep
  rw [bit_eq, List.getElem!_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  cases v.testBit i <;> rfl

theorem linVK_eq (imgs : List Nat) (v : Nat) : linVK imgs v = linV imgs v := by
  have e : linVK imgs v = linStep imgs v 5 (linStep imgs v 4 (linStep imgs v 3
      (linStep imgs v 2 (linStep imgs v 1 (linStep imgs v 0 0))))) := rfl
  rw [e]
  unfold linV
  simp only [List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, linStep_eq]

theorem linV_lt {imgs : List Nat} (h : ∀ x ∈ imgs, x < 64) (v : Nat) : linV imgs v < 64 := by
  have hi : ∀ i, imgs[i]! < 64 := fun i => by
    rw [List.getElem!_eq_getElem?_getD]
    cases e : imgs[i]? with
    | none => exact Nat.zero_lt_succ _
    | some x => exact h x (List.mem_of_getElem? e)
  unfold linV
  generalize (List.range 6) = l
  suffices ∀ acc, acc < 64 → l.foldl (fun acc i => if v.testBit i then acc ^^^ imgs[i]! else acc)
      acc < 64 from this 0 (by norm_num)
  induction l with
  | nil => exact fun acc h => h
  | cons i l ih =>
    intro acc hacc
    rw [List.foldl_cons]
    refine ih _ ?_
    split
    · exact Nat.xor_lt_two_pow (n := 6) hacc (hi i)
    · exact hacc

theorem linA_eq (hw : 64 < 2 ^ w) {imgs : List Nat} (h : ∀ x ∈ imgs, x < 64) :
    linA imgs = unpack 64 w (linK w imgs) := by
  unfold linA linK
  rw [unpack_pmk (by norm_num) fun x _ => by rw [linVK_eq]; exact Nat.lt_trans (linV_lt h x) hw]
  congr 1
  funext x
  rw [linVK_eq]

theorem memK_eq (L : List Nat) (y : Nat) : memK L y = L.contains y := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change CFSG.KLie.CT.orB (Nat.beq a y) (memK L y) = _
    have hab : Nat.beq a y = (y == a) :=
      Bool.eq_iff_iff.2 (by rw [beq_iff_eq, Nat.beq_eq]; exact eq_comm)
    rw [orB_eq, ih, List.contains_cons, hab]

theorem presL_eq (hw : 64 < 2 ^ w) {oval : List (List Nat)} (hov : ovalOK oval = true)
    {imgs : List Nat} (h : ∀ x ∈ imgs, x < 64) :
    presL oval imgs =
      oval.all fun L => oval.any fun L' => L.all fun x => L'.contains (linA imgs)[x]! := by
  unfold presL
  refine all_congr_mem fun L hL => ?_
  dsimp only
  refine any_congr_mem fun L' _ => ?_
  rw [List.all_map]
  refine all_congr_mem fun x hx => ?_
  have hx64 : x < 64 := by
    have := List.all_eq_true.1 (List.all_eq_true.1 hov L hL) x hx
    exact Nat.blt_eq.mp this
  rw [Function.comp_apply, memK_eq, linA_eq hw h, unpack_getElem!]
  simp only [hx64, ↓reduceIte]
  unfold linK
  rw [pg_pmk (by norm_num)
    (fun z _ => by rw [linVK_eq]; exact Nat.lt_trans (linV_lt h z) hw) hx64]

theorem orMask_testBit (g : Nat → Nat) (j : Nat) : ∀ k,
    (Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (pw2 (g x))) k : Nat).testBit j =
      (List.range k).any fun x => decide (g x = j)
  | 0 => by simp
  | k + 1 => by
    change Nat.testBit (_ ||| pw2 (g k)) j = _
    rw [Nat.testBit_or, orMask_testBit g j k, pw2_eq, Nat.testBit_two_pow, List.range_succ,
      List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem popK_eq_length (k X : Nat) : popK k X = ((List.range k).filter X.testBit).length := by
  unfold popK
  rw [← sumN_count]
  congr 1
  funext i
  rw [bit_eq]

theorem injK_of_injA {P : Nat} (h : injA (unpack 64 w P) = true) :
    injK w P = true := by
  unfold injK
  rw [popK_eq_length, pw2_eq]
  apply Nat.beq_eq.mpr
  set g : Nat → Nat := fun x => pgC 64 w P x
  have hinj : ∀ x < 64, ∀ y < 64, g x = g y → x = y := by
    intro x hx y hy e
    have := List.all_eq_true.1 (List.all_eq_true.1 h x (List.mem_range.2 hx)) y
      (List.mem_range.2 hy)
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with this | this
    · exact this
    · exact absurd (by rw [← pgC_eq, ← pgC_eq]; exact e) this
  have hlt : ∀ x, g x < 2 ^ w := fun x => by
    change pgC 64 w P x < _
    unfold pgC
    cases Nat.blt x 64
    · exact Nat.two_pow_pos w
    · exact PF.pg_lt _ _ _
  have hnd1 : ((List.range (2 ^ w)).filter fun j =>
      (Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (pw2 (pgC 64 w P x))) 64 :
        Nat).testBit j).Nodup := (List.nodup_range).filter _
  have hnd2 : ((List.range 64).map g).Nodup :=
    (List.nodup_range).map_on fun x hx y hy e =>
      hinj x (List.mem_range.1 hx) y (List.mem_range.1 hy) e
  have hset : ((List.range (2 ^ w)).filter fun j =>
      (Nat.rec (motive := fun _ => Nat) 0 (fun x acc => Nat.lor acc (pw2 (pgC 64 w P x))) 64 :
        Nat).testBit j).toFinset = ((List.range 64).map g).toFinset := by
    ext j
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, List.mem_map]
    rw [orMask_testBit]
    simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨-, x, hx, e⟩
      exact ⟨x, hx, e⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hlt x, x, hx, rfl⟩
  rw [← List.toFinset_card_of_nodup hnd1, hset, List.toFinset_card_of_nodup hnd2,
    List.length_map, List.length_range]

theorem length_flatMap_const {α β : Type} (l : List α) (g : α → List β) {m : Nat}
    (hg : ∀ x ∈ l, (g x).length = m) : (l.flatMap g).length = l.length * m := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, hg x List.mem_cons_self,
      ih fun y hy => hg y (List.mem_cons_of_mem x hy), List.length_cons, Nat.succ_mul,
      Nat.add_comm]

theorem getElem?_flatMap_const {α β : Type} (g : α → List β) {m : Nat} : ∀ (l : List α),
    (∀ x ∈ l, (g x).length = m) → ∀ i (hi : i < l.length), ∀ j < m,
      (l.flatMap g)[i * m + j]? = (g l[i])[j]?
  | [], _, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | x :: l, hg, 0, _, j, hj => by
    rw [List.flatMap_cons, Nat.zero_mul, Nat.zero_add,
      List.getElem?_append_left (by rw [hg x List.mem_cons_self]; exact hj)]
    rfl
  | x :: l, hg, i + 1, hi, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hg x List.mem_cons_self]; nlinarith),
      hg x List.mem_cons_self]
    have e : (i + 1) * m + j - m = i * m + j := by rw [Nat.succ_mul]; omega
    rw [e, getElem?_flatMap_const g l (fun y hy => hg y (List.mem_cons_of_mem x hy)) i
      (by simpa using hi) j hj]
    rfl

theorem getElem!_flatMap3 {α : Type} {β : Type} [Inhabited β] (l : List α)
    (f : α → α → α → β) {i j k : Nat} (hi : i < l.length) (hj : j < l.length)
    (hk : k < l.length) :
    (l.flatMap fun p => l.flatMap fun q => l.map fun r => f p q r)[(i * l.length + j) *
      l.length + k]! = f l[i] l[j] l[k] := by
  have h1 : ∀ q ∈ l, (l.map fun r => f l[i] q r).length = l.length := fun _ _ => by simp
  have h2 : ∀ p ∈ l, (l.flatMap fun q => l.map fun r => f p q r).length = l.length * l.length :=
    fun p _ => length_flatMap_const _ _ fun _ _ => by simp
  rw [List.getElem!_eq_getElem?_getD, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc,
    getElem?_flatMap_const _ l h2 i hi _ (by nlinarith),
    getElem?_flatMap_const _ l h1 j hj k hk, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

theorem length_flatMap3 {α : Type} {β : Type} (l : List α) (f : α → α → α → β) :
    (l.flatMap fun p => l.flatMap fun q => l.map fun r => f p q r).length =
      l.length * (l.length * l.length) :=
  length_flatMap_const _ _ fun _ _ => length_flatMap_const _ _ fun _ _ => by simp

theorem ovalPairs_lt {oval : List (List Nat)} (hov : ovalOK oval = true) {p : Nat × Nat}
    (hp : p ∈ oval.flatMap fun L => (L.filter (· != 0)).flatMap fun a =>
      ((L.filter (· != 0)).filter (· != a)).map fun b => (a, b)) : p.1 < 64 ∧ p.2 < 64 := by
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hp
  obtain ⟨L, hL, a, ⟨ha, -⟩, b, ⟨⟨hb, -⟩, -⟩, rfl⟩ := hp
  have hL' := List.all_eq_true.1 hov L hL
  exact ⟨Nat.blt_eq.mp (List.all_eq_true.1 hL' a ha), Nat.blt_eq.mp (List.all_eq_true.1 hL' b hb)⟩

end CFSG.KC.HexaStabK

end
