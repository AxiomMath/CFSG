module

public import Certificates.Data.Kernel.SuzGamma2294
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.Fi22Snd.Rows
import CFSG.Certificates.Kernel.Fi22Snd.AdjBfs

public section

namespace CFSG.KC.G2294

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KS.Raw CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore.Native

@[expose] noncomputable def unpackC (n C : Nat) : Array Nat :=
  Array.ofFn (n := n) fun v => cs C v.val

theorem unpackC_get {n C v : Nat} (hv : v < n) : (unpackC n C)[v]! = cs C v := by
  rw [unpackC, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]

theorem g2294S_rowOK_facts {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) :
    rg (R x) (d - 1) < n ∧ ∀ i < d - 1, rg (R x) i < rg (R x) (i + 1) := by
  unfold rowOK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  exact ⟨Nat.le_of_ble_eq_true h1,
    fun i hi => Nat.le_of_ble_eq_true (CFSG.KC.Pack.allN_spec h2 i hi)⟩

theorem g2294S_row_strict {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) {i j : Nat}
    (hij : i < j) (hj : j < d) : rg (R x) i < rg (R x) j := by
  obtain ⟨-, h2⟩ := g2294S_rowOK_facts h
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · exact lt_trans (ih hij (by omega)) (h2 j (by omega))
    · exact h2 i (by omega)

theorem g2294S_row_lt {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) {i : Nat}
    (hi : i < d) : rg (R x) i < n := by
  obtain ⟨h1, -⟩ := g2294S_rowOK_facts h
  rcases Nat.lt_or_ge i (d - 1) with hi' | hi'
  · exact lt_trans (g2294S_row_strict h hi' (by omega)) h1
  · obtain rfl : i = d - 1 := by omega
    exact h1

theorem g2294S_row_d_le {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) : d ≤ 65536 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · omega
  have key : ∀ i < d, i ≤ rg (R x) i := by
    intro i hi
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      exact Nat.succ_le_of_lt
        (lt_of_le_of_lt (ih (by omega)) (g2294S_row_strict h (Nat.lt_succ_self i) hi))
  have h1 := key (d - 1) (by omega)
  have h2 := CFSG.KC.Fi22Snd.rg_lt (R x) (d - 1)
  omega

theorem g2294S_row_pairwise {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) :
    (decodeRow d (R x)).Pairwise (· < ·) := by
  rw [CFSG.KC.Fi22Snd.decodeRow_eq, List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun _ hb hab =>
    g2294S_row_strict h hab (List.mem_range.1 hb)

theorem g2294S_row_entry_lt {n d x : Nat} {R : Nat → Nat} (h : rowOK n d R x = true) {p : Nat}
    (hp : p ∈ decodeRow d (R x)) : p < n := by
  rw [CFSG.KC.Fi22Snd.decodeRow_eq, List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact g2294S_row_lt h (List.mem_range.1 hi)

theorem g2294S_maskFold (h : Nat → Nat) {f : Nat → Nat → Nat}
    (hf : ∀ i a, f i a = (a ||| 2 ^ (64 + h i)) + 1) {m c : Nat} (hm : c + m < 2 ^ 64) (q : Nat) :
    (foldN m f c >>> 64).testBit q = decide (∃ i < m, h i = q) := by
  obtain ⟨B', h1, h2⟩ := CFSG.KC.Fi22Snd.maskFold_aux h hf m 0 c hm
  simp only [Nat.mul_zero, Nat.zero_add] at h1
  rw [CFSG.KC.Pack.foldN_eq, h1, Nat.shiftRight_eq_div_pow, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt hm, Nat.add_zero, h2]
  simp

theorem g2294S_imgMask_testBit {d s : Nat} (hd : s + d < 2 ^ 64) (G r q : Nat) :
    (Nat.shiftRight (imgMask d G r s) (nat_lit 64)).testBit q =
      decide (∃ i < d, gp G (rg r i) = q) :=
  g2294S_maskFold (fun i => gp G (rg r i))
    (f := fun i a => Nat.add (Nat.lor a (Nat.shiftLeft (nat_lit 1)
      (Nat.add (nat_lit 64) (gp G (rg r i))))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + gp G (rg r i))) + 1 = _
      rw [Nat.one_shiftLeft]) hd q

theorem g2294S_rowMask_testBit {d s : Nat} (hd : s + d < 2 ^ 64) (r q : Nat) :
    (Nat.shiftRight (rowMask d r s) (nat_lit 64)).testBit q = decide (q ∈ decodeRow d r) := by
  have h := g2294S_maskFold (rg r) (f := fun i a => Nat.add (Nat.lor a
    (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) (rg r i)))) (nat_lit 1))
    (fun i a => by
      change (a ||| 1 <<< (64 + rg r i)) + 1 = _
      rw [Nat.one_shiftLeft]) hd q
  refine h.trans (decide_eq_decide.2 ?_)
  simp [CFSG.KC.Fi22Snd.decodeRow_eq]

theorem g2294S_shift_bound {x d : Nat} (hx : x < 32768) (hd : d ≤ 65536) :
    Nat.shiftLeft x (nat_lit 16) + d < 2 ^ 64 := by
  have e : Nat.shiftLeft x (nat_lit 16) = x * 65536 := by
    change x <<< 16 = _
    rw [Nat.shiftLeft_eq]
  rw [e, show (2 : Nat) ^ 64 = 18446744073709551616 by norm_num]
  omega

theorem g2294S_unpack15 {n P i : Nat} (hi : i < n) : (unpack n 15 P)[i]! = gp P i :=
  (CFSG.KS.Raw.Orb.unpack_get hi).trans rfl

theorem g2294S_imgOK_facts {n d G x : Nat} {R : Nat → Nat} (h : imgOK n d G R x = true) :
    gp G x < n ∧ Nat.shiftRight (imgMask d G (R x) (Nat.shiftLeft x (nat_lit 16))) (nat_lit 64) =
      Nat.shiftRight (rowMask d (R (gp G x)) (Nat.shiftLeft (gp G x) (nat_lit 16)))
        (nat_lit 64) := by
  unfold imgOK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h2
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem g2294S_img {n d x P : Nat} {R : Nat → Nat} (hn : n < 32768)
    (hrow : ∀ x < n, rowOK n d R x = true) (himg : imgOK n d P R x = true) (hx : x < n) :
    imgSorted (unpack n 15 P) (decodeRow d (R x)) = decodeRow d (R (gp P x)) := by
  obtain ⟨hy, hmask⟩ := g2294S_imgOK_facts himg
  have hrx := hrow x hx
  have hry := hrow _ hy
  refine List.Perm.eq_of_sortedLE List.sortedLE_mergeSort
    (g2294S_row_pairwise hry).sortedLT.sortedLE ?_
  refine (List.mergeSort_perm _ _).trans ?_
  have hsub : decodeRow d (R (gp P x)) ⊆ (decodeRow d (R x)).map fun p => (unpack n 15 P)[p]! := by
    intro q hq
    have hb : (Nat.shiftRight (rowMask d (R (gp P x)) (Nat.shiftLeft (gp P x) (nat_lit 16)))
        (nat_lit 64)).testBit q = true := by
      rw [g2294S_rowMask_testBit (g2294S_shift_bound (by omega) (g2294S_row_d_le hry))]
      exact decide_eq_true hq
    rw [← hmask, g2294S_imgMask_testBit (g2294S_shift_bound (by omega) (g2294S_row_d_le hrx))]
      at hb
    obtain ⟨i, hi, hiq⟩ := of_decide_eq_true hb
    rw [List.mem_map]
    refine ⟨rg (R x) i, ?_, ?_⟩
    · rw [CFSG.KC.Fi22Snd.decodeRow_eq]
      exact List.mem_map_of_mem (List.mem_range.2 hi)
    · rw [g2294S_unpack15 (g2294S_row_lt hrx hi), hiq]
  have hperm := ((g2294S_row_pairwise hry).nodup.subperm hsub).perm_of_length_le (by
    rw [List.length_map, CFSG.KC.Fi22Snd.row_length, CFSG.KC.Fi22Snd.row_length])
  exact hperm.symm

theorem g2294S_treeOK_facts {n ng : Nat} {G T : Nat → Nat} {x : Nat}
    (h : treeOK n ng G T x = true) (hx : x ≠ 0) :
    ∃ p g, p < n ∧ g < ng ∧
      Nat.land (Nat.shiftRight (T p) (nat_lit 24)) (nat_lit 65535) <
        Nat.land (Nat.shiftRight (T x) (nat_lit 24)) (nat_lit 65535) ∧
      gp (G g) p = x := by
  unfold treeOK at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  have h0 : ¬ Nat.beq x (nat_lit 0) = true := fun hb => hx (Nat.eq_of_beq_eq_true hb)
  rw [if_neg h0, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h'⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h''⟩ := CFSG.KC.Pack.band_iff.1 h'
  obtain ⟨h3, h4⟩ := CFSG.KC.Pack.band_iff.1 h''
  exact ⟨_, _, Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem graph_sound {n d ng : Nat} {gens : Array (Array Nat)} {R G T : Nat → Nat}
    {root : List Nat} (hn0 : 0 < n) (hn : n < 32768) (hd : 0 < d) (hgs : gens.size = ng)
    (hG : ∀ k < ng, gens[k]! = unpack n 15 (G k))
    (hrow : ∀ x < n, rowOK n d R x = true)
    (himg : ∀ k < ng, ∀ x < n, imgOK n d (G k) R x = true)
    (htree : ∀ x < n, treeOK n ng G T x = true) (hsym : ∀ i < d, sym0OK R i = true)
    (hroot : root = decodeRow d (R 0)) :
    adjSearch n gens root = rowsArr n d R ∧ adjOK n gens (rowsArr n d R) root = true := by
  have hlt : ∀ k < gens.size, ∀ x < n, (gens[k]!)[x]! < n := by
    intro k hk x hx
    have hk' : k < ng := by omega
    rw [hG k hk', g2294S_unpack15 hx]
    exact (g2294S_imgOK_facts (himg k hk' x hx)).1
  have himg' : ∀ k < gens.size, ∀ x < n,
      imgSorted gens[k]! (decodeRow d (R x)) = decodeRow d (R (gens[k]!)[x]!) := by
    intro k hk x hx
    have hk' : k < ng := by omega
    rw [hG k hk', g2294S_unpack15 hx]
    exact g2294S_img hn hrow (himg k hk' x hx) hx
  have hreach : ∀ P : Nat → Prop, P 0 → (∀ p < n, P p → ∀ k < gens.size, P (gens[k]!)[p]!) →
      ∀ x < n, P x := by
    intro P h0 hcl
    have key : ∀ D x, x < n → Nat.land (Nat.shiftRight (T x) (nat_lit 24)) (nat_lit 65535) = D →
        P x := by
      intro D
      induction D using Nat.strong_induction_on with
      | _ D ih =>
        intro x hx hD
        by_cases hx0 : x = 0
        · subst hx0
          exact h0
        · obtain ⟨p, g, hp, hg, hdep, hpg⟩ := g2294S_treeOK_facts (htree x hx) hx0
          have hPp : P p := ih _ (hD ▸ hdep) p hp rfl
          have := hcl p hp hPp g (by omega)
          rwa [hG g hg, g2294S_unpack15 hp, hpg] at this
    exact fun x hx => key _ x hx rfl
  have h1 : adjSearch n gens root = rowsArr n d R := by
    rw [hroot]
    exact CFSG.KC.Fi22Snd.adjSearch_eq (Row := fun x => decodeRow d (R x)) hn0 hlt himg' hreach
  refine ⟨h1, ?_⟩
  unfold adjOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · simp [rowsArr]
  · rw [CFSG.KC.Fi22Snd.rowsArr_get hn0, hroot]
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro x hx
    rw [CFSG.KC.Fi22Snd.rowsArr_get hx, Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun y hy => decide_eq_true (g2294S_row_entry_lt (hrow x hx) hy),
      CFSG.KC.Fi22Snd.strictIncr_of_pairwise (g2294S_row_pairwise (hrow x hx))⟩
  · rw [CFSG.KC.Fi22Snd.rowsArr_get hn0, List.all_eq_true]
    intro y hy
    have hyn := g2294S_row_entry_lt (hrow 0 hn0) hy
    rw [CFSG.KC.Fi22Snd.decodeRow_eq, List.mem_map] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hs : rg (R (rg (R 0) i)) 0 = 0 := Nat.eq_of_beq_eq_true (hsym i (List.mem_range.1 hi))
    have hm : 0 ∈ decodeRow d (R (rg (R 0) i)) := by
      rw [CFSG.KC.Fi22Snd.decodeRow_eq]
      exact List.mem_map.2 ⟨0, List.mem_range.2 hd, hs⟩
    rw [CFSG.KC.Fi22Snd.rowsArr_get hyn]
    simpa using hm
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro x hx
    rw [beq_iff_eq, CFSG.KC.Fi22Snd.rowsArr_get (hlt k hk x hx), CFSG.KC.Fi22Snd.rowsArr_get hx]
    exact (himg' k hk x hx).symm

theorem g2294S_modE (a b : Nat) : Nat.mod a b = a % b := rfl

theorem g2294S_hcol_eq (x : Nat) : hcol x = hcK x := by
  simp only [hcol, hcK, cmod, CFSG.KC.Pack.strictN_eq, g2294S_modE, Nat.add_eq, Nat.mul_eq]

theorem g2294S_stepCol_eq (c s : Nat) :
    ((c % cmod () * 1000003 + c % cmod ()) % cmod () * 1000003 + s) % cmod () = stepCol c s := by
  simp only [stepCol, cmK, cmod, g2294S_modE, Nat.add_eq, Nat.mul_eq]

theorem g2294S_rowLt {n d : Nat} {R : Nat → Nat} (hd : 0 < d)
    (hrow : ∀ x < n, rowOK n d R x = true) : ∀ x < n, ∀ i < d, rg (R x) i < n := by
  intro x hx i hi
  have h := hrow x hx
  unfold rowOK at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.band_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hinc : ∀ j, j + 1 < d → rg (R x) j < rg (R x) (j + 1) := fun j hj => by
    have := CFSG.KC.Pack.allN_spec h2 j (by change j < d - 1; omega)
    rwa [Nat.blt_eq] at this
  have hle : ∀ k, ∀ i, i + k = d - 1 → rg (R x) i ≤ rg (R x) (d - 1) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      rw [← hi, Nat.add_zero]
    | succ k ih =>
      intro i hi
      exact le_trans (le_of_lt (hinc i (by omega))) (ih (i + 1) (by omega))
  exact lt_of_le_of_lt (hle (d - 1 - i) i (by omega)) h1

theorem g2294S_foldr_sum (g : Nat → Nat) (l : List Nat) :
    l.foldr (fun i a => Nat.add a (g i)) 0 = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, ih, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

theorem g2294S_hashAt {n C H w : Nat} (hH : ∀ v < n, hashOK C H v = true) (hw : w < n) :
    hcol (unpackC n C)[w]! = cs H w := by
  have hH' : cs H w = hcK (cs C w) := Nat.eq_of_beq_eq_true (hH w hw)
  rw [unpackC_get hw, g2294S_hcol_eq, hH']

theorem g2294S_hsum {d H r : Nat} : hsum d H r = ((List.range d).map fun i => cs H (rg r i)).sum := by
  unfold hsum
  rw [CFSG.KC.Pack.foldN_eq, g2294S_foldr_sum]

theorem g2294S_nbrRow {n d v : Nat} {R : Nat → Nat} (c : Array Nat) (hv : v < n) :
    nbrSum (rowsArr n d R) c v = ((List.range d).map fun i => hcol c[rg (R v) i]!).sum := by
  unfold nbrSum
  rw [rowsArr, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn,
    CFSG.KC.Fi22Snd.decodeRow_eq, List.map_map]
  rfl

theorem g2294S_nbr {n d : Nat} {R : Nat → Nat} {C H v : Nat}
    (hrow' : ∀ x < n, ∀ i < d, rg (R x) i < n) (hH : ∀ v < n, hashOK C H v = true) (hv : v < n) :
    nbrSum (rowsArr n d R) (unpackC n C) v = hsum d H (R v) := by
  rw [g2294S_nbrRow _ hv, g2294S_hsum]
  exact congrArg List.sum (List.map_congr_left fun i hi =>
    g2294S_hashAt hH (hrow' v hv i (List.mem_range.1 hi)))

theorem g2294S_idA {n v : Nat} (hv : v < n) : (idA n)[v]! = v := by
  rw [idA, getElem!_pos _ v (by simpa using hv), Array.getElem_ofFn]

theorem g2294S_unpackC_ofFn {n C v : Nat} (hv : v < (unpackC n C).size) :
    (unpackC n C)[v]'hv = cs C v := by
  simp only [unpackC, Array.getElem_ofFn]

theorem g2294S_round {d : Nat} {R : Nat → Nat} {C H C' v : Nat}
    (h : roundOK d R C H C' v = true) : cs C' v = stepCol (cs C v) (hsum d H (R v)) := by
  unfold roundOK at h
  rw [CFSG.KC.Pack.strictB_eq] at h
  exact Nat.eq_of_beq_eq_true h

theorem step_sound {n d : Nat} {R : Nat → Nat} {C H C' : Nat} (hd : 0 < d)
    (hrow : ∀ x < n, rowOK n d R x = true) (hH : ∀ v < n, hashOK C H v = true)
    (hC : ∀ v < n, roundOK d R C H C' v = true) :
    stepT n (rowsArr n d R) (idA n) (unpackC n C) = unpackC n C' := by
  apply Array.ext
  · simp [stepT, unpackC]
  · intro v hv1 hv2
    have hv : v < n := by simpa [stepT] using hv1
    rw [g2294S_unpackC_ofFn hv2, g2294S_round (hC v hv)]
    simp only [stepT, Array.getElem_ofFn]
    rw [g2294S_idA hv, unpackC_get hv, g2294S_nbr (g2294S_rowLt hd hrow) hH hv]
    exact g2294S_stepCol_eq _ _

theorem g2294S_strictIncr : ∀ l : List Nat, l.Pairwise (· < ·) → strictIncr l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have hab : a < b := List.rel_of_pairwise_cons h List.mem_cons_self
    have ht := g2294S_strictIncr (b :: l) (List.Pairwise.of_cons h)
    simp [strictIncr, hab, ht]

theorem inj_sound {n C P : Nat} (h : injK n C P = true) : colInj n (unpackC n C) = true := by
  unfold injK at h
  have h' : (allN n (fun i => Nat.blt (rg P i) n) && allN (Nat.sub n 1) (fun i =>
      Nat.blt (cs C (rg P i)) (cs C (rg P (Nat.add i 1))))) = true := by
    rw [← h]
    cases allN n (fun i => Nat.blt (rg P i) n) <;> rfl
  rw [Bool.and_eq_true] at h'
  obtain ⟨h1, h2⟩ := h'
  have hP : ∀ i < n, rg P i < n := fun i hi => by
    have := CFSG.KC.Pack.allN_spec h1 i hi
    rwa [Nat.blt_eq] at this
  have hinc : ∀ i, i + 1 < n → cs C (rg P i) < cs C (rg P (i + 1)) := fun i hi => by
    have := CFSG.KC.Pack.allN_spec h2 i (by change i < n - 1; omega)
    rwa [Nat.blt_eq] at this
  have hmono : ∀ i j, i < j → j < n → cs C (rg P i) < cs C (rg P j) := by
    intro i j hij hj
    induction j, hij using Nat.le_induction with
    | base => exact hinc i hj
    | succ k hk ih => exact Nat.lt_trans (ih (by omega)) (hinc k hj)
  set M := (List.range n).map (fun i => cs C (rg P i)) with hM
  have hMs : M.Pairwise (· < ·) := by
    rw [hM, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := n))
    intro a b ha hb hab
    exact hmono a b hab (List.mem_range.1 hb)
  set A := (List.range n).map (rg P) with hA
  have hAn : A.Nodup := by
    rw [hA]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro a ha b hb e
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · exact absurd (congrArg (cs C) e) (Nat.ne_of_lt (hmono a b hab (List.mem_range.1 hb)))
    · exact hab
    · exact absurd (congrArg (cs C) e) (Nat.ne_of_gt (hmono b a hab (List.mem_range.1 ha)))
  have hAp : A.Perm (List.range n) := by
    refine (hAn.subperm fun x hx => ?_).perm_of_length_le (by simp [hA])
    rw [hA, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact List.mem_range.2 (hP i (List.mem_range.1 hi))
  have hL : ((List.range n).map fun w => (unpackC n C)[w]!) = (List.range n).map (cs C) :=
    List.map_congr_left fun w hw => unpackC_get (List.mem_range.1 hw)
  have hLM : ((List.range n).map (cs C)).Perm M := by
    have e : M = A.map (cs C) := by
      rw [hM, hA, List.map_map]
      rfl
    rw [e]
    exact (hAp.map (cs C)).symm
  unfold colInj
  dsimp only
  rw [hL]
  apply g2294S_strictIncr
  have hperm := (List.mergeSort_perm ((List.range n).map (cs C))
    (fun a b => decide (a ≤ b))).trans hLM
  have hsort := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by
      rcases Nat.le_total a b with hab | hab <;> simp [hab])
    ((List.range n).map (cs C))
  have hnd := hperm.nodup_iff.2 hMs.nodup
  refine (hsort.and hnd).imp ?_
  intro a b ⟨hab, hne⟩
  simp only [decide_eq_true_eq] at hab
  omega

theorem cellCnt_eq (n C col : Nat) : cellCnt n C col = cellCount n (unpackC n C) col := by
  rw [cellCnt, CFSG.KC.Pack.foldN_eq, cellCount]
  have key : ∀ m ≤ n, ∀ s, (List.range m).foldr
      (fun w a => nIf(Nat.beq (cs C w) col, Nat.add a (nat_lit 1), a)) s =
      s + (List.range m).countP fun w => (unpackC n C)[w]! == col := by
    intro m
    induction m with
    | zero => intro _ s; rfl
    | succ m ih =>
      intro hm s
      rw [List.range_succ, List.foldr_append, List.countP_append, List.foldr_cons, List.foldr_nil,
        ih (by omega), List.countP_singleton, unpackC_get (by omega)]
      have e : (cs C m == col) = Nat.beq (cs C m) col := rfl
      rw [e]
      cases Nat.beq (cs C m) col
      · rfl
      · change s + 1 + _ = s + (_ + if true = true then 1 else 0)
        rw [if_pos rfl]
        omega
  have h := key n le_rfl 0
  rw [Nat.zero_add] at h
  exact h

end CFSG.KC.G2294

end
