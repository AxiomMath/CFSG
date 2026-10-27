module

public import CFSG.Certificates.Kernel.Fi22LH.Rows
public import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.Pop
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.Certificates.Kernel.Fi22LH.Trees
import CFSG.Certificates.Kernel.Fi22LH.RowPhi
import CFSG.Certificates.Kernel.Fi22LH.StarFacts
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.List.Sort

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.TW CFSG.KC.Enum
  CFSG.F4.Native

variable {D : LHData}

theorem root_get (h : LHChecks D) {j : Nat} (hj : j < 351) :
    (lhData ())[0]![j]! = ent D.lb0 j ∧ (lhData ())[1]![j]! = ent D.lb1 j :=
  ⟨(h.lb0 j hj).symm, (h.lb1 j hj).symm⟩

theorem dataOK_gen {S : Array Nat} (hS : S.size = 351) {lb : Nat}
    (hSj : ∀ j < 351, S[j]! = ent lb j) (hinc : incK lb = true) (h0 : ent lb 0 = 0) :
    (S.size == 351 && S[0]! == 0 && allIn 0 350 (fun k => S[k]! < S[k + 1]!) &&
      S[350]! < 3510) = true := by
  obtain ⟨hi, hlt⟩ := incK_spec hinc
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨by rw [hS]; rfl, by rw [hSj 0 (by decide), h0]; rfl⟩, ?_⟩,
    by rw [hSj 350 (by decide)]; exact decide_eq_true (hlt 350 (by decide))⟩
  rw [allIn_iff]
  intro k hk
  rw [hSj k (by omega), hSj (k + 1) (by omega), decide_eq_true_eq]
  exact hi k (k + 1) (by omega) (by omega)

theorem c_dataOK (h : LHChecks D) : dataOK (lhData ()) = true := by
  unfold dataOK
  rw [Bool.and_eq_true, Array.all_eq_true]
  refine ⟨rfl, fun i hi => ?_⟩
  have hi2 : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · rw [← getElem!_pos (lhData ()) 0 hi]
    exact dataOK_gen lhData0_size (fun j hj => (root_get h hj).1) (walk_rest h.walkA).2.1
      (walk_rest h.walkA).2.2
  · rw [← getElem!_pos (lhData ()) 1 hi]
    exact dataOK_gen lhData1_size (fun j hj => (root_get h hj).2) (walk_rest h.walkB).2.1
      (walk_rest h.walkB).2.2

theorem memOK_gen {S : Array Nat} (hS : ∀ a ∈ S, a < 3520) : memOK (bitsOf S) S = true := by
  unfold memOK
  rw [allIn_iff]
  intro x hx
  rw [beq_iff_eq]
  apply Bool.eq_iff_iff.2
  rw [(bitsIs_bitsOf hS).2 x (by omega), Array.contains_iff_mem]

theorem root_lt {S : Array Nat} (hS : S.size = 351) {lb : Nat}
    (hSj : ∀ j < 351, S[j]! = ent lb j) (hinc : incK lb = true) : ∀ a ∈ S, a < 3520 := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 ha
  have := (incK_spec hinc).2 j (by omega)
  rw [← hSj j (by omega), getElem!_pos S j hj] at this
  omega

theorem c_mem0 (h : LHChecks D) : memOK (bitsOf (lhData ())[0]!) (lhData ())[0]! = true :=
  memOK_gen (root_lt lhData0_size (fun j hj => (root_get h hj).1) (walk_rest h.walkA).2.1)

theorem c_mem1 (h : LHChecks D) : memOK (bitsOf (lhData ())[1]!) (lhData ())[1]! = true :=
  memOK_gen (root_lt lhData1_size (fun j hj => (root_get h hj).2) (walk_rest h.walkB).2.1)

theorem closedOK_gen (hO : OrbOK) (h : LHChecks D) {lb : Nat} {B : Bits}
    (hB : BitsIs B fun y => ∃ j < 351, ent lb j = y) (hinc : incK lb = true)
    (hc : closedK D.R lb (bs lb) = true) : closedOK (tauAll orbL) B = true := by
  obtain ⟨-, hlt⟩ := incK_spec hinc
  unfold closedOK
  rw [allIn_iff]
  intro s hs
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hbs : bitAt B s = true
  · right
    obtain ⟨j, hj, rfl⟩ := (hB.2 _ (by omega)).1 hbs
    rw [allIn_iff]
    intro t ht
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hbt : bitAt B t = true
    · right
      obtain ⟨j', hj', rfl⟩ := (hB.2 _ (by omega)).1 hbt
      have hcl := allN_iff.1 hc j hj
      rw [strictB_eq] at hcl
      have := allN_iff.1 hcl j' hj'
      rw [memB_eq, testBit_bs] at this
      rw [((tauAll_TR hO h _ (hlt j hj)).2 _ ht).1]
      exact (hB.2 _ (by have := ((tauAll_TR hO h _ (hlt j hj)).2 _ ht).2; omega)).2 this
    · left
      exact Bool.eq_false_iff.2 hbt
  · left
    exact Bool.eq_false_iff.2 hbs

theorem c_closed0 (hO : OrbOK) (h : LHChecks D) :
    closedOK (tauAll orbL) (bitsOf (lhData ())[0]!) = true :=
  closedOK_gen hO h (B0_bits h) (walk_rest h.walkA).2.1 (rootW_spec h.rootX).1

theorem c_closed1 (hO : OrbOK) (h : LHChecks D) :
    closedOK (tauAll orbL) (bitsOf (lhData ())[1]!) = true :=
  closedOK_gen hO h (B1_bits h) (walk_rest h.walkB).2.1 (rootW_spec h.rootY).1

theorem anyBelow_iff {n : Nat} {p : Nat → Bool} : anyBelow n p = true ↔ ∃ x < n, p x = true := by
  unfold anyBelow
  simp

theorem fixed_count {lb : Nat} {B : Bits} (hB : BitsIs B fun y => ∃ j < 351, ent lb j = y)
    (hinc : incK lb = true) {t : Table} {g : Nat → Nat} (ht : ∀ x < 3510, ap t x = g x) :
    (List.range 3510).countP (fun x => bitAt B x && ap t x == x) =
      ∑ j ∈ Finset.range 351, (if g (ent lb j) = ent lb j then 1 else 0) := by
  classical
  obtain ⟨hi, hlt⟩ := incK_spec hinc
  have hinj : ∀ i < 351, ∀ j < 351, ent lb i = ent lb j → i = j := by
    intro i hi' j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := hi i j h1 hj
      omega
    · have := hi j i h1 hi'
      omega
  rw [countP_range, ← Finset.card_filter]
  rw [show (∑ i ∈ Finset.range 3510, (bitAt B i && ap t i == i).toNat) =
      ∑ i ∈ Finset.range 3510, if (bitAt B i && ap t i == i) = true then 1 else 0 from
    Finset.sum_congr rfl fun i _ => by cases (bitAt B i && ap t i == i) <;> rfl,
    ← Finset.card_filter]
  have e : (Finset.range 3510).filter (fun x => (bitAt B x && ap t x == x) = true) =
      ((Finset.range 351).filter fun j => g (ent lb j) = ent lb j).image (ent lb) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Bool.and_eq_true,
      beq_iff_eq]
    constructor
    · rintro ⟨hx, hb, hf⟩
      obtain ⟨j, hj, rfl⟩ := (hB.2 _ (by omega)).1 hb
      exact ⟨j, ⟨hj, by rw [← ht _ hx]; exact hf⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hf⟩, rfl⟩
      exact ⟨hlt j hj, (hB.2 _ (by have := hlt j hj; omega)).2 ⟨j, hj, rfl⟩,
        by rw [ht _ (hlt j hj)]; exact hf⟩
  rw [e, Finset.card_image_of_injOn]
  intro i hi' j hj e
  exact hinj i (Finset.mem_range.1 (Finset.mem_filter.1 hi').1) j
    (Finset.mem_range.1 (Finset.mem_filter.1 hj).1) e

theorem c_count63 (hO : OrbOK) (h : LHChecks D) :
    count63OK (tauAll orbL) (bitsOf (lhData ())[0]!) = true := by
  unfold count63OK
  rw [allIn_iff]
  intro f hf
  rw [B0_at h hf, Bool.or_eq_true]
  cases hb : (bs D.lb0).testBit f
  · right
    rw [beq_iff_eq, fixed_count (B0_bits h) (walk_rest h.walkA).2.1
      (fun x hx => ((tauAll_TR hO h f hf).2 x hx).1)]
    exact ((rowF_spec h hf).2 hb).2.2.2.2
  · exact Or.inl rfl

theorem dom_of_count {lb : Nat} {B : Bits} (hB : BitsIs B fun y => ∃ j < 351, ent lb j = y)
    (hinc : incK lb = true) {t : Table} {g : Nat → Nat} (ht : ∀ x < 3510, ap t x = g x)
    (hc : 0 < ∑ j ∈ Finset.range 351, (if g (ent lb j) = ent lb j then 1 else 0))
    (hc' : ∑ j ∈ Finset.range 351, (if g (ent lb j) = ent lb j then 1 else 0) < 351) :
    (anyBelow 3510 (fun x => bitAt B x && ap t x == x) &&
      anyBelow 3510 (fun x => bitAt B x && ap t x != x)) = true := by
  classical
  obtain ⟨-, hlt⟩ := incK_spec hinc
  rw [Bool.and_eq_true, anyBelow_iff, anyBelow_iff]
  constructor
  · obtain ⟨j, hj, hjf⟩ : ∃ j ∈ Finset.range 351, g (ent lb j) = ent lb j := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero fun j hj => if_neg (hne j hj)] at hc
      omega
    refine ⟨ent lb j, hlt j (Finset.mem_range.1 hj), ?_⟩
    rw [Bool.and_eq_true, beq_iff_eq, ht _ (hlt j (Finset.mem_range.1 hj)), hjf]
    exact ⟨(hB.2 _ (by have := hlt j (Finset.mem_range.1 hj); omega)).2
      ⟨j, Finset.mem_range.1 hj, rfl⟩, rfl⟩
  · obtain ⟨j, hj, hjf⟩ : ∃ j ∈ Finset.range 351, g (ent lb j) ≠ ent lb j := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_congr rfl fun j hj => if_pos (hne j hj), Finset.sum_const,
        Finset.card_range] at hc'
      simp at hc'
    refine ⟨ent lb j, hlt j (Finset.mem_range.1 hj), ?_⟩
    rw [Bool.and_eq_true, bne_iff_ne, ht _ (hlt j (Finset.mem_range.1 hj))]
    exact ⟨(hB.2 _ (by have := hlt j (Finset.mem_range.1 hj); omega)).2
      ⟨j, Finset.mem_range.1 hj, rfl⟩, hjf⟩

theorem c_dom0 (hO : OrbOK) (h : LHChecks D) :
    domOK (tauAll orbL) (bitsOf (lhData ())[0]!) = true := by
  unfold domOK
  rw [allIn_iff]
  intro f hf
  rw [B0_at h hf, Bool.or_eq_true]
  cases hb : (bs D.lb0).testBit f
  · right
    have h63 := ((rowF_spec h hf).2 hb).2.2.2.2
    exact dom_of_count (B0_bits h) (walk_rest h.walkA).2.1
      (fun x hx => ((tauAll_TR hO h f hf).2 x hx).1) (by omega) (by omega)
  · exact Or.inl rfl

theorem domK_spec (h : LHChecks D) {f : Nat} (hf : f < 3510) (hb : (bs D.lb1).testBit f = false) :
    0 < ∑ j ∈ Finset.range 351, (if ent (D.R f) (ent D.lb1 j) = ent D.lb1 j then 1 else 0) ∧
      ∑ j ∈ Finset.range 351, (if ent (D.R f) (ent D.lb1 j) = ent D.lb1 j then 1 else 0) < 351 := by
  have hs := h.dom (f / 880) (by omega)
  unfold domSlW domSl at hs
  rw [strictB_eq] at hs
  have := allN_iff.1 hs (f % 880) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.mul (nat_lit 880) (f / 880)) (f % 880) = f := by
    change 880 * (f / 880) + f % 880 = f
    omega
  rw [strictB_eq, e, bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hf)] at this
  unfold domK at this
  rw [bIf_eq, memB_eq, hb, if_neg (by simp), strictB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true,
    Nat.blt_eq, Nat.blt_eq, sum351_eq] at this
  simp only [strictN_eq, nIf_eq, Nat.beq_eq] at this
  exact this

theorem c_dom1 (hO : OrbOK) (h : LHChecks D) :
    domOK (tauAll orbL) (bitsOf (lhData ())[1]!) = true := by
  unfold domOK
  rw [allIn_iff]
  intro f hf
  have hb1 : bitAt (bitsOf (lhData ())[1]!) f = (bs D.lb1).testBit f := by
    apply Bool.eq_iff_iff.2
    rw [(B1_bits h).2 f (by omega), testBit_bs]
  rw [hb1, Bool.or_eq_true]
  cases hb : (bs D.lb1).testBit f
  · right
    obtain ⟨c1, c2⟩ := domK_spec h hf hb
    exact dom_of_count (B1_bits h) (walk_rest h.walkB).2.1
      (fun x hx => ((tauAll_TR hO h f hf).2 x hx).1) c1 c2
  · exact Or.inl rfl

theorem filter_range_rank (p : Nat → Bool) : ∀ n x, x < n → p x = true →
    ((List.range n).filter p)[(List.range x).countP p]? = some x
  | 0, x, hx, _ => absurd hx (Nat.not_lt_zero x)
  | n + 1, x, hx, hp => by
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx' | rfl
    · have ih := filter_range_rank p n x hx' hp
      obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 ih
      rw [List.getElem?_append_left hl, ih]
    · rw [List.countP_eq_length_filter, List.getElem?_append_right (le_refl _), Nat.sub_self]
      simp [hp]

theorem ea_toList (hO : OrbOK) (h : LHChecks D) :
    (eaPts orbL).toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k := by
  unfold eaPts
  rw [List.toList_toArray]
  apply List.filter_congr
  intro k hk
  rw [(ent_al hO h (List.mem_range.1 hk)).1]

theorem ea_size (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k) :
    E.size = 693 := by
  rw [← Array.length_toList, hE, ← List.countP_eq_length_filter, h.al]
  exact star_count

set_option exponentiation.threshold 3584 in
theorem pop_below (s : Nat) {x : Nat} (hx : x ≤ 3584) :
    popK masks (Nat.land s (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1))) =
      (List.range x).countP fun y => s.testBit y := by
  have e : Nat.land s (Nat.sub (Nat.shiftLeft (nat_lit 1) x) (nat_lit 1)) = s % 2 ^ x := by
    rw [shiftLeft_one]
    exact Nat.and_two_pow_sub_one_eq_mod s x
  have hle : 2 ^ x ≤ 2 ^ 3584 := Nat.pow_le_pow_right (n := 2) (Nat.succ_pos 1) hx
  have hlt : s % 2 ^ x < 2 ^ 3584 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos x)) hle
  rw [e, popK_eq hlt, countP_range, countP_range]
  simp only [Nat.testBit_mod_two_pow]
  have e2 : 3584 = x + (3584 - x) := by omega
  have hz : ∑ i ∈ Finset.range (3584 - x), (decide (x + i < x) && s.testBit (x + i)).toNat = 0 :=
    Finset.sum_eq_zero fun i _ => by simp
  rw [e2, Finset.sum_range_add, hz, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [decide_eq_true (Finset.mem_range.1 hi), Bool.true_and]

theorem starK_at (h : LHChecks D) {x : Nat} (hx : x < 3510) :
    D.eb.testBit x = (x != 0 && ent D.al x == x) ∧
    (D.eb.testBit x = true →
      ∀ c, ent D.up (fld(D.pd, Nat.mul (nat_lit 10)
        ((List.range x).countP fun y => D.eb.testBit y), nat_lit 1023)) = c →
      D.h0.testBit x = hy 0 c ∧ D.h1.testBit x = hy 1 c ∧ D.h2.testBit x = hy 2 c ∧
        (bs D.lb0).testBit x = D.h0.testBit x ∧ (bs D.lb1).testBit x = D.h2.testBit x) ∧
    (D.eb.testBit x = false →
      D.h0.testBit x = false ∧ D.h1.testBit x = false ∧ D.h2.testBit x = false) := by
  have hs := h.star
  unfold starW starK at hs
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, allN_iff] at hs
  have hx' := hs.2 x hx
  rw [pop_below D.eb (by omega)] at hx'
  simp only [bEq_eq, bIf_eq, notB_eq, memB_eq, strictB_eq, bAnd_eq, Bool.and_eq_true, beq_iff_eq,
    Nat.beq_eq] at hx'
  obtain ⟨h1, h2⟩ := hx'
  refine ⟨?_, fun hb c hc => ?_, fun hb => ?_⟩
  · rw [h1]
    apply Bool.eq_iff_iff.2
    simp [beq_dec]
  · rw [if_pos hb, hc] at h2
    simpa only [Bool.and_eq_true, beq_iff_eq] using h2
  · rw [if_neg (by rw [hb]; decide)] at h2
    simpa using h2

theorem mono_of_step {f : Nat → Nat} {n : Nat} (hf : ∀ i, i + 1 < n → f i < f (i + 1)) {i j : Nat}
    (hij : i < j) (hj : j < n) : f i < f j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
    · exact (ih h' (by omega)).trans (hf j hj)
    · exact hf i hj

theorem up_get (h : LHChecks D) {k : Nat} (hk : k < 693) : ent D.up k = uPts[k]! := by
  have hu := h.up
  unfold upK at hu
  simp only [bAnd_eq, Bool.and_eq_true, strictB_eq, allN_iff] at hu
  obtain ⟨hinc, hmem⟩ := hu
  have hL : (uPts ()).toList = (List.range 693).map (ent D.up) := by
    unfold uPts
    rw [List.toList_toArray]
    refine List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) ?_ fun c => ?_
    · rw [List.pairwise_map]
      refine List.pairwise_lt_range.imp_of_mem ?_
      intro i j _ hj hij
      exact mono_of_step (n := 693) (fun i hi => by
        have := hinc i (by omega)
        rw [Nat.blt_eq] at this
        exact this) hij (List.mem_range.1 hj)
    · rw [List.mem_filter, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨hc, hp⟩
        have hm := hmem c hc
        rw [bEq_eq, upP_eq c hc, hp, memB_eq] at hm
        obtain ⟨i, hi, e⟩ := (testBit_bsF_zero (n := 693) (d := 10) (by decide) _ c).1 (by simpa using hm)
        exact ⟨i, List.mem_range.2 hi, e⟩
      · rintro ⟨i, hi, rfl⟩
        have hc := ent_lt D.up i
        refine ⟨hc, ?_⟩
        have hm := hmem _ hc
        rw [bEq_eq, upP_eq _ hc, memB_eq,
          (testBit_bsF_zero (n := 693) (d := 10) (by decide) _ _).2 ⟨i, List.mem_range.1 hi, rfl⟩] at hm
        simpa using hm
  have hsz : (uPts ()).size = 693 := by
    rw [← Array.length_toList, hL, List.length_map, List.length_range]
  rw [getElem!_pos (uPts ()) k (by rw [hsz]; exact hk), ← Array.getElem_toList]
  simp only [hL, List.getElem_map, List.getElem_range]

theorem phiPos_inv {u : Nat} (hu : u < 693) : phiPos[u]! < 693 ∧ phiData[phiPos[u]!]! = u := by
  have hp : phiPos[u]! = phiData.toList.idxOf u := by
    unfold phiPos
    rw [getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]
  have hm : u ∈ phiData.toList := by
    have := pd_mem u hu
    rw [Array.contains_iff_mem] at this
    exact Array.mem_toList_iff.2 this
  have hl : phiData.toList.idxOf u < phiData.toList.length := List.idxOf_lt_length_of_mem hm
  rw [hp]
  refine ⟨by simpa [pd_size] using hl, ?_⟩
  rw [getElem!_pos phiData _ (by simpa using hl), ← Array.getElem_toList]
  exact List.getElem_idxOf hl

theorem ePos_get {e : Array Nat} {x : Nat} (hx : x < 3510) : (ePos e)[x]! = e.toList.idxOf x := by
  unfold ePos
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

theorem ea_nodup {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k) :
    E.toList.Nodup := by
  rw [hE]
  exact List.nodup_range.filter _

theorem ea_get (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k)
    {i : Nat} (hi : i < 693) :
    E[i]! < 3510 ∧ D.eb.testBit E[i]! = true ∧ (ePos E)[E[i]!]! = i := by
  have hs := ea_size h hE
  have hl : i < E.toList.length := by rw [Array.length_toList, hs]; exact hi
  have e : E[i]! = E.toList[i] := by
    rw [getElem!_pos _ i (by rw [hs]; exact hi), Array.getElem_toList]
  have hmem : E.toList[i] ∈ (List.range 3510).filter fun k => k != 0 && ent D.al k == k := by
    rw [← hE]
    exact List.getElem_mem hl
  rw [List.mem_filter, List.mem_range] at hmem
  rw [e]
  refine ⟨hmem.1, by rw [(starK_at h hmem.1).1]; exact hmem.2, ?_⟩
  rw [ePos_get hmem.1]
  have := List.get_idxOf (ea_nodup hE) ⟨i, hl⟩
  simp only [List.get_eq_getElem] at this
  exact this

theorem star_pt (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k)
    {x : Nat} (hx : x < 3510) (hb : D.eb.testBit x = true) :
    (ePos E)[x]! < 693 ∧
      D.h0.testBit x = hypC 0 uPts[phiData[(ePos E)[x]!]!]! ∧
      D.h1.testBit x = hypC 1 uPts[phiData[(ePos E)[x]!]!]! ∧
      D.h2.testBit x = hypC 2 uPts[phiData[(ePos E)[x]!]!]! ∧
      (bs D.lb0).testBit x = D.h0.testBit x ∧ (bs D.lb1).testBit x = D.h2.testBit x := by
  obtain ⟨hst, hon, -⟩ := starK_at h hx
  have hpx : (x != 0 && ent D.al x == x) = true := by rw [← hst]; exact hb
  have hcnt : ((List.range x).countP fun y => D.eb.testBit y) =
      (List.range x).countP fun k => k != 0 && ent D.al k == k := by
    apply List.countP_congr
    intro y hy
    rw [(starK_at h (by have := List.mem_range.1 hy; omega)).1]
  have hr := filter_range_rank (fun k => k != 0 && ent D.al k == k) 3510 x hx hpx
  rw [← hE] at hr
  obtain ⟨hl, hrx⟩ := List.getElem?_eq_some_iff.1 hr
  have hl' : (List.range x).countP (fun k => k != 0 && ent D.al k == k) < 693 := by
    rw [Array.length_toList, ea_size h hE] at hl
    exact hl
  have hpos : (ePos E)[x]! = (List.range x).countP fun k => k != 0 && ent D.al k == k := by
    rw [ePos_get hx]
    have := List.get_idxOf (ea_nodup hE) ⟨_, hl⟩
    simp only [List.get_eq_getElem, hrx] at this
    exact this
  rw [hpos]
  generalize hr' : (List.range x).countP (fun k => k != 0 && ent D.al k == k) = r at hl' hcnt
  have hpd : fld(D.pd, Nat.mul (nat_lit 10) ((List.range x).countP fun y => D.eb.testBit y),
      nat_lit 1023) = phiData[r]! := by
    rw [hcnt]
    exact h.pd _ hl'
  have hu := up_get h (pd_lt _ hl')
  have hc := hon hb _ (by rw [hpd, hu])
  have hlt : uPts[phiData[r]!]! < 4096 := by
    rw [← hu]
    exact ent_lt _ _
  obtain ⟨y0, y1, y2⟩ := hy_hypC _ hlt
  rw [y0, y1, y2] at hc
  exact ⟨hl', hc⟩

theorem star_out (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k)
    {x : Nat} (hx : x < 3510) (hb : D.eb.testBit x = false) :
    (ePos E)[x]! = 693 ∧
      D.h0.testBit x = false ∧ D.h1.testBit x = false ∧ D.h2.testBit x = false := by
  obtain ⟨hst, -, hoff⟩ := starK_at h hx
  refine ⟨?_, hoff hb⟩
  rw [ePos_get hx, List.idxOf_eq_length, Array.length_toList, ea_size h hE]
  rw [hE, List.mem_filter]
  rintro ⟨-, hp⟩
  rw [← hst, hb] at hp
  exact Bool.false_ne_true hp

theorem star_gen (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k)
    {B : Bits} {j : Nat}
    (hB : ∀ x < 3510, D.eb.testBit x = true → bitAt B x = hypC j uPts[phiData[(ePos E)[x]!]!]!) :
    starOK E B j = true := by
  unfold starOK
  rw [allIn_iff]
  intro u hu
  obtain ⟨hi, hpu⟩ := phiPos_inv hu
  obtain ⟨hx, hb, hep⟩ := ea_get h hE hi
  rw [beq_iff_eq, hB _ hx hb, hep, hpu]

theorem c_star0 (hO : OrbOK) (h : LHChecks D) :
    starOK (eaPts orbL) (bitsOf (lhData ())[0]!) 0 = true := by
  refine star_gen h (ea_toList hO h) fun x hx hb => ?_
  obtain ⟨-, h0, -, -, e0, -⟩ := star_pt h (ea_toList hO h) hx hb
  rw [B0_at h hx, e0, h0]

theorem c_star1 (hO : OrbOK) (h : LHChecks D) :
    starOK (eaPts orbL) (bitsOf (lhData ())[1]!) 2 = true := by
  refine star_gen h (ea_toList hO h) fun x hx hb => ?_
  obtain ⟨-, -, -, h2, -, e2⟩ := star_pt h (ea_toList hO h) hx hb
  have hb1 : bitAt (bitsOf (lhData ())[1]!) x = (bs D.lb1).testBit x := by
    apply Bool.eq_iff_iff.2
    rw [(B1_bits h).2 x (by omega), testBit_bs]
  rw [hb1, e2, h2]

theorem h1_eq (h : LHChecks D) {E : Array Nat}
    (hE : E.toList = (List.range 3510).filter fun k => k != 0 && ent D.al k == k)
    {x : Nat} (hx : x < 3510) :
    (decide ((ePos E)[x]! < 693) && hypC 1 uPts[phiData[(ePos E)[x]!]!]!) = D.h1.testBit x := by
  rcases Bool.eq_false_or_eq_true (D.eb.testBit x) with hb | hb
  · obtain ⟨hp, -, h1, -⟩ := star_pt h hE hx hb
    rw [h1, decide_eq_true hp, Bool.true_and]
  · obtain ⟨hp, -, h1, -⟩ := star_out h hE hx hb
    simp [hp, h1]

theorem c_fail (hO : OrbOK) (h : LHChecks D) : failOK (tauAll orbL) (ePos (eaPts orbL)) = true := by
  have hf := h.fail
  unfold failK at hf
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, memB_eq, notB_eq, bEq_eq, allN_iff] at hf
  obtain ⟨-, hh1, ht, hal, hall⟩ := hf
  have hT : ∀ k < 3510, ∀ x < 3510, ap (tauAll orbL)[k]! x = ent (D.R k) x :=
    fun k hk x hx => ((tauAll_TR hO h k hk).2 x hx).1
  have h63 := h1_eq h (ea_toList hO h) (x := 63) (by decide)
  rw [hh1, Bool.and_eq_true] at h63
  unfold failOK lhFailT lhFailC
  simp only [Bool.and_eq_true, allIn_iff]
  refine ⟨⟨⟨⟨⟨h63.1, h63.2⟩, ?_⟩, by decide⟩, ?_⟩, fun x hx => ?_⟩
  · rw [hT 63 (by decide) 2751 (by decide), beq_iff_eq]
    exact Nat.eq_of_beq_eq_true ht
  · rw [hT 0 (by decide) 2751 (by decide), row_zero h]
    simpa [beq_dec] using hal
  · have e := hall x hx
    rw [h1_eq h (ea_toList hO h) hx, hT 63 (by decide) x hx, hT 0 (by decide) x hx, row_zero h,
      hT 2751 (by decide) x hx]
    simp only [beq_iff_eq] at e ⊢
    simp only [Bool.beq_eq_decide_eq, beq_dec, bne, Bool.and_assoc] at e ⊢
    exact e

end CFSG.KS.Fi22LH
