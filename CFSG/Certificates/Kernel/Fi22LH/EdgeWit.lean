module

public import CFSG.Certificates.Kernel.Fi22LH.Defs
import CFSG.Certificates.Kernel.Fi22LH.Acc
import CFSG.Certificates.Kernel.Fi22LH.Card
import CFSG.Certificates.Kernel.Fi22LH.Maps
import CFSG.Certificates.Kernel.Fi22LH.OrbSets
import CFSG.Certificates.Kernel.Fi22LH.Pop
import CFSG.Certificates.Kernel.Fi22LH.Prim
import CFSG.Certificates.Kernel.Fi22LH.Rows
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KC.Enum CFSG.KS

variable {D : LHData}

private theorem nland_eq (a b : Nat) : Nat.land a b = a &&& b := rfl

private theorem nsub_eq (a b : Nat) : Nat.sub a b = a - b := rfl

private theorem minFold_testBit (Z : Nat → Nat) (q bB : Nat) : ∀ (l : List Nat) (k : Nat),
    (l.foldr (fun j c => strictN (ent q j) fun a => nIf(memB bB a, Nat.land c (Z a), c))
      (2 ^ 3510 - 1)).testBit k = true ↔
      k < 3510 ∧ ∀ j ∈ l, bB.testBit (ent q j) = true → (Z (ent q j)).testBit k = true
  | [], k => by simp [Nat.testBit_two_pow_sub_one]
  | j :: l, k => by
    rw [List.foldr_cons, strictN_eq, nIf_eq, memB_eq]
    by_cases hb : bB.testBit (ent q j) = true
    · rw [if_pos hb, nland_eq, Nat.testBit_and, Bool.and_eq_true, minFold_testBit Z q bB l k]
      constructor
      · rintro ⟨⟨hk, hl⟩, hz⟩
        refine ⟨hk, fun j' hj' hb' => ?_⟩
        rcases List.mem_cons.1 hj' with rfl | hj'
        · exact hz
        · exact hl j' hj' hb'
      · rintro ⟨hk, hl⟩
        exact ⟨⟨hk, fun j' hj' hb' => hl j' (List.mem_cons_of_mem _ hj') hb'⟩,
          hl j List.mem_cons_self hb⟩
    · rw [if_neg hb, minFold_testBit Z q bB l k]
      constructor
      · rintro ⟨hk, hl⟩
        refine ⟨hk, fun j' hj' hb' => ?_⟩
        rcases List.mem_cons.1 hj' with rfl | hj'
        · exact absurd hb' hb
        · exact hl j' hj' hb'
      · rintro ⟨hk, hl⟩
        exact ⟨hk, fun j' hj' hb' => hl j' (List.mem_cons_of_mem _ hj') hb'⟩

private theorem bitsIs_ones : BitsIs (Array.replicate 55 (~~~(0 : UInt64))) fun _ => True := by
  refine ⟨by simp, fun y hy => ?_⟩
  simp only [iff_true]
  rw [bitAt_eq, getElem!_pos _ _ (by simp; omega), Array.getElem_replicate]
  have : (~~~(0 : UInt64)).toNat = 2 ^ 64 - 1 := by decide
  rw [this, Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_true_eq]
  omega

private theorem bitsIs_andFold (I : Bits) (CB : Array Bits) (P : Nat → Nat → Prop) : ∀ n,
    (∀ z < n, BitsIs CB[z]! (P z)) →
    BitsIs (Nat.fold n (fun z _ acc => if bitAt I z then andBits acc CB[z]! else acc)
      (Array.replicate 55 (~~~0))) fun y => ∀ z < n, bitAt I z = true → P z y
  | 0, _ => by
    rw [Nat.fold_zero]
    exact bitsIs_ones.congr fun y _ => by simp
  | n + 1, hCB => by
    rw [Nat.fold_succ]
    have ih := bitsIs_andFold I CB P n fun z hz => hCB z (by omega)
    by_cases hI : bitAt I n = true
    · rw [if_pos hI]
      refine (bitsIs_andBits ih (hCB n (by omega))).congr fun y _ => ?_
      constructor
      · rintro ⟨h1, h2⟩ z hz hIz
        rcases Nat.lt_or_ge z n with hz' | hz'
        · exact h1 z hz' hIz
        · rw [show z = n by omega]
          exact h2
      · intro h
        exact ⟨fun z hz hIz => h z (by omega) hIz, h n (by omega) hI⟩
    · rw [if_neg hI]
      refine ih.congr fun y _ => ?_
      constructor
      · intro h z hz hIz
        rcases Nat.lt_or_ge z n with hz' | hz'
        · exact h z hz' hIz
        · rw [show z = n by omega] at hIz
          exact absurd hIz hI
      · intro h z hz hIz
        exact h z (by omega) hIz

private theorem find?_range_eq {n w : Nat} {p : Nat → Bool} (hw : w < n) (hp : p w = true)
    (hlt : ∀ k < w, p k = false) : (List.range n).find? p = some w := by
  obtain ⟨r, rfl⟩ : ∃ r, n = w + 1 + r := ⟨n - w - 1, by omega⟩
  rw [List.range_add, List.range_succ, List.find?_append, List.find?_append]
  have h1 : (List.range w).find? p = none := List.find?_eq_none.2 fun k hk => by
    rw [hlt k (List.mem_range.1 hk)]
    simp
  rw [h1]
  simp [hp]

theorem ent_inj_of_setSl {Q : Nat → Nat} {al be : Nat}
    (hs : ∀ s < 20, setSl Q al be s = true) {k : Nat} (hk : k < 14080) :
    ∀ i < 351, ∀ j < 351, ent (Q k) i = ent (Q k) j → i = j := by
  classical
  have hpop := sb_pop hs hk
  have hlt : sb (Q k) < 2 ^ 3584 :=
    lt_of_lt_of_le (sb_lt _) (Nat.pow_le_pow_right (by omega) (by omega))
  rw [popK_eq hlt, countP_range] at hpop
  have himg : (Finset.range 351).image (ent (Q k)) =
      (Finset.range 3584).filter fun y => (sb (Q k)).testBit y = true := by
    ext y
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by have := mem_lt hs hk hj; omega, (sb_mem hs hk _).2 ⟨j, hj, rfl⟩⟩
    · rintro ⟨-, hy⟩
      exact (sb_mem hs hk y).1 hy
  have hcard : ((Finset.range 3584).filter fun y => (sb (Q k)).testBit y = true).card = 351 := by
    rw [Finset.card_filter, ← hpop]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases (sb (Q k)).testBit i <;> rfl
  have hc : ((Finset.range 351).image (ent (Q k))).card = (Finset.range 351).card := by
    rw [himg, hcard, Finset.card_range]
  have hinj := Finset.card_image_iff.1 hc
  intro i hi j hj e
  exact hinj (by simpa using hi) (by simpa using hj) e

theorem edgeWit_eq_of_edgeK (hO : OrbOK) (h : LHChecks D) {m m' w : Nat} (hm : m < 14080)
    (hm' : m' < 14080)
    (he : edgeK D.R D.Z (D.QA m) (sb (D.QA m)) (sb (D.QA m')) w = true) :
    w < 3510 ∧
      mapsOnto (tauAll orbL)[w]! (bitsOfNat (sb (D.QA m))) (bitsOfNat (sb (D.QA m'))) = true ∧
      edgeWit (tauAll orbL) (commBits (tauAll orbL)) (bitsOfNat (sb (D.QA m)))
        (bitsOfNat (sb (D.QA m'))) = w := by
  classical
  have hs := h.setA
  set q := D.QA m with hq
  set bA := sb q with hbA
  set bB := sb (D.QA m') with hbB
  unfold edgeK at he
  rw [bAnd_eq, Bool.and_eq_true, strictB_eq, allN_iff] at he
  obtain ⟨hmin, himg⟩ := he
  unfold minWitK at hmin
  rw [strictB_eq, foldN_eq] at hmin
  set c := (List.range 351).foldr (fun j c => strictN (ent q j) fun a =>
      nIf(memB bB a, Nat.land c (D.Z a), c))
    (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 3510)) (nat_lit 1)) with hc
  have hc' : c = (List.range 351).foldr (fun j c => strictN (ent q j) fun a =>
      nIf(memB bB a, Nat.land c (D.Z a), c)) (2 ^ 3510 - 1) := by
    rw [hc, nsub_eq, shiftLeft_one]
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, memB_eq, notB_eq, Bool.not_eq_true',
    strictB_eq, Nat.beq_eq] at hmin
  obtain ⟨hw, hcw, hAw, hmin⟩ := hmin
  have hcbit : ∀ k, c.testBit k = true ↔ k < 3510 ∧
      ∀ j < 351, bB.testBit (ent q j) = true → (D.Z (ent q j)).testBit k = true := by
    intro k
    rw [hc', minFold_testBit]
    simp only [List.mem_range]
  have hbelow : ∀ k < w, c.testBit k = true → bA.testBit k = true := by
    intro k hk hck
    set y := Nat.land c (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)) with hy
    have hy1 : y.testBit k = true := by
      rw [hy, nland_eq, Nat.testBit_and, hck, nsub_eq, shiftLeft_one, Nat.testBit_two_pow_sub_one]
      simp [hk]
    have hle : y ≤ Nat.land y bA := by
      have := hmin
      rw [nsub_eq] at this
      omega
    have hge : Nat.land y bA ≤ y := by rw [nland_eq]; exact Nat.and_le_left
    have he : Nat.land y bA = y := le_antisymm hge hle
    have := congrArg (fun t => t.testBit k) he
    simp only [nland_eq, Nat.testBit_and, hy1, Bool.true_and] at this
    exact this
  have hA := bitsIs_bitsOfNat bA
  have hB := bitsIs_bitsOfNat bB
  have hT := tauAll_TR hO h
  have hCB : ∀ z < 3510, BitsIs (commBits (tauAll orbL))[z]! fun y => (D.Z z).testBit y = true :=
    fun z hz => by
      rw [commBits_eq hO h, getElem!_pos _ z (by rw [Array.size_ofFn]; exact hz),
        Array.getElem_ofFn]
      exact bitsIs_bitsOfNat _
  have hI := bitsIs_andBits hA hB
  have hC0 := bitsIs_andFold (andBits (bitsOfNat bA) (bitsOfNat bB)) (commBits (tauAll orbL))
    (fun z y => (D.Z z).testBit y = true) 3510 hCB
  have hC := bitsIs_diffBits hC0 hA
  have hCmem : ∀ k < 3510, bitAt (diffBits (Nat.fold 3510 (fun z _ acc =>
      if bitAt (andBits (bitsOfNat bA) (bitsOfNat bB)) z then
        andBits acc (commBits (tauAll orbL))[z]! else acc) (Array.replicate 55 (~~~0)))
      (bitsOfNat bA)) k = true ↔ c.testBit k = true ∧ bA.testBit k = false := by
    intro k hk
    rw [hC.2 k (by omega)]
    dsimp only
    rw [hcbit, Bool.not_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hk, fun j hj hbj => h1 (ent q j) (mem_lt hs hm hj) ?_⟩, h2⟩
      rw [hI.2 _ (Nat.lt_of_lt_of_le (mem_lt hs hm hj) (by decide))]
      exact ⟨(sb_mem hs hm _).2 ⟨j, hj, rfl⟩, hbj⟩
    · rintro ⟨⟨-, h1⟩, h2⟩
      refine ⟨fun z hz hIz => ?_, h2⟩
      rw [hI.2 z (by omega)] at hIz
      obtain ⟨hzA, hzB⟩ := hIz
      obtain ⟨j, hj, rfl⟩ := (sb_mem hs hm z).1 hzA
      exact h1 j hj hzB
  have hf : ∀ x < 3510, ∀ y < 3510, ent (D.R w) x = ent (D.R w) y → x = y :=
    fun x hx y hy e => row_inj hO h hw hx hy e
  have hentA := ent_inj_of_setSl hs hm
  have hiff : ∀ x < 3510, bB.testBit (ent (D.R w) x) = true ↔ bA.testBit x = true := by
    intro x hx
    have key := img_eq_of_sub (g := fun j => ent (D.R w) (ent q j)) (e := ent (D.QA m'))
      (fun i hi j hj e => hentA i hi j hj (hf _ (mem_lt hs hm hi) _ (mem_lt hs hm hj) e))
      (fun j hj => by
        have := himg j hj
        rw [memB_eq] at this
        exact (sb_mem hs hm' _).1 this)
      (ent (D.R w) x)
    rw [sb_mem hs hm', key, sb_mem hs hm]
    constructor
    · rintro ⟨j, hj, e⟩
      exact ⟨j, hj, hf _ (mem_lt hs hm hj) _ hx e⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
  have hmaps : mapsOnto (tauAll orbL)[w]! (bitsOfNat bA) (bitsOfNat bB) = true := by
    refine mapsOnto_of hA hB (fun x hx => ?_) fun x hx => ?_
    · rw [((hT w hw).2 x hx).1]
      exact row_lt hO h hw hx
    · rw [((hT w hw).2 x hx).1]
      exact hiff x hx
  refine ⟨hw, hmaps, ?_⟩
  unfold edgeWit
  dsimp only
  rw [find?_range_eq (w := w) (by omega) ?_ ?_]
  · rfl
  · rw [Bool.and_eq_true]
    exact ⟨(hCmem w hw).2 ⟨hcw, hAw⟩, hmaps⟩
  · intro k hk
    rw [Bool.and_eq_false_iff]
    left
    rw [Bool.eq_false_iff]
    intro e
    obtain ⟨hck, hAk⟩ := (hCmem k (by omega)).1 e
    rw [hbelow k hk hck] at hAk
    exact absurd hAk (by decide)

end CFSG.KS.Fi22LH
