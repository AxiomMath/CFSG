module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Pack
public import Mathlib.Data.LawfulXor.Basic

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

abbrev Vec12 : Type := Fin 12 → ZMod 2

@[expose] def fixM (M : Mat12) : Set Vec12 := {v | M *ᵥ v = v}

@[expose] def fixV (X : Subgroup GL12) : Set Vec12 := {v | ∀ x ∈ X, (x : Mat12) *ᵥ v = v}

@[expose] def vecBits (f : Vec12) : ℕ :=
  bitsOf 12 fun j => if h : j < 12 then f ⟨j, h⟩ == 1 else false

theorem vecBits_lt (f : Vec12) : vecBits f < 4096 := by
  have h : ∀ j, 12 ≤ j → (vecBits f).testBit j = false := fun j hj => by
    rw [vecBits, testBit_bitsOf]
    simp [show ¬ j < 12 by omega]
  by_contra hc
  have h2 := Nat.testBit_log2 (show vecBits f ≠ 0 by omega)
  have h3 : 12 ≤ Nat.log2 (vecBits f) := by
    rw [Nat.le_log2 (by omega)]
    omega
  rw [h _ h3] at h2
  exact absurd h2 (by decide)

theorem toVec_vecBits (f : Vec12) : toVec 12 (vecBits f) = f := by
  ext j
  rw [toVec, vecBits, testBit_bitsOf]
  simp only [j.isLt, decide_true, Bool.true_and, Fin.eta, dite_true]
  exact bz_beq_one _

theorem vecBits_toVec {v : ℕ} (hv : v < 4096) : vecBits (toVec 12 v) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [vecBits, testBit_bitsOf]
  by_cases hj : j < 12
  · simp only [hj, decide_true, Bool.true_and, dite_true, toVec]
    cases v.testBit j <;> rfl
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

theorem toVec_injOn {v w : ℕ} (hv : v < 4096) (hw : w < 4096) (h : toVec 12 v = toVec 12 w) :
    v = w := by
  rw [← vecBits_toVec hv, ← vecBits_toVec hw, h]

theorem toVec_xor (v w : ℕ) : toVec 12 (v ^^^ w) = toVec 12 v + toVec 12 w := by
  ext j
  simp [toVec, Nat.testBit_xor, bz_xor]

theorem xor_lt {v w m : ℕ} (hv : v < 2 ^ m) (hw : w < 2 ^ m) : v ^^^ w < 2 ^ m :=
  Nat.xor_lt_two_pow hv hw

@[expose] def mulVecK (k v : ℕ) : ℕ := bmulVec 12 12 (rowsOf k) v

theorem toVec_mulVecK (k v : ℕ) : toVec 12 (mulVecK k v) = toMatK k *ᵥ toVec 12 v := by
  rw [mulVecK, toVec_bmulVec, toMat_rowsOf]

theorem bitsOf_lt (n : ℕ) (f : ℕ → Bool) : bitsOf n f < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_bitsOf]
    simp [show ¬ i < n by omega]

theorem mulVecK_lt (k v : ℕ) : mulVecK k v < 4096 := by
  rw [mulVecK, bmulVec]
  exact bitsOf_lt 12 _

theorem mulVecK_xor (k v w : ℕ) : mulVecK k (v ^^^ w) = mulVecK k v ^^^ mulVecK k w := by
  apply toVec_injOn (mulVecK_lt _ _)
    (xor_lt (m := 12) (mulVecK_lt _ _) (mulVecK_lt _ _))
  rw [toVec_mulVecK, toVec_xor, toVec_xor, mulVec_add, toVec_mulVecK, toVec_mulVecK]

theorem mulVecK_zero (k : ℕ) : mulVecK k 0 = 0 := by
  apply toVec_injOn (mulVecK_lt _ _) (by norm_num)
  rw [toVec_mulVecK]
  have h0 : toVec 12 0 = 0 := by ext j; simp [toVec]
  rw [h0, mulVec_zero]

@[expose] def spanF : List ℕ → Finset ℕ
  | [] => {0}
  | w :: ws => spanF ws ∪ (spanF ws).image (· ^^^ w)

theorem lt_of_mem_spanF {m : ℕ} : ∀ {ws : List ℕ}, (∀ w ∈ ws, w < 2 ^ m) →
    ∀ x ∈ spanF ws, x < 2 ^ m
  | [], _, x, hx => by
    rw [spanF, Finset.mem_singleton] at hx
    rw [hx]
    positivity
  | w :: ws, h, x, hx => by
    rw [spanF, Finset.mem_union, Finset.mem_image] at hx
    have ih := lt_of_mem_spanF (ws := ws) fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · exact xor_lt (ih y hy) (h w List.mem_cons_self)

theorem fixed_of_mem_spanF {k : ℕ} : ∀ {ws : List ℕ}, (∀ w ∈ ws, mulVecK k w = w) →
    ∀ x ∈ spanF ws, mulVecK k x = x
  | [], _, x, hx => by
    rw [spanF, Finset.mem_singleton] at hx
    rw [hx, mulVecK_zero]
  | w :: ws, h, x, hx => by
    rw [spanF, Finset.mem_union, Finset.mem_image] at hx
    have ih := fixed_of_mem_spanF (ws := ws) fun w' hw' => h w' (List.mem_cons_of_mem _ hw')
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ih x hx
    · rw [mulVecK_xor, ih y hy, h w List.mem_cons_self]

theorem card_spanF : ∀ {ws : List ℕ}, ws.Pairwise (fun a b => b < 2 ^ Nat.log2 a) →
    (∀ w ∈ ws, w ≠ 0) → (spanF ws).card = 2 ^ ws.length
  | [], _, _ => by simp [spanF]
  | w :: ws, hp, h0 => by
    rw [List.pairwise_cons] at hp
    have ih := card_spanF hp.2 fun w' hw' => h0 w' (List.mem_cons_of_mem _ hw')
    have hw0 : w ≠ 0 := h0 w List.mem_cons_self
    have hlt : ∀ x ∈ spanF ws, x < 2 ^ Nat.log2 w := lt_of_mem_spanF hp.1
    have hbit : ∀ x ∈ spanF ws, x.testBit (Nat.log2 w) = false := fun x hx =>
      Nat.testBit_lt_two_pow (hlt x hx)
    have hdisj : Disjoint (spanF ws) ((spanF ws).image (· ^^^ w)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
      have := hbit _ hx
      rw [Nat.testBit_xor, hbit y hy, Nat.testBit_log2 hw0] at this
      exact absurd this (by decide)
    have hinj : Set.InjOn (· ^^^ w) (spanF ws : Set ℕ) := fun a _ b _ e => by
      simpa using congrArg (· ^^^ w) e
    rw [spanF, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, ih,
      List.length_cons, pow_succ]
    ring

@[expose] def fixLB (k : ℕ) (ws : List ℕ) : Bool :=
  ws.all (fun w => decide (w < 4096) && decide (w ≠ 0) && mulVecK k w == w) &&
    decide (ws.Pairwise fun a b => b < 2 ^ Nat.log2 a)

theorem fixLB_sound {k : ℕ} {ws : List ℕ} (h : fixLB k ws = true) :
    2 ^ ws.length ≤ Nat.card (fixM (toMatK k)) := by
  simp only [fixLB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hall, hp⟩ := h
  have hlt : ∀ x ∈ spanF ws, x < 4096 := fun x hx =>
    lt_of_mem_spanF (m := 12) (fun w hw => (hall w hw).1.1) x hx
  have hfix : ∀ x ∈ spanF ws, mulVecK k x = x :=
    fixed_of_mem_spanF fun w hw => (hall w hw).2
  have hmem : ∀ x : spanF ws, toVec 12 x.1 ∈ fixM (toMatK k) := fun x => by
    show toMatK k *ᵥ toVec 12 x.1 = toVec 12 x.1
    rw [← toVec_mulVecK, hfix x.1 x.2]
  let f : spanF ws → fixM (toMatK k) := fun x => ⟨toVec 12 x.1, hmem x⟩
  have hf : Function.Injective f := fun a b e =>
    Subtype.ext (toVec_injOn (hlt a.1 a.2) (hlt b.1 b.2) (congrArg Subtype.val e))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe,
    card_spanF hp fun w hw => (hall w hw).1.2] at this

theorem fixM_of_rep {k : ℕ} {x : GL12} (h : Rep k x) : fixM (toMatK k) = fixM (x : Mat12) := by
  rw [h]

@[expose] def rrefPiv (rows : List ℕ) : List (ℕ × ℕ) :=
  ((List.range 12).reverse.foldl (fun (acc : List (ℕ × ℕ) × List ℕ) c =>
    match acc.2.find? (fun r => r.testBit c) with
    | none => acc
    | some r =>
      ((acc.1.map fun p => (p.1, if p.2.testBit c then p.2 ^^^ r else p.2)) ++ [(c, r)],
        (acc.2.erase r).map fun x => if x.testBit c then x ^^^ r else x)) ([], rows)).1

@[expose] def echIns (piv : List ℕ) (v : ℕ) : List ℕ :=
  let r := piv.foldl (fun acc p => if acc.testBit (Nat.log2 p) then acc ^^^ p else acc) v
  if r = 0 then piv else
    (piv.filter fun p => Nat.log2 r < Nat.log2 p) ++
      r :: piv.filter fun p => Nat.log2 p < Nat.log2 r

@[expose] def kerBasis (k : ℕ) : List ℕ :=
  let rows := (List.range 12).map fun i => ((k >>> (12 * i)) % 4096) ^^^ 2 ^ i
  let piv := rrefPiv rows
  let free := (List.range 12).filter fun f => !(piv.any fun p => p.1 == f)
  let vs := free.map fun f =>
    piv.foldl (fun acc p => if p.2.testBit f then acc ||| 2 ^ p.1 else acc) (2 ^ f)
  vs.foldl echIns []

end CFSG.EvenSmallLie.OmegaEight.Stage2
