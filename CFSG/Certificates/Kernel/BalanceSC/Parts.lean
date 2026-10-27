module

public import Certificates.Data.Kernel.BalanceSC
public import CFSG.Certificates.Kernel.BalanceSC.Orbits
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.BalanceSC

open Equiv Equiv.Perm Finset

@[expose] def nmask (s : Finset ℕ) : ℕ := ∑ i ∈ s, 2 ^ i

theorem testBit_nmask (s : Finset ℕ) (i : ℕ) : (nmask s).testBit i = decide (i ∈ s) := by
  induction s using Finset.induction_on_max generalizing i with
  | empty => simp [nmask]
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hlt : nmask s < 2 ^ a := Nat.lt_pow_two_of_testBit _ fun j hj => by
      rw [ih]
      simp only [decide_eq_false_iff_not]
      exact fun h => absurd (ha j h) (by omega)
    have : nmask (insert a s) = 2 ^ a * 1 + nmask s := by simp [nmask, sum_insert has]
    rw [this, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, mul_one, Nat.testBit_two_pow, ih]
    by_cases h : i = a
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem nmask_injective : Function.Injective nmask := by
  intro s t h
  ext i
  have := testBit_nmask s i
  rw [h, testBit_nmask] at this
  simpa using this.symm

variable {n : ℕ}

@[expose] def fmask (s : Finset (Fin n)) : ℕ := nmask (s.map Fin.valEmbedding)

theorem testBit_fmask (s : Finset (Fin n)) (i : ℕ) :
    (fmask s).testBit i = true ↔ ∃ x ∈ s, (x : ℕ) = i := by
  simp [fmask, testBit_nmask]

theorem fmask_injective : Function.Injective (fmask (n := n)) :=
  fun _ _ h => map_injective _ (nmask_injective h)

theorem fmask_lt (s : Finset (Fin n)) : fmask s < 2 ^ n :=
  Nat.lt_pow_two_of_testBit _ fun j hj => by
    rw [Bool.eq_false_iff, ne_eq, testBit_fmask]
    rintro ⟨x, -, rfl⟩
    exact absurd x.2 (by omega)

theorem bitCount_fmask (s : Finset (Fin n)) : bitCount n (fmask s) = s.card := by
  unfold bitCount
  have hnd : ((List.range n).filter fun i => (fmask s).testBit i).Nodup :=
    (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd, ← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, testBit_fmask, mem_map,
    Fin.valEmbedding_apply]
  constructor
  · exact fun h => h.2
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, x, hx, rfl⟩

theorem land_fmask_of_disjoint {s t : Finset (Fin n)} (h : Disjoint s t) :
    Nat.land (fmask s) (fmask t) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((fmask s) &&& (fmask t)).testBit i = Nat.testBit 0 i
  rw [Nat.testBit_and, Nat.zero_testBit, Bool.and_eq_false_iff]
  by_contra hc
  simp only [not_or, Bool.not_eq_false, testBit_fmask] at hc
  obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := hc
  rw [Fin.val_inj] at hxy
  subst hxy
  exact disjoint_left.1 h hx hy

theorem mem_rMasks {r m : ℕ} : m ∈ rMasks n r ↔ m < 2 ^ n ∧ bitCount n m = r := by
  simp [rMasks]

theorem land_lor_eq_zero {x y z : ℕ} (h1 : Nat.land x y = 0) (h2 : Nat.land x z = 0) :
    Nat.land x (Nat.lor y z) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 := congrArg (fun t => Nat.testBit t i) h1
  have e2 := congrArg (fun t => Nat.testBit t i) h2
  change (x &&& y).testBit i = Nat.testBit 0 i at e1
  change (x &&& z).testBit i = Nat.testBit 0 i at e2
  change (x &&& (y ||| z)).testBit i = Nat.testBit 0 i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at e1 e2 ⊢
  cases hx : x.testBit i <;> simp_all

theorem mem_chains {S L : List ℕ} (h : L.Sublist S) (hP : L.Pairwise (fun a b => Nat.land a b = 0))
    {acc : ℕ} (hacc : ∀ m ∈ L, Nat.land m acc = 0) : L ∈ chains S L.length acc := by
  induction h generalizing acc with
  | slnil => simp [chains]
  | @cons L S a h ih =>
    cases L with
    | nil => simp [chains]
    | cons b L =>
      rw [List.length_cons, chains]
      exact List.mem_append_right _ (ih hP hacc)
  | @cons_cons L S a h ih =>
    rw [List.pairwise_cons] at hP
    rw [List.length_cons, chains, if_pos (by simpa using hacc a List.mem_cons_self)]
    refine List.mem_append_left _ (List.mem_map.2 ⟨L, ih hP.2 fun m hm => ?_, rfl⟩)
    refine land_lor_eq_zero (hacc m (List.mem_cons_of_mem _ hm)) ?_
    have h1 : a &&& m = 0 := hP.1 m hm
    change m &&& a = 0
    rw [Nat.land_comm]
    exact h1

theorem sublist_of_pairwise_lt : ∀ {L S : List ℕ}, L.Pairwise (· < ·) → S.Pairwise (· < ·) →
    (∀ x ∈ L, x ∈ S) → L.Sublist S
  | [], S, _, _, _ => List.nil_sublist S
  | x :: _, [], _, _, h => absurd (h x List.mem_cons_self) (by simp)
  | x :: L, s :: S, hL, hS, h => by
    rw [List.pairwise_cons] at hS
    have hL' := List.pairwise_cons.1 hL
    by_cases hxs : x = s
    · subst hxs
      refine List.Sublist.cons₂ x (sublist_of_pairwise_lt hL'.2 hS.2 fun y hy => ?_)
      rcases List.mem_cons.1 (h y (List.mem_cons_of_mem _ hy)) with h' | h'
      · exact absurd h' (ne_of_gt (hL'.1 y hy))
      · exact h'
    · have hx' : x ∈ S := by
        rcases List.mem_cons.1 (h x List.mem_cons_self) with h' | h'
        · exact absurd h' hxs
        · exact h'
      have hsx : ∀ y ∈ x :: L, s < y := by
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hS.1 _ hx'
        · exact (hS.1 x hx').trans (hL'.1 y hy)
      refine List.Sublist.cons s (sublist_of_pairwise_lt hL hS.2 fun y hy => ?_)
      rcases List.mem_cons.1 (h y hy) with h' | h'
      · exact absurd h' (ne_of_gt (hsx y hy))
      · exact h'

theorem disjoint_blk {e : Perm (Fin n)} {x y : Fin n} (h : blk e x ≠ blk e y) :
    Disjoint (blk e x) (blk e y) := by
  rw [disjoint_left]
  intro z hx hy
  exact h ((blk_eq_of_sameCycle (mem_blk.1 hx)).trans (blk_eq_of_sameCycle (mem_blk.1 hy)).symm)

@[expose] noncomputable def sortMasks (e : Perm (Fin n)) : List ℕ :=
  ((cycParts e).image fmask).sort (· ≤ ·)

theorem mem_sortMasks {e : Perm (Fin n)} {m : ℕ} :
    m ∈ sortMasks e ↔ ∃ B ∈ cycParts e, fmask B = m := by
  simp [sortMasks]

theorem length_sortMasks (e : Perm (Fin n)) : (sortMasks e).length = (cycParts e).card := by
  rw [sortMasks, length_sort, card_image_of_injective _ fmask_injective]

theorem pairwise_sortMasks (e : Perm (Fin n)) :
    (sortMasks e).Pairwise (fun a b => a < b ∧ Nat.land a b = 0) := by
  have hp := (pairwise_sort ((cycParts e).image fmask) (· ≤ ·)).and
    (sort_nodup ((cycParts e).image fmask) (· ≤ ·))
  refine hp.imp_of_mem fun {a b} ha hb hab => ⟨lt_of_le_of_ne hab.1 hab.2, ?_⟩
  obtain ⟨B, hB, rfl⟩ := mem_sortMasks.1 ha
  obtain ⟨B', hB', rfl⟩ := mem_sortMasks.1 hb
  obtain ⟨x, -, rfl⟩ := mem_image.1 hB
  obtain ⟨y, -, rfl⟩ := mem_image.1 hB'
  exact land_fmask_of_disjoint (disjoint_blk fun h => hab.2 (by rw [h]))

theorem sortMasks_mem_partsK {e : Perm (Fin n)} {r : ℕ} (hr : r.Prime) (her : e ^ r = 1) :
    sortMasks e ∈ partsK n r (cycParts e).card := by
  rw [partsK, ← length_sortMasks]
  have hP := pairwise_sortMasks e
  refine mem_chains (sublist_of_pairwise_lt (hP.imp And.left)
    ((List.pairwise_lt_range).filter _) fun m hm => ?_) (hP.imp And.right) (by simp)
  obtain ⟨B, hB, rfl⟩ := mem_sortMasks.1 hm
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hB
  exact mem_rMasks.2 ⟨fmask_lt _, by rw [bitCount_fmask, card_blk hr her hx]⟩

end CFSG.KC.BalanceSC
