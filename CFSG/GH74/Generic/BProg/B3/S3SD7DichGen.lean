module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import CFSG.Foundations.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.Generic.BProg.B3.S3SD7DichGen

open Equiv Equiv.Perm Subgroup CFSG

abbrev Quad := Fin 7 × Fin 7 × Fin 7 × Fin 7

@[expose] def qp (q : Quad) : Perm (Fin 7) := swap q.1 q.2.1 * swap q.2.2.1 q.2.2.2

@[expose] def pairs : List (Fin 7 × Fin 7) :=
  (List.finRange 7).flatMap fun a =>
    (List.finRange 7).filterMap fun b => if a < b then some (a, b) else none

@[expose] def S0q : List Quad :=
  (pairs.flatMap fun p => (List.finRange 7).flatMap fun c =>
      if p.2 < c then [(p.1, p.2, p.1, c), (p.1, c, p.1, p.2)] else []) ++
  (pairs.flatMap fun p => pairs.filterMap fun q =>
      if p.1 < q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 then some (p.1, p.2, q.1, q.2) else none)

theorem S0q_ne : ∀ q ∈ S0q, q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 := by decide +kernel

theorem qp_mem_alt {q : Quad} (hq : q ∈ S0q) : qp q ∈ alternatingGroup (Fin 7) := by
  obtain ⟨h1, h2⟩ := S0q_ne q hq
  rw [mem_alternatingGroup]
  simp [qp, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]

@[expose] def is3 (q : Quad) : Bool :=
  q.1 == q.2.2.1 && q.1 != q.2.1 && q.1 != q.2.2.2 && q.2.1 != q.2.2.2

theorem qp_isThreeCycle {q : Quad} (h : is3 q = true) : (qp q).IsThreeCycle := by
  unfold is3 at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨e, h1⟩, h2⟩, h3⟩ := h
  unfold qp
  rw [← e]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same h1 h2 h3

@[expose] def img (σ : Perm (Fin 7)) (m : ℕ) : ℕ :=
  (List.finRange 7).foldl (fun acc i => if m.testBit i.val then acc ||| 2 ^ (σ i).val else acc) 0

theorem img_sound (σ : Perm (Fin 7)) (m : ℕ) (j : Fin 7) (h : (img σ m).testBit j.val = true) :
    ∃ i : Fin 7, m.testBit i.val = true ∧ σ i = j := by
  have key : ∀ (l : List (Fin 7)) (acc : ℕ),
      (l.foldl (fun acc i => if m.testBit i.val then acc ||| 2 ^ (σ i).val else acc) acc).testBit
        j.val = true →
      acc.testBit j.val = true ∨ ∃ i ∈ l, m.testBit i.val = true ∧ σ i = j := by
    intro l
    induction l with
    | nil => intro acc h; exact Or.inl h
    | cons i l ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with h1 | ⟨i', hi', h2⟩
      · by_cases hm : m.testBit i.val = true
        · simp only [hm, ↓reduceIte, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
            decide_eq_true_eq] at h1
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr ⟨i, by simp, hm, by first | exact h1 | exact Fin.ext h1⟩
        · simp only [hm] at h1
          exact Or.inl h1
      · exact Or.inr ⟨i', List.mem_cons_of_mem _ hi', h2⟩
  rcases key (List.finRange 7) 0 h with h1 | ⟨i, -, h2⟩
  · simp at h1
  · exact ⟨i, h2⟩

@[expose] def stepM (L : List Quad) (m : ℕ) : ℕ := L.foldl (fun acc q => acc ||| img (qp q) m) m

theorem stepM_sound (L : List Quad) (m : ℕ) (j : Fin 7) (h : (stepM L m).testBit j.val = true) :
    m.testBit j.val = true ∨ ∃ q ∈ L, ∃ i : Fin 7, m.testBit i.val = true ∧ qp q i = j := by
  have key : ∀ (l : List Quad) (acc : ℕ),
      (l.foldl (fun acc q => acc ||| img (qp q) m) acc).testBit j.val = true →
      acc.testBit j.val = true ∨ ∃ q ∈ l, ∃ i : Fin 7, m.testBit i.val = true ∧ qp q i = j := by
    intro l
    induction l with
    | nil => intro acc h; exact Or.inl h
    | cons q l ih =>
      intro acc h
      simp only [List.foldl_cons] at h
      rcases ih _ h with h1 | ⟨q', hq', h2⟩
      · rw [Nat.testBit_or, Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · obtain ⟨i, hi, hqi⟩ := img_sound _ _ _ h1
          exact Or.inr ⟨q, by simp, i, hi, hqi⟩
      · exact Or.inr ⟨q', List.mem_cons_of_mem _ hq', h2⟩
  exact key L m h

@[expose] def reachM (L : List Quad) : ℕ → ℕ → ℕ
  | 0, m => m
  | n + 1, m => reachM L n (stepM L m)

theorem reachM_sound {H : Subgroup (Perm (Fin 7))} {L : List Quad} (hL : ∀ q ∈ L, qp q ∈ H) :
    ∀ (n m : ℕ), (∀ j : Fin 7, m.testBit j.val = true → ∃ h ∈ H, h 0 = j) →
      ∀ j : Fin 7, (reachM L n m).testBit j.val = true → ∃ h ∈ H, h 0 = j := by
  intro n
  induction n with
  | zero => intro m hm; exact hm
  | succ n ih =>
    intro m hm
    apply ih
    intro j hj
    rcases stepM_sound L m j hj with h1 | ⟨q, hq, i, h1, h2⟩
    · exact hm j h1
    · obtain ⟨h, hH, h0⟩ := hm i h1
      exact ⟨qp q * h, mul_mem (hL q hq) hH, by simp [h0, h2]⟩

@[expose] def genOKb (L : List Quad) : Bool := L.any is3 && reachM L 6 1 == 127

theorem alt_le_of_genOKb {H : Subgroup (Perm (Fin 7))} {L : List Quad} (hL : ∀ q ∈ L, qp q ∈ H)
    (h : genOKb L = true) : alternatingGroup (Fin 7) ≤ H := by
  unfold genOKb at h
  rw [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨⟨q3, hq3, h3⟩, hr⟩ := h
  have hreach : ∀ j : Fin 7, ∃ h ∈ H, h 0 = j := by
    intro j
    refine reachM_sound hL 6 1 ?_ j ?_
    · intro j hj
      have h0 : j = 0 := Fin.ext (Nat.testBit_one_eq_true_iff_self_eq_zero.1 hj)
      subst h0
      exact ⟨1, one_mem H, rfl⟩
    · rw [hr]
      revert j
      decide
  have htrans : MulAction.IsPretransitive H (Fin 7) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨a, ha, hax⟩ := hreach x
    obtain ⟨b, hb, hby⟩ := hreach y
    refine ⟨⟨b * a⁻¹, mul_mem hb (inv_mem ha)⟩, ?_⟩
    show (b * a⁻¹) x = y
    rw [← hax]
    simpa using hby
  have hprim : MulAction.IsPreprimitive H (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; decide)
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim
    (qp_isThreeCycle h3) (hL q3 hq3)

theorem elemAb_top {K : Type*} [Group K] [hK : IsElementaryAbelian 2 K] :
    IsElementaryAbelian 2 ↥(⊤ : Subgroup K) := by
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply Subtype.ext
    exact (hK.toIsMulCommutative.is_comm).comm (a : K) b
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
    apply Subtype.ext
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (IsElementaryAbelian.exponent_dvd_p 2 K) (a : K)
    simpa using this

theorem elemAb_of_le {G : Type*} [Group G] {E F : Subgroup G}
    [hE : IsElementaryAbelian 2 ↥E] (h : F ≤ E) : IsElementaryAbelian 2 ↥F :=
  CFSG.IsElementaryAbelian.of_le inferInstance h

theorem card_eq_two_pow_pRank {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    [hE : IsElementaryAbelian 2 ↥E] : Nat.card ↥E = 2 ^ pRank 2 ↥E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := ↥E)).1 (IsElementaryAbelian.isPGroup 2 ↥E)
  have hub : ∀ r ∈ {r : ℕ | ∃ A : Subgroup ↥E, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r},
      r ≤ n := by
    rintro r ⟨A, -, hA⟩
    have := Subgroup.card_subgroup_dvd_card A
    rw [hA, hn] at this
    exact (Nat.pow_dvd_pow_iff_le_right Nat.one_lt_two).1 this
  have hmem : n ∈ {r : ℕ | ∃ A : Subgroup ↥E, IsElementaryAbelian 2 ↥A ∧ Nat.card ↥A = 2 ^ r} :=
    ⟨⊤, elemAb_top, by rw [Subgroup.card_top, hn]⟩
  have : pRank 2 ↥E = n := by
    unfold pRank
    exact le_antisymm (csSup_le ⟨n, hmem⟩ hub) (le_csSup ⟨n, hub⟩ hmem)
  rw [this, hn]

theorem pRank_eq_of_card {G : Type*} [Group G] [Finite G] {E : Subgroup G}
    [IsElementaryAbelian 2 ↥E] {s : ℕ} (h : Nat.card ↥E = 2 ^ s) : pRank 2 ↥E = s := by
  have h2 := card_eq_two_pow_pRank (E := E)
  rw [h] at h2
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

theorem sq_mul_of_comm {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : x * y * (x * y) = 1 := by
  have h2 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
  rw [← mul_assoc, h2, hy]

@[expose] def V4 {G : Type*} [Group G] (x y : G) (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : Subgroup G where
  carrier := {z | z = 1 ∨ z = x ∨ z = y ∨ z = x * y}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h1 : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
    have h2 : x * y * x = y := by rw [hxy, mul_assoc, hx, mul_one]
    have h3 : y * (x * y) = x := by rw [← mul_assoc, ← hxy, mul_assoc, hy, mul_one]
    have h4 : x * y * y = x := by rw [mul_assoc, hy, mul_one]
    have h5 : x * y * (x * y) = 1 := sq_mul_of_comm hx hy hxy
    have h6 : y * x = x * y := hxy.symm
    rintro a b (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
      simp [h1, h2, h3, h4, h5, h6, hx, hy]
  inv_mem' := by
    have h5 : x * y * (x * y) = 1 := sq_mul_of_comm hx hy hxy
    rintro a (rfl | rfl | rfl | rfl)
    · simp
    · simp [inv_eq_of_mul_eq_one_right hx]
    · simp [inv_eq_of_mul_eq_one_right hy]
    · simp [inv_eq_of_mul_eq_one_right h5]

section V4

variable {G : Type*} [Group G] {x y : G} {hx : x * x = 1} {hy : y * y = 1} {hxy : x * y = y * x}

theorem mem_V4 {z : G} : z ∈ V4 x y hx hy hxy ↔ z = 1 ∨ z = x ∨ z = y ∨ z = x * y := Iff.rfl

theorem V4_le {E : Subgroup G} (hx' : x ∈ E) (hy' : y ∈ E) : V4 x y hx hy hxy ≤ E := by
  intro z hz
  rcases hz with rfl | rfl | rfl | rfl
  exacts [one_mem E, hx', hy', mul_mem hx' hy']

theorem card_V4 (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(V4 x y hx hy hxy) = 4 := by
  classical
  have e1 : x * y ≠ 1 := fun h =>
    hne ((mul_eq_one_iff_eq_inv.1 h).trans (inv_eq_of_mul_eq_one_right hy))
  have e2 : x * y ≠ x := fun h => hy1 (by simpa using h)
  have e3 : x * y ≠ y := fun h => hx1 (by simpa using h)
  have hF : ({1, x, y, x * y} : Finset G).card = 4 := by
    have n1 : (1 : G) ∉ ({x, y, x * y} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1.symm, hy1.symm, e1.symm⟩
    have n2 : x ∉ ({y, x * y} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hne, e2.symm⟩
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_pair e3.symm]
  have hset : ∀ z : G, z ∈ V4 x y hx hy hxy ↔ z ∈ ({1, x, y, x * y} : Finset G) := by
    intro z; simp [mem_V4]
  rw [← hF, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight hset)

theorem mem_centralizer_V4 {σ : G} (h1 : σ * x = x * σ) (h2 : σ * y = y * σ) :
    σ ∈ Subgroup.centralizer ((V4 x y hx hy hxy : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases hz with rfl | rfl | rfl | rfl
  · simp
  · exact h1.symm
  · exact h2.symm
  · rw [mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]

theorem mem_centralizer_zpowers {σ : G} (h1 : σ * x = x * σ) :
    σ ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ((Commute.zpow_left (show Commute x σ from h1.symm) n)).eq

theorem card_zpowers_of_sq {z : G} (hz : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card ↥(Subgroup.zpowers z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hz) hz1

end V4

end CFSG.GH74.Generic.BProg.B3.S3SD7DichGen
