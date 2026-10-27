module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

private lemma central_comm {n : G} (hn : n ∈ center G) (g : G) : g * n = n * g :=
  Subgroup.mem_center_iff.mp hn g

private lemma bilin_left (hder : ∀ x y : G, ⁅x, y⁆ ∈ center G) (x y w : G) :
    ⁅x * y, w⁆ = ⁅x, w⁆ * ⁅y, w⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, central_comm (hder y w) x, mul_inv_cancel_right]
  exact central_comm (hder x w) _

private lemma bilin_right (hder : ∀ x y : G, ⁅x, y⁆ ∈ center G) (x y w : G) :
    ⁅x, y * w⁆ = ⁅x, y⁆ * ⁅x, w⁆ := by
  rw [← commutatorElement_inv (y * w) x, bilin_left hder, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact central_comm (hder x y) _

private lemma comm_left_of_mem_center {n : G} (hn : n ∈ center G) (y : G) : ⁅n, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (central_comm hn y).symm

private lemma comm_right_of_mem_center {n : G} (hn : n ∈ center G) (x : G) : ⁅x, n⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (central_comm hn x)

private lemma comm_mul_central (hder : ∀ x y : G, ⁅x, y⁆ ∈ center G) {n n' : G}
    (hn : n ∈ center G) (hn' : n' ∈ center G) (x y : G) : ⁅x * n, y * n'⁆ = ⁅x, y⁆ := by
  rw [bilin_left hder, bilin_right hder, bilin_right hder, comm_right_of_mem_center hn' x,
    comm_left_of_mem_center hn y, comm_left_of_mem_center hn n']
  simp

private theorem comm_values_two [Finite G] (hder : ∀ x y : G, ⁅x, y⁆ ∈ center G)
    (hidx : Nat.card G = 4 * Nat.card (center G)) :
    ∃ c : G, c * c = 1 ∧ ∀ x y : G, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = c := by
  by_cases hab : ∀ x y : G, ⁅x, y⁆ = 1
  · exact ⟨1, one_mul 1, fun x y => Or.inl (hab x y)⟩
  push Not at hab
  obtain ⟨a, b, hc⟩ := hab
  have hQ : Nat.card (G ⧸ center G) = 4 := by
    have h1 := (center G).card_mul_index
    have h2 : (center G).index = Nat.card (G ⧸ center G) := (center G).index_eq_card
    have hpos : 0 < Nat.card (center G) := Nat.card_pos
    rw [h2] at h1
    have h3 : Nat.card (center G) * Nat.card (G ⧸ center G) = Nat.card (center G) * 4 := by
      rw [h1, hidx]; omega
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have hrefute : ∀ u : G, ⁅a, u⁆ = 1 → ((u : G) : G ⧸ center G) ≠ ((b : G) : G ⧸ center G) := by
    intro u hu he
    apply hc
    have hn : u⁻¹ * b ∈ center G := QuotientGroup.eq.mp he
    have hb : b = u * (u⁻¹ * b) := by group
    rw [hb, bilin_right hder, hu, comm_right_of_mem_center hn]
    simp
  have hA1 : ((a : G) : G ⧸ center G) ≠ 1 := fun h =>
    hc (comm_left_of_mem_center (QuotientGroup.eq_one_iff _ |>.mp h) b)
  have hB1 : ((b : G) : G ⧸ center G) ≠ 1 := fun h =>
    hc (comm_right_of_mem_center (QuotientGroup.eq_one_iff _ |>.mp h) a)
  have hAB : ((a : G) : G ⧸ center G) ≠ ((b : G) : G ⧸ center G) :=
    hrefute a (commutatorElement_self a)
  have hAB' : ((a : G) : G ⧸ center G) * ((b : G) : G ⧸ center G) ≠ 1 := by
    intro h
    have h' : ((a⁻¹ : G) : G ⧸ center G) = ((b : G) : G ⧸ center G) := by
      rw [QuotientGroup.mk_inv]
      exact inv_eq_of_mul_eq_one_right h
    exact hrefute a⁻¹ (by simp [commutatorElement_def]) h'
  have F3 : ∀ q : G ⧸ center G, q = 1 ∨ q = ((a : G) : G ⧸ center G) ∨
      q = ((b : G) : G ⧸ center G) ∨
      q = ((a : G) : G ⧸ center G) * ((b : G) : G ⧸ center G) := by
    intro q
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    have hfin : Fintype (G ⧸ center G) := Fintype.ofFinite _
    have hnd : [1, ((a : G) : G ⧸ center G), ((b : G) : G ⧸ center G),
        ((a : G) : G ⧸ center G) * ((b : G) : G ⧸ center G), q].Nodup := by
      simp [List.nodup_cons, hA1, hB1, hAB, Ne.symm hA1, Ne.symm hB1, Ne.symm hAB',
        Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
    have := hnd.length_le_card
    rw [← Nat.card_eq_fintype_card, hQ] at this
    simp at this
  have F3G : ∀ x : G, ∃ n ∈ center G, x = 1 * n ∨ x = a * n ∨ x = b * n ∨ x = (a * b) * n := by
    intro x
    rcases F3 (x : G ⧸ center G) with h | h | h | h
    · exact ⟨x, (QuotientGroup.eq_one_iff _).mp h, Or.inl (by simp)⟩
    · refine ⟨a⁻¹ * x, QuotientGroup.eq.mp h.symm, Or.inr (Or.inl (by group))⟩
    · refine ⟨b⁻¹ * x, QuotientGroup.eq.mp h.symm, Or.inr (Or.inr (Or.inl (by group)))⟩
    · have h' : ((a * b : G) : G ⧸ center G) = (x : G ⧸ center G) := by
        rw [QuotientGroup.mk_mul]; exact h.symm
      refine ⟨(a * b)⁻¹ * x, QuotientGroup.eq.mp h', Or.inr (Or.inr (Or.inr (by group)))⟩
  have hA2 : ((a * a : G) : G ⧸ center G) = 1 := by
    rw [QuotientGroup.mk_mul]
    rcases F3 (((a : G) : G ⧸ center G) * ((a : G) : G ⧸ center G)) with h | h | h | h
    · exact h
    · exact absurd (mul_eq_left.mp h) hA1
    · exact absurd (by rw [QuotientGroup.mk_mul]; exact h) (hrefute (a * a) (by
        rw [bilin_right hder]; simp))
    · exact absurd (mul_left_cancel h) hAB
  have haa : a * a ∈ center G := (QuotientGroup.eq_one_iff _).mp hA2
  have hcc : ⁅a, b⁆ * ⁅a, b⁆ = 1 := by
    rw [← bilin_left hder]
    exact comm_left_of_mem_center haa b
  have hba : ⁅b, a⁆ = ⁅a, b⁆ := by
    rw [← commutatorElement_inv a b]
    exact inv_eq_of_mul_eq_one_right hcc
  refine ⟨⁅a, b⁆, hcc, fun x y => ?_⟩
  obtain ⟨n, hn, hx⟩ := F3G x
  obtain ⟨n', hn', hy⟩ := F3G y
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    rw [comm_mul_central hder hn hn'] <;>
    simp [bilin_left hder, bilin_right hder, hba]

end Abstract

theorem card_derived_le_two {A : Type} [Group A] [Finite A] (W : Subgroup A)
    (hder : ⁅W, W⁆ ≤ W ⊓ centralizer (W : Set A))
    (hidx : Nat.card ↥W = 4 * Nat.card ↥(W ⊓ centralizer (W : Set A))) :
    Nat.card ↥⁅W, W⁆ ≤ 2 := by
  have hder' : ∀ x y : ↥W, ⁅x, y⁆ ∈ center ↥W := by
    intro x y
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : ((⁅x, y⁆ : ↥W) : A) ∈ W ⊓ centralizer (W : Set A) :=
      hder (commutator_mem_commutator x.2 y.2)
    exact Subtype.ext (mem_centralizer_iff.mp h1.2 g g.2)
  have hcard : Nat.card ↥W = 4 * Nat.card ↥(center ↥W) := by
    rw [hidx]
    congr 1
    refine Nat.card_congr
      { toFun := fun w => ⟨⟨(w : A), w.2.1⟩, Subgroup.mem_center_iff.mpr fun g =>
          Subtype.ext (mem_centralizer_iff.mp w.2.2 g g.2)⟩
        invFun := fun w => ⟨(w.1 : A), w.1.2, mem_centralizer_iff.mpr fun h hh =>
          congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨h, hh⟩)⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  obtain ⟨c, hcc, hcv⟩ := comm_values_two hder' hcard
  have hle : ⁅W, W⁆ ≤ zpowers (c : A) := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rcases hcv ⟨x, hx⟩ ⟨y, hy⟩ with h | h
    · have h' : ⁅x, y⁆ = 1 := congrArg Subtype.val h
      rw [h']
      exact one_mem _
    · have h' : ⁅x, y⁆ = (c : A) := congrArg Subtype.val h
      rw [h']
      exact mem_zpowers _
  have hc2 : (c : A) ^ 2 = 1 := by
    have := congrArg Subtype.val hcc
    simpa [sq] using this
  calc Nat.card ↥⁅W, W⁆ ≤ Nat.card ↥(zpowers (c : A)) := Subgroup.card_le_of_le hle
    _ = orderOf (c : A) := Nat.card_zpowers _
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc2)

theorem card_modEq_centralizer {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    {W X : Subgroup A} (hX : IsPGroup p ↥X) (hXW : X ≤ normalizer (W : Set A)) :
    Nat.card ↥W ≡ Nat.card ↥(W ⊓ centralizer (X : Set A)) [MOD p] := by
  have hconj : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun x hx w hw =>
    (mem_normalizer_iff.mp (hXW hx) w).mp hw
  let _ : MulAction ↥X ↥W :=
    { smul := fun x w => ⟨x * w * x⁻¹, hconj x x.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show ((1 : ↥X) : A) * (w : A) * ((1 : ↥X) : A)⁻¹ = w
        simp)
      mul_smul := fun x y w => Subtype.ext (by
        show ((x * y : ↥X) : A) * (w : A) * ((x * y : ↥X) : A)⁻¹ =
          (x : A) * ((y : A) * (w : A) * (y : A)⁻¹) * (x : A)⁻¹
        simp [mul_assoc]) }
  have hmod := hX.card_modEq_card_fixedPoints ↥W
  have hfix : ∀ w : ↥W, w ∈ MulAction.fixedPoints ↥X ↥W ↔ (w : A) ∈ centralizer (X : Set A) := by
    intro w
    rw [MulAction.mem_fixedPoints, mem_centralizer_iff]
    constructor
    · intro h x hx
      have h' : x * (w : A) * x⁻¹ = w := congrArg Subtype.val (h ⟨x, hx⟩)
      calc x * (w : A) = (x * w * x⁻¹) * x := by group
        _ = w * x := by rw [h']
    · intro h x
      refine Subtype.ext ?_
      show (x : A) * (w : A) * (x : A)⁻¹ = w
      have h' : (x : A) * (w : A) = (w : A) * x := h x x.2
      calc (x : A) * (w : A) * (x : A)⁻¹ = (w * x) * (x : A)⁻¹ := by rw [h']
        _ = w := by group
  have e : Nat.card (MulAction.fixedPoints ↥X ↥W) =
      Nat.card ↥(W ⊓ centralizer (X : Set A)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : A), w.1.2, (hfix w.1).1 w.2⟩
        invFun := fun w => ⟨⟨(w : A), w.2.1⟩, (hfix ⟨(w : A), w.2.1⟩).2 w.2.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  rw [e] at hmod
  exact hmod

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
