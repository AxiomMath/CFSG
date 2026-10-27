module

public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.ClassicalInvolution.Basic

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]

theorem IsClassicalMember.ne_one {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) :
    z ≠ 1 := by
  intro hz
  have h2 := h.orderOf_eq_two
  rw [hz, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem IsClassicalMember.not_le_center {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) :
    ¬ L ≤ Subgroup.center Y := by
  intro hle
  have hcomm : ∀ a b : L, a * b = b * a := fun a b =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hle a.2) b.1).symm
  have hperf : commutator L = ⊤ := h.perfect.commutator_eq_top
  have hz : (⟨z, h.mem⟩ : L) ∈ commutator L := by rw [hperf]; exact Subgroup.mem_top _
  have hbot : commutator L ≤ ⊥ := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a b
  have := Subgroup.mem_bot.mp (hbot hz)
  exact h.ne_one (congrArg Subtype.val this)

theorem IsClassicalMember.conj {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) (g : Y) :
    IsClassicalMember p f (conjSub g L) (g * z * g⁻¹) where
  orderOf_eq_two := by rw [orderOf_conj_eq]; exact h.orderOf_eq_two
  mem := conj_mem_conjSub h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map (MulAut.conj g).toMonoidHom
  subnormal := isSubnormal_map_conj_centralizer h.subnormal g
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : L ≃* conjSub g L := L.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    have hO : (classicalInvolutionOddCore L).map e.toMonoidHom =
        classicalInvolutionOddCore (conjSub g L) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

theorem IsClassicalMember.card_ge [Finite Y] {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) : Nat.card SL(2, GaloisField p f) ≤ Nat.card L := by
  obtain ⟨e⟩ := h.nonempty_equiv
  rw [← Nat.card_congr e.toEquiv]
  exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem card_lt_of_ne_top {G : Type*} [Group G] [Finite G] {H : Subgroup G} (h : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hmul := Subgroup.card_mul_index H
  have hidx : H.index ≠ 1 := fun h1 => h (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ H.index := by omega
  nlinarith

end CFSG.ClassicalInvolution.Generic
