module

public import CFSG.ClassicalInvolution.Generic.Induction
import CFSG.ClassicalInvolution.Basic
import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ClassicalInvolution.Upgrade

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.Semidihedral
open scoped MatrixGroups

theorem le_card_sl2_galoisField {p f : ℕ} [Fact p.Prime] (hq : 5 ≤ p ^ f) :
    120 ≤ Nat.card SL(2, GaloisField p f) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField p f),
    GaloisField.card p f hf]
  set N := p ^ f with hN
  have h : 24 ≤ N ^ 2 - 1 := by
    have : 25 ≤ N ^ 2 := by nlinarith
    omega
  calc 120 = 5 * 24 := by norm_num
    _ ≤ N * (N ^ 2 - 1) := Nat.mul_le_mul hq h

theorem card_centralizer_ge_of_isClassicalMember {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} {z : Y} (h : IsClassicalMember p f L z) (hq : 5 ≤ p ^ f) :
    120 ≤ Nat.card (Subgroup.centralizer ({z} : Set Y)) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have h1 : Nat.card SL(2, GaloisField p f) ≤ Nat.card L := by
    rw [← Nat.card_congr e.toEquiv]
    exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  have h2 : Nat.card L ≤ Nat.card (Subgroup.centralizer ({z} : Set Y)) :=
    Subgroup.card_le_of_le (isSubnormal_le h.subnormal)
  exact (le_card_sl2_galoisField hq).trans (h1.trans h2)

theorem not_isClassicalMember_of_isSporadic_m11 {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]
    [Finite G] (hG : CFSG.Blueprint.NativeSporadic.IsSporadic G .M11) (hq : 5 ≤ p ^ f)
    {K : Subgroup G} {z : G} (h : IsClassicalMember p f K z) : False := by
  obtain ⟨e⟩ := hG
  have hz : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact h.orderOf_eq_two
  obtain ⟨hc, hN⟩ := ProperSubgroupRegularity.m11_involution_centralizer_card_and_odd_core
    (e z) hz
  obtain ⟨hc', -⟩ := ProperSubgroupRegularity.centralizer_card_and_core_of_equiv e z hc hN
  have := card_centralizer_ge_of_isClassicalMember h hq
  have h48 : Nat.card (Subgroup.centralizer ({z} : Set G)) = 48 := hc'
  omega

end CFSG.ClassicalInvolution.Upgrade
