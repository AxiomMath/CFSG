module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Q3.Q3B1

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T.MFS

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

section General

variable {Y : Type} [Group Y]

structure Setting (z : Y) (L T : Subgroup Y) : Prop where
  oddCore : classicalInvolutionOddCore Y = ⊥
  member : IsClassicalMember3 L z
  comp : IsComponentOf T ⊤
  sup : T ⊔ L = ⊤
  gen : Subgroup.normalClosure (L : Set Y) = ⊤
  conn : NonCommConnected (Q3B.conjClass L)
  normal : T.Normal
  cent : Subgroup.centralizer (T : Set Y) = ⊥

@[expose] noncomputable def memberIndex (L T : Subgroup Y) : ℕ :=
  (T.subgroupOf L ⊔ classicalInvolutionOddCore L).index

theorem isPGroup_two_le_of_odd_index {T : Subgroup Y} [T.Normal] (hT : Odd T.index)
    {P : Subgroup Y} (hP : IsPGroup 2 P) : P ≤ T := by
  intro g hg
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have hk' : g ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf (QuotientGroup.mk g : Y ⧸ T) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hk']
    rfl
  have h2 : orderOf (QuotientGroup.mk g : Y ⧸ T) ∣ T.index := by
    have := orderOf_dvd_natCard (QuotientGroup.mk g : Y ⧸ T)
    simpa [Subgroup.index] using this
  have hcop : Nat.Coprime (2 ^ k) T.index :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hT)
  have h3 : orderOf (QuotientGroup.mk g : Y ⧸ T) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have := orderOf_eq_one_iff.mp h3
  exact (QuotientGroup.eq_one_iff g).mp this

variable [Finite Y]

theorem commutator_zpowers_le_of_isSubnormal {p : ℕ} (hp : p.Prime) {K C U : Subgroup Y}
    {σ : Y} (hK : IsSubnormal K C) (hσK : σ ∈ K) (hσp : IsPGroup p (Subgroup.zpowers σ))
    (hUC : U ≤ C) (hUσ : Subgroup.zpowers σ ≤ Subgroup.normalizer (U : Set Y))
    (hcop : ¬ p ∣ Nat.card U) : ⁅U, Subgroup.zpowers σ⁆ ≤ K := by
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent p hp
    (Subgroup.zpowers σ) U hσp hcop hUσ
  induction hK with
  | refl H =>
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hbH : b ∈ H := (Subgroup.zpowers_le.mpr hσK) hb
    have haH : a ∈ H := hUC ha
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem haH hbH) (H.inv_mem haH)) (H.inv_mem hbH)
  | @step J M H hJM hJn hMH ih =>
    have hσM : σ ∈ M := hJM hσK
    have h1 : ⁅U, Subgroup.zpowers σ⁆ ≤ M := ih hσM hUC
    have hA : ⁅⁅U, Subgroup.zpowers σ⁆, Subgroup.zpowers σ⁆ ≤ J := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have haM : a ∈ M := h1 ha
      have hxJ : x ∈ J := (Subgroup.zpowers_le.mpr hσK) hx
      have hconj : a * x * a⁻¹ ∈ J := (Subgroup.normal_subgroupOf_iff hJM).mp hJn x a hxJ haM
      rw [commutatorElement_def]
      have := J.mul_mem hconj (J.inv_mem hxJ)
      simpa [mul_assoc] using this
    rwa [hidem] at hA

end General


section Index

variable {Y : Type} [Group Y] [Finite Y] {L T : Subgroup Y}

omit [Finite Y] in
theorem index_eq_index_subgroupOf [T.Normal] (hT : T ⊔ L = ⊤) :
    T.index = (T.subgroupOf L).index := by
  have h1 := Subgroup.relIndex_sup_left (K := T) (H := L)
  rw [hT, Subgroup.relIndex_top_right] at h1
  exact h1

theorem odd_relIndex_sup_oddCore [T.Normal] :
    Odd ((T.subgroupOf L).relIndex (T.subgroupOf L ⊔ classicalInvolutionOddCore L)) := by
  have hM : (T.subgroupOf L).Normal := inferInstance
  have h1 : (T.subgroupOf L).relIndex (classicalInvolutionOddCore L ⊔ T.subgroupOf L) =
      (T.subgroupOf L).relIndex (classicalInvolutionOddCore L) :=
    Subgroup.relIndex_sup_right (classicalInvolutionOddCore L) (T.subgroupOf L)
  rw [sup_comm] at h1
  rw [h1]
  have hdvd : (T.subgroupOf L).relIndex (classicalInvolutionOddCore L) ∣
      Nat.card (classicalInvolutionOddCore L) := Subgroup.index_dvd_card _
  exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card L) hdvd

omit [Finite Y] in
theorem index_eq_mul_memberIndex [T.Normal] (hT : T ⊔ L = ⊤) :
    T.index = (T.subgroupOf L).relIndex (T.subgroupOf L ⊔ classicalInvolutionOddCore L) *
      memberIndex L T := by
  rw [index_eq_index_subgroupOf hT]
  exact (Subgroup.relIndex_mul_index (le_sup_left)).symm

theorem odd_index_of_memberIndex_eq_three [T.Normal] (hT : T ⊔ L = ⊤) (h3 : memberIndex L T = 3) :
    Odd T.index ∧ 3 ∣ T.index := by
  have h := index_eq_mul_memberIndex hT
  rw [h3] at h
  refine ⟨?_, ⟨_, by rw [h, mul_comm]⟩⟩
  rw [h]
  exact Odd.mul odd_relIndex_sup_oddCore (by decide)

end Index

end CFSG.ClassicalInvolution.Q3.Q3T.MFS
