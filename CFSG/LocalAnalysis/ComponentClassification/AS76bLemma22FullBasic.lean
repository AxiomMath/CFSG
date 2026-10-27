module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22Full

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22
open scoped commutatorElement

section OddIndex

variable {G : Type*} [Group G]

theorem mem_of_pow_eq_one_of_odd_relIndex {N Y : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ normalizer (N : Set G)) (hodd : Odd (N.relIndex Y)) {x : G} (hxY : x ∈ Y)
    {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  have : (N.subgroupOf Y).Normal := (normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  set q : ↥Y ⧸ N.subgroupOf Y := QuotientGroup.mk' (N.subgroupOf Y) ⟨x, hxY⟩ with hq
  have h1 : orderOf q ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have hx' : (⟨x, hxY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hx)
    rw [hq, ← map_pow, hx', map_one]
  have h2 : orderOf q ∣ N.relIndex Y := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (N.relIndex Y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h3 : orderOf q = 1 := by
    have h := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.mp h
  rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem le_of_isPGroup_of_odd_relIndex {N Y P : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ normalizer (N : Set G)) (hodd : Odd (N.relIndex Y)) (hPY : P ≤ Y)
    (hP : IsPGroup 2 P) : P ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact mem_of_pow_eq_one_of_odd_relIndex hNY hYN hodd (hPY hx)
    (by simpa using congrArg Subtype.val hk)

end OddIndex

section Perfect

variable {X : Type*} [Group X] [Finite X]

theorem not_isCyclic_sylow_of_isPerfect [Group.IsPerfect X] [Nontrivial X] (S : Sylow 2 X) :
    ¬ IsCyclic (S : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hS
  obtain ⟨N, hN, hNS⟩ := CFSG.exists_normal_isComplement'_of_isCyclic_sylow_two S hS
  have hSc : ∀ a ∈ (S : Subgroup X), ∀ b ∈ (S : Subgroup X), a * b = b * a := by
    intro a ha b hb
    have := (hS.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact congrArg Subtype.val this
  have hdec : ∀ x : X, ∃ n ∈ N, ∃ s ∈ (S : Subgroup X), x = n * s := by
    intro x
    have hx : x ∈ ((N ⊔ (S : Subgroup X) : Subgroup X) : Set X) := by
      rw [hNS.sup_eq_top]
      exact mem_top x
    rw [normal_mul] at hx
    obtain ⟨n, hn, s, hs, rfl⟩ := hx
    exact ⟨n, hn, s, hs, rfl⟩
  have hcomm : commutator X ≤ N := by
    rw [commutator_def, commutator_le]
    intro x _ y _
    obtain ⟨n, hn, s, hs, rfl⟩ := hdec x
    obtain ⟨n', hn', s', hs', rfl⟩ := hdec y
    rw [← QuotientGroup.eq_one_iff (N := N), ← QuotientGroup.mk'_apply, map_commutatorElement]
    have hn1 : QuotientGroup.mk' N n = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    have hn1' : QuotientGroup.mk' N n' = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn'
    have h1 : QuotientGroup.mk' N (n * s) = QuotientGroup.mk' N s := by
      rw [map_mul, hn1, one_mul]
    have h2 : QuotientGroup.mk' N (n' * s') = QuotientGroup.mk' N s' := by
      rw [map_mul, hn1', one_mul]
    rw [h1, h2, ← map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr
      (hSc s hs s' hs'), map_one]
  have hNtop : N = ⊤ := top_unique (by rw [← Group.IsPerfect.commutator_eq_top]; exact hcomm)
  have hcard := hNS.card_mul_card
  rw [hNtop, Subgroup.card_top] at hcard
  have hS1 : Nat.card (S : Subgroup X) = 1 := by
    have hpos : 0 < Nat.card X := Nat.card_pos
    nlinarith [hcard]
  have h2 : 2 ∣ Nat.card X := (show (2 : ℕ) ∣ 4 by norm_num).trans four_dvd_card_of_isPerfect
  exact S.ne_bot_of_dvd_card h2 (Subgroup.card_eq_one.mp hS1)

end Perfect

section Center

variable {P Q : Type*} [Group P] [Group Q]

theorem map_center_of_mulEquiv (e : P ≃* Q) : (center P).map e.toMonoidHom = center Q := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_center_iff]
    intro q
    have h := mem_center_iff.mp hx (e.symm q)
    have h' := congrArg e h
    simpa using h'
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    change e.symm y ∈ center P
    rw [mem_center_iff]
    intro p
    have h := mem_center_iff.mp hy (e p)
    have h' := congrArg e.symm h
    simpa using h'

theorem card_center_congr (e : P ≃* Q) : Nat.card (center P) = Nat.card (center Q) :=
  Nat.card_congr (Subgroup.centerCongr e).toEquiv

noncomputable def quotientCenterCongr (e : P ≃* Q) : P ⧸ center P ≃* Q ⧸ center Q :=
  QuotientGroup.congr (center P) (center Q) e (map_center_of_mulEquiv e)

end Center

section Quasisimple

variable {G : Type*} [Group G]

theorem mem_centralizer_of_commutator_mem {A X : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hcen : A ⊓ X ≤ centralizer (A : Set G)) {x : G}
    (hx : ∀ a ∈ A, ∀ k : ℤ, ⁅a, (x ^ k : G)⁆ ∈ A ⊓ X) : x ∈ centralizer (A : Set G) := by
  have hperf : Group.IsPerfect A := ⟨hq.1⟩
  have h1 : ⁅A, zpowers x⁆ ≤ A ⊓ X := by
    rw [commutator_le]
    intro a ha z hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact hx a ha k
  have h2 : ⁅⁅A, zpowers x⁆, A⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact h1.trans hcen
  have h3 := CFSG.LocalCores.perfect_double_commutator hperf h2
  rw [commutator_eq_bot_iff_le_centralizer] at h3
  rw [mem_centralizer_iff]
  intro a ha
  exact (mem_centralizer_iff.mp (h3 ha) x (mem_zpowers x)).symm

end Quasisimple

end Lemma22Full

end CFSG.ComponentClassification.AS76b
