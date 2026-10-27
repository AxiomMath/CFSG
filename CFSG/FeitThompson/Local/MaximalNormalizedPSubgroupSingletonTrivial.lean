module

public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Definitions.MaximalANormalizedQSubgroups
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
public import Mathlib.GroupTheory.Solvable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise

variable {G : Type*} [Group G] {q : ℕ} {M N Q : Subgroup G}

private theorem normalizer_smul (σ : MulAut G) (Q : Subgroup G) :
    normalizer ((σ • Q : Subgroup G) : Set G) = σ • normalizer (Q : Set G) := by
  rw [show (σ • Q) = Q.map σ.toMonoidHom from rfl,
    show (σ • normalizer (Q : Set G)) = (normalizer (Q : Set G)).map σ.toMonoidHom from rfl,
    Subgroup.map_equiv_normalizer_eq]

private theorem isPGroup_smul_and_le_normalizer_smul (σ : MulAut G) (hσ : σ • N = N)
    (hQ : IsPGroup q Q) (hQN : N ≤ normalizer (Q : Set G)) :
    IsPGroup q (σ • Q : Subgroup G) ∧ N ≤ normalizer ((σ • Q : Subgroup G) : Set G) := by
  refine ⟨hQ.of_equiv (Subgroup.equivSMul σ Q), ?_⟩
  calc N = σ • N := hσ.symm
    _ ≤ σ • normalizer (Q : Set G) := Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hQN
    _ = normalizer ((σ • Q : Subgroup G) : Set G) := (normalizer_smul σ Q).symm

theorem smul_mem_maximalNormalizedPSubgroups {σ : MulAut G} (hσ : σ • N = N)
    (hQ : Q ∈ maximalNormalizedPSubgroups N q) :
    (σ • Q : Subgroup G) ∈ maximalNormalizedPSubgroups N q := by
  have hσ' : σ⁻¹ • N = N := by rw [inv_smul_eq_iff, hσ]
  obtain ⟨h1, h2⟩ := isPGroup_smul_and_le_normalizer_smul σ hσ (isPGroup_of_mem hQ)
    (le_normalizer_of_mem hQ)
  refine mem_maximalNormalizedPSubgroups_of_forall h1 h2 fun R hR hRN hQR => ?_
  obtain ⟨h3, h4⟩ := isPGroup_smul_and_le_normalizer_smul σ⁻¹ hσ' hR hRN
  have hQR' : Q ≤ (σ⁻¹ • R : Subgroup G) := by
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := σ⁻¹).2 hQR
    rwa [inv_smul_smul] at this
  have := eq_of_mem_of_le hQ h3 h4 hQR'
  rw [← this, smul_inv_smul]

theorem le_normalizer_of_maximalNormalizedPSubgroups_eq_singleton
    (hMN : M ≤ normalizer (N : Set G)) (h : maximalNormalizedPSubgroups N q = {Q}) :
    M ≤ normalizer (Q : Set G) := by
  intro m hm
  have hfix : MulAut.conj m • N = N := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hMN hm)
  have hQ : Q ∈ maximalNormalizedPSubgroups N q := by rw [h]; rfl
  have := smul_mem_maximalNormalizedPSubgroups (σ := MulAut.conj m) hfix hQ
  rw [h, Set.mem_singleton_iff] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 this

theorem eq_bot_of_isPGroup_of_isCoatom_of_le_normalizer [Finite G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hq : q.Prime) (hM : IsCoatom M)
    (hqF : ¬ q ∣ Nat.card (fittingRaw M)) (hQM : M ≤ normalizer (Q : Set G))
    (hQ : IsPGroup q Q) : Q = ⊥ := by
  have := Fact.mk hq
  by_contra hQb
  have hlt : normalizer (Q : Set G) < ⊤ := normalizer_lt_top_of_isPGroup hG hq hQb hQ
  have hNQ : normalizer (Q : Set G) = M := by
    rcases lt_or_eq_of_le hQM with h | h
    · exact absurd (hM.2 _ h) hlt.ne
    · exact h.symm
  have hQle : Q ≤ M := hNQ ▸ Subgroup.le_normalizer
  have hcard : Nat.card (Q.subgroupOf M) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
  have hnorm : (Q.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).2 hQM
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hpp : IsPrimePowerOrder (Q.subgroupOf M) :=
    isPrimePowerOrder_iff.2 ⟨q, hq, n, by rw [hcard, hn]⟩
  have hdvd : Nat.card (Q.subgroupOf M) ∣ Nat.card (fittingRaw M) :=
    Subgroup.card_dvd_of_le (le_fittingRaw hnorm hpp)
  rw [hcard, hn] at hdvd
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hQb (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  exact hqF ((dvd_pow_self q hn0).trans hdvd)

theorem eq_bot_of_maximalNormalizedPSubgroups_eq_singleton [Finite G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hq : q.Prime) (hM : IsCoatom M)
    (hMN : M ≤ normalizer (N : Set G)) (hqF : ¬ q ∣ Nat.card (fittingRaw M))
    (h : maximalNormalizedPSubgroups N q = {Q}) : Q = ⊥ := by
  have hQ : Q ∈ maximalNormalizedPSubgroups N q := by rw [h]; rfl
  exact eq_bot_of_isPGroup_of_isCoatom_of_le_normalizer hG hq hM hqF
    (le_normalizer_of_maximalNormalizedPSubgroups_eq_singleton hMN h) (isPGroup_of_mem hQ)

theorem eq_bot_of_isPGroup_of_le_normalizer [Finite G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hq : q.Prime) (hM : IsCoatom M)
    (hMN : M ≤ normalizer (N : Set G)) (hqF : ¬ q ∣ Nat.card (fittingRaw M))
    (h : maximalNormalizedPSubgroups N q = {Q}) {R : Subgroup G} (hR : IsPGroup q R)
    (hRN : N ≤ normalizer (R : Set G)) : R = ⊥ := by
  obtain ⟨Q', hQ', hRQ'⟩ := exists_mem_maximalNormalizedPSubgroups_ge hR hRN
  rw [h, Set.mem_singleton_iff] at hQ'
  subst hQ'
  exact le_bot_iff.1 (hRQ'.trans
    (eq_bot_of_maximalNormalizedPSubgroups_eq_singleton hG hq hM hMN hqF h).le)

theorem eq_bot_and_forall_eq_bot_of_maximalNormalizedPSubgroups_eq_singleton [Finite G]
    (_hodd : Odd (Nat.card G)) (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hM : IsCoatom M) (hNM : N ≤ M)
    (hNnormal : (N.subgroupOf M).Normal) (_hN : N ≠ ⊥) (hq : q.Prime)
    (hqF : ¬ q ∣ Nat.card (fittingRaw M)) (h : maximalNormalizedPSubgroups N q = {Q}) :
    Q = ⊥ ∧ ∀ R : Subgroup G, IsPGroup q R → N ≤ normalizer (R : Set G) → R = ⊥ := by
  have := hsimple
  have hMN : M ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).1 hNnormal
  exact ⟨eq_bot_of_maximalNormalizedPSubgroups_eq_singleton hG hq hM hMN hqF h,
    fun _ hR hRN => eq_bot_of_isPGroup_of_le_normalizer hG hq hM hMN hqF h hR hRN⟩

end CFSG.FeitThompson
