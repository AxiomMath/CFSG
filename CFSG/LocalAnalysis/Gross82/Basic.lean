module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphismsCongr
public import CFSG.LocalAnalysis.GL83PartI.I710.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer congr_mem_inner_iff)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 (R891GrossCore)

theorem exists_sylow_eq_of_isSylowOf_top {K : Type*} [Group K] [Finite K] {P : Subgroup K}
    (hP : IsSylowOf 3 P ⊤) : ∃ Q : Sylow 3 K, (Q : Subgroup K) = P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hPgrp, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hPgrp.toSylow hdvd, IsPGroup.toSylow_coe _ _⟩

private theorem conj_comm_of_fix {K : Type*} [Group K] {α : MulAut K} {P : Subgroup K}
    (hfix : ∀ x ∈ P, α x = x) {Q : Sylow 3 K} (hQ : (Q : Subgroup K) = P) :
    ∀ g ∈ (Q : Subgroup K), α * MulAut.conj g = MulAut.conj g * α := by
  intro g hg
  have hgP : g ∈ P := by rw [← hQ]; exact hg
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix g hgP]

theorem exists_eq_conj_of_isSylowOf_top_of_mem_inner {K : Type*} [Group K] [Finite K]
    (hZ : Subgroup.center K = ⊥) (α : MulAut K) (hα : ∃ k : ℕ, orderOf α = 3 ^ k)
    (P : Subgroup K) (hP : IsSylowOf 3 P ⊤) (hfix : ∀ x ∈ P, α x = x)
    (hinner : α ∈ inner K) : ∃ t ∈ P, α = MulAut.conj t := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_isSylowOf_top hP
  have hα' : ∃ n : ℕ, α ^ (3 ^ n) = 1 := by
    obtain ⟨k, hk⟩ := hα
    exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one α⟩
  obtain ⟨t, ht, htα⟩ :=
    GL83.I710.exists_eq_conj_of_mem_inner (p := 3) hZ Q hα' (conj_comm_of_fix hfix hQ) hinner
  exact ⟨t, by rwa [hQ] at ht, htα⟩

end CFSG.LocalAnalysis.Gross82
