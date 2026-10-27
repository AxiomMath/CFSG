module

public import CFSG.GroupTheory.InvariantSubgroup
public import CFSG.ClassicalGroups.Linear.CentreGroupsOrderThree

public section

namespace CFSG.ClassicalGroups.Linear.Model

open Matrix CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.GroupTheory
open CFSG.LargeExtraspecial.S4
open scoped MatrixGroups

theorem exists_not_mem_span_singleton {n : ℕ} {K : Type} [Field K] (hn : 2 ≤ n)
    {c : Fin n → K} (hc : c ≠ 0) : ∃ d : Fin n → K, d ∉ Submodule.span K {c} := by
  by_contra h
  push Not at h
  have htop : Submodule.span K {c} = ⊤ := Submodule.eq_top_iff'.mpr h
  have := finrank_span_singleton (K := K) hc
  rw [htop, finrank_top, Module.finrank_fin_fun] at this
  omega

theorem span_pair_ne_top {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) (c d : Fin n → K) :
    Submodule.span K {c, d} ≠ ⊤ := by
  classical
  intro h
  have h1 := finrank_span_finset_le_card (R := K) ({c, d} : Finset (Fin n → K))
  unfold Set.finrank at h1
  rw [Finset.coe_insert, Finset.coe_singleton, h, finrank_top, Module.finrank_fin_fun] at h1
  have := Finset.card_le_two (a := c) (b := d)
  omega

theorem exists_inv_data_centre (n : ℕ) (K : Type) [Field K] [CharP K 2] (hn : 3 ≤ n)
    {c : Fin n → K} (hc : c ≠ 0) :
    ∃ (x : StatedProj (StatedSL n K)) (Λ : Subgroup (StatedProj (StatedSL n K))),
      ¬ IsPGroup 2 ↥(cg n K c ⊔ conjSubgroup x (cg n K c)) ∧
      conjSubgroup x (cg n K c) ≤ Λ ∧ Λ ≠ ⊤ ∧
      ∀ α : MulAut (StatedProj (StatedSL n K)),
        (∀ v ∈ cg n K c, α v = v) → Λ.map α.toMonoidHom ≤ Λ := by
  obtain ⟨d, hd⟩ := exists_not_mem_span_singleton (by omega : 2 ≤ n) hc
  have hcd : c ∉ Submodule.span K {d} := by
    intro h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hc (by simpa using ht.symm)
    apply hd
    refine Submodule.mem_span_singleton.mpr ⟨t⁻¹, ?_⟩
    rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  obtain ⟨ψ, hψc, hψd⟩ := exists_vec_of_notMem hcd
  have hψd0 : ψ ⬝ᵥ d = 0 := hψd d (Submodule.mem_span_singleton_self d)
  set y₀ := transvSL hψd0 with hy₀
  set x := psl n K y₀ with hx
  have hy₀c : (((y₀ : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c + d := by
    rw [hy₀, coe_transvSL, one_add_vecMulVec_mulVec, hψc, one_smul, add_comm]
  have hxW : conjSubgroup x (cg n K c) = cg n K (c + d) := by
    rw [hx, conjSubgroup_cg, hy₀c]
  have hc' : c + d ∉ Submodule.span K {c} := by
    intro h
    apply hd
    have h2 : d = (c + d) - c := by abel
    rw [h2]
    exact Submodule.sub_mem _ h (Submodule.mem_span_singleton_self c)
  set E : Subgroup (StatedProj (StatedSL n K)) :=
    cg n K c ⊓ Subgroup.normalizer (cg n K (c + d) : Set (StatedProj (StatedSL n K))) with hE
  refine ⟨x, invGroup (cg n K c) E, ?_, ?_, ?_, ?_⟩
  · rw [hxW]
    exact not_isPGroup_cg_sup n K c (c + d) hc hc'
  · rw [hxW]
    exact le_invGroup ⟨x, hxW.symm⟩ inf_le_right
  · set Pl : Submodule K (Fin n → K) := Submodule.span K {c, d} with hPl
    have hcPl : c ∈ Pl := Submodule.subset_span (by simp)
    have hdPl : d ∈ Pl := Submodule.subset_span (by simp)
    have hPl1 : Pl ≠ ⊥ := fun h => hc (by simpa [h] using hcPl)
    have hle : invGroup (cg n K c) E ≤ planeStab n K Pl := by
      refine iSup₂_le fun W hW => ?_
      obtain ⟨⟨g, rfl⟩, hEW⟩ := hW
      obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective _ g
      have hW : conjSubgroup (psl n K g₀) (cg n K c) = cg n K
          ((((g₀ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ c) := conjSubgroup_cg n K c g₀
      rw [hW] at hEW ⊢
      apply cg_le_planeStab
      by_contra hu
      set u : Fin n → K := (((g₀ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) *ᵥ c with hu_def
      have hu0 : u ≠ 0 := fun h => hu (by rw [h]; exact Pl.zero_mem)
      obtain ⟨a, haU, haPl⟩ := exists_vec_of_notMem hu
      have hac : a ⬝ᵥ c = 0 := haPl c hcPl
      have had : a ⬝ᵥ d = 0 := haPl d hdPl
      set X := transvSL hac with hX
      have ht : psl n K X ∈ cg n K c := psl_transvSL_mem_cg hac
      have hXcd : (((X : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (c + d) =
          c + d := by
        rw [hX, coe_transvSL, one_add_vecMulVec_mulVec, dotProduct_add, hac, had, add_zero,
          zero_smul, add_zero]
      have htN : psl n K X ∈ Subgroup.normalizer
          (cg n K (c + d) : Set (StatedProj (StatedSL n K))) := by
        rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_cg, hXcd]
      have h1 := hEW ⟨ht, htN⟩
      rw [mem_normalizer_iff_conjSubgroup_eq, conjSubgroup_cg] at h1
      have hXu : (((X : StatedSL n K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u =
          u + c := by
        rw [hX, coe_transvSL, one_add_vecMulVec_mulVec, haU, one_smul, add_comm]
      rw [hXu] at h1
      obtain ⟨μ, hμ⟩ := eq_smul_of_cg_eq n K hn u (u + c) hu0 h1.symm
      have hcu : c = (μ - 1) • u := by
        rw [sub_smul, one_smul, ← hμ]
        abel
      have hμ1 : μ - 1 ≠ 0 := by
        intro h0
        apply hc
        rw [hcu, h0, zero_smul]
      apply hu
      have : u = (μ - 1)⁻¹ • c := by
        rw [hcu, smul_smul, inv_mul_cancel₀ hμ1, one_smul]
      rw [this]
      exact Pl.smul_mem _ hcPl
    exact ne_top_of_le_ne_top (planeStab_ne_top n K Pl hPl1 (span_pair_ne_top hn c d)) hle
  · intro α hα
    exact invGroup_map_le (cg n K c) E inf_le_left α hα

end CFSG.ClassicalGroups.Linear.Model
