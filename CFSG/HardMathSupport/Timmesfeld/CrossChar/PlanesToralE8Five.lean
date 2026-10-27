module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralFive
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralE8
public import CFSG.HardMathSupport.Timmesfeld.Torality.E8A4Block
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangThree

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality

theorem iform_e8s (j k : Fin 4) : iform (e8s j) (e8s k) =
    if j = k then 2 else if (j : ℕ) + 1 = k ∨ (k : ℕ) + 1 = j then -1 else 0 := by
  revert j k
  decide +kernel

theorem chainSum_mem_aChainRoots (β : Fin 4 → Fin Tag.E8.rank → ℤ) {i j : Fin 5}
    (hij : i ≠ j) : chainSum β i j ∈ aChainRoots β := by
  classical
  have key : ∀ (c : Fin 4 → ℤ) (s : Finset (Fin 4)), (∀ k, c k = if k ∈ s then 1 else 0) →
      ∑ k : Fin 4, c k • β k = ∑ k ∈ s, β k := by
    intro c s hc
    rw [← Finset.univ_inter s, ← Finset.sum_ite_mem]
    exact Finset.sum_congr rfl fun k _ => by rw [hc k]; split_ifs <;> simp
  rcases lt_or_gt_of_ne hij with h | h
  · have h' : (i : ℕ) < j := h
    refine ⟨⟨i, by omega⟩, ⟨j - 1, by omega⟩, Fin.mk_le_mk.2 (by omega), Or.inl ?_⟩
    rw [chainSum]
    refine key _ _ fun k => ?_
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
    split_ifs <;> omega
  · have h' : (j : ℕ) < i := h
    refine ⟨⟨j, by omega⟩, ⟨i - 1, by omega⟩, Fin.mk_le_mk.2 (by omega), Or.inr ?_⟩
    have hs := key (fun k => if (j : ℕ) ≤ k ∧ (k : ℕ) < i then 1 else 0)
      (Finset.Icc ⟨j, by omega⟩ ⟨i - 1, by omega⟩) (fun k => by
        simp only [Finset.mem_Icc, Fin.le_iff_val_le_val]
        split_ifs <;> omega)
    rw [← hs, ← Finset.sum_neg_distrib, chainSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← neg_smul]
    congr 1
    split_ifs <;> omega

theorem chainSet5_subset_aChainRoots (β : Fin 4 → Fin Tag.E8.rank → ℤ) :
    chainSet5 β ⊆ aChainRoots β := by
  rintro r ⟨i, j, hij, rfl⟩
  exact chainSum_mem_aChainRoots β hij

section


theorem isE8Chain_of_isAChain {β : Fin 4 → Fin Tag.E8.rank → ℤ} (h : IsAChain β) :
    IsE8Chain β where
  isRoot := h.isRoot
  gram j k := by
    rw [iform_e8s]
    split_ifs with hjk h12
    · subst hjk
      exact iform_self_E8 (h.isRoot j)
    · rcases h12 with h1 | h2
      · exact h.adj j k h1.symm
      · rw [iform_comm]
        exact h.adj k j h2.symm
    · have hjk' : (j : ℕ) ≠ k := fun e => hjk (Fin.ext e)
      rcases lt_or_gt_of_ne hjk' with h3 | h3
      · exact h.orth j k (by omega)
      · rw [iform_comm]
        exact h.orth k j (by omega)

end


theorem chainBlockToral_E8_four : ChainBlockToral Tag.E8 4 := by
  intro L _ _ hL β hβ
  obtain ⟨m, hmS, hmN, hmρ, hmt⟩ := a4Block_E8 (L := L) hL (isE8Chain_of_isAChain hβ)
  have hsub : rootSpan Tag.E8 L (chainSet5 β) ≤ rootSpan Tag.E8 L (aChainRoots β) :=
    biSup_mono (chainSet5_subset_aChainRoots β)
  refine ⟨m, hsub hmS, hmN, by rw [hmρ, chainRefl_four], fun t ht => ?_⟩
  obtain ⟨y, hy, hyt⟩ := hmt t ht
  exact ⟨y, hsub hy, hyt⟩

theorem planesToralBar_E8_five_of_stab
    (hstab : ∀ (L : Type) [Field L] (a : Fin Tag.E8.rank → Lˣ), (∀ i, a i ^ 5 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    PlanesToralBar Tag.E8 5 :=
  planesToralBar_five_of_chainBlock (fun _ hγ => iform_self_E8 hγ) chainBlockToral_E8_four hstab

theorem e8FiveToralPlane_of_stab
    (hstab : ∀ (L : Type) [Field L] (a : Fin Tag.E8.rank → Lˣ), (∀ i, a i ^ 5 = 1) →
      rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    E8FiveToralPlane :=
  e8FiveToralPlane_of_bar (planesToralBar_E8_five_of_stab hstab)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
