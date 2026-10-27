
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M23Check
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.Facts

@[expose] public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.RankThree.LocalRank CFSG.Blueprint

theorem gA_mem : gA ∈ NativeSporadic.M23 := subset_closure (Set.mem_insert _ _)

theorem gB_mem : gB ∈ NativeSporadic.M23 := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem letG_mem (l : ℤ) : letG l ∈ NativeSporadic.M23 := by
  unfold letG
  split_ifs
  · exact gA_mem
  · exact inv_mem gA_mem
  · exact gB_mem
  · exact inv_mem gB_mem

theorem wordG_mem (w : List ℤ) : wordG letG w ∈ NativeSporadic.M23 := by
  unfold wordG
  refine NativeSporadic.M23.list_prod_mem fun g hg => ?_
  obtain ⟨l, -, rfl⟩ := List.mem_map.mp hg
  exact letG_mem l

theorem theta_of_words_m23 (K : Subgroup (Equiv.Perm (Fin 23))) (ps : List (List ℤ × List ℤ))
    (hcov : ∀ y ∈ K, (orderOf y).Prime → orderOf y ≠ 3 →
      ∃ r ∈ ps.map Prod.fst, ∃ c ∈ K, y = c * wordG letG r * c⁻¹)
    (hwit : ∀ p ∈ ps, wordG letG p.2 ∈ K ∧
      3 ∣ orderOf (wordG letG p.1 * (wordG letG p.2 * wordG letG p.1 * (wordG letG p.2)⁻¹))) :
    aschbacherSolvableCore 3 ↥K = ⊥ := by
  refine aschbacherSolvableCore_eq_bot_of_witnesses K (ps.map fun p => wordG letG p.1) ?_ ?_
  · intro y hy hq hq3
    obtain ⟨r, hr, c, hc, rfl⟩ := hcov y hy hq hq3
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, c, hc, rfl⟩
  · intro x hx N _ hN hxN
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hh, h3⟩ := hwit p hp
    exact ⟨_, N.mul_mem hxN (hN _ hh _ hxN), h3⟩

theorem m23_sylow : (9 : ℕ) = 3 ^ (10200960 : ℕ).factorization 3 := by
  rw [show (10200960 : ℕ) = 3 ^ 2 * 1133440 by norm_num,
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
  norm_num

end CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M23
