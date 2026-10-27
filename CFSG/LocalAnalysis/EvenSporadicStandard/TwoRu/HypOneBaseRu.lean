module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBase
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuLocalFacts

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.RuSchreier CFSG.Certificates
open CFSG.ComponentClassification.M12Cover

theorem eq_one_of_fix_base {n : ℕ} {Q : RawSchreierDatum n} (hQ : ValidSchreier Q)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ Q.originalSubgroup) (hfix : ∀ b ∈ Q.base.toList, g b = b) :
    g = 1 := by
  have hmem : g ∈ Q.levelSubgroup Q.baseCount := by
    rw [Q.mem_levelSubgroup_iff hQ Q.baseCount le_rfl]
    refine ⟨hg, fun b hb => hfix b ?_⟩
    rwa [List.take_of_length_le (by simp)] at hb
  rw [Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact hmem

theorem fourClassesLarge_ruC_of_base
    (hC : fourBaseC = true) : FourClassesLarge ruC := by
  have h := ruChainC_check.1
  refine fourClassesLarge_of_baseOK (by norm_num) ruC
    (gg := fun l => CFSG.Monster.B.Co2.permOfArr 4060 (ruField4060 1)[l]!) (fun l hl => ?_)
    (by norm_num) (by norm_num) hC (fun g hg hfix => ?_)
  · have hl2 : l < 2 := by simpa [baseGensC] using hl
    refine ⟨?_, ?_⟩
    · have e : baseGensC[l]! = tblOfArr (ruField4060 1)[l]! := by
        interval_cases l <;> simp [baseGensC]
      rw [e]
      exact rep_tblOfArr (CFSG.Monster.B.Co2.rep_permOfArr
        (ruChain_strong_inv h (j := l) (by simp [ruField4060, ruLines4060]; omega))).1
    · rw [← ruChainC_sub]
      apply Subgroup.subset_closure
      change _ ∈ ruChainC.original.toList
      rw [ruChainC, ofArrays_original_toList]
      exact List.mem_map.2 ⟨l, List.mem_range.2 (by simpa [ruCGenCount] using hl2), rfl⟩
  · rw [← ruChainC_sub] at hg
    refine eq_one_of_fix_base (ruChain_valid h) hg fun b hb => ?_
    change b ∈ ruFinList 4060 (by decide) ruCBase at hb
    simp only [ruFinList, ruCBase, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact hfix _ List.mem_cons_self (by decide)
    · exact hfix _ (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)
    · exact hfix _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by decide)

theorem fourClassesLarge_ruL_of_base
    (hL : fourBaseL = true) : FourClassesLarge ruL := by
  have h := ruL_check.1
  refine fourClassesLarge_of_baseOK (by norm_num) ruL
    (gg := fun l => CFSG.Monster.B.Co2.permOfArr 4060 (ruField4060 5)[l]!) (fun l hl => ?_)
    (by norm_num) (by norm_num) hL (fun g hg hfix => ?_)
  · have hl3 : l < 3 := by simpa [baseGensL] using hl
    refine ⟨?_, ?_⟩
    · have e : baseGensL[l]! = tblOfArr (ruField4060 5)[l]! := by
        interval_cases l <;> simp [baseGensL]
      rw [e]
      exact rep_tblOfArr (CFSG.Monster.B.Co2.rep_permOfArr
        (ruChain_strong_inv h (j := l) (by simp [ruField4060, ruLines4060]; omega))).1
    · rw [← ruChainL_sub]
      apply Subgroup.subset_closure
      change _ ∈ ruChainL.original.toList
      rw [ruChainL, ofArrays_original_toList]
      exact List.mem_map.2 ⟨l, List.mem_range.2 hl3, rfl⟩
  · rw [← ruChainL_sub] at hg
    refine eq_one_of_fix_base (ruChain_valid h) hg fun b hb => ?_
    change b ∈ ruFinList 4060 (by decide) ruLChainBase at hb
    simp only [ruFinList, ruLChainBase, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hfix _ List.mem_cons_self (by decide)
    · exact hfix _ (List.mem_cons_of_mem _ List.mem_cons_self) (by decide)

end CFSG.EvenSporadicStandard.TwoRu.HypOne
