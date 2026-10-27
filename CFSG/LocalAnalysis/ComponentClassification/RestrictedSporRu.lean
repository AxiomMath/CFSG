module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporRuCheck

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.RuSchreier
open CFSG.Sporadic.Schreier (centralizerIn centralizerIn_conj)

theorem ruC_comps : CompsSatisfy ruC fun Y _ => ¬ 3 ∣ Nat.card Y := by
  have hn : (4060 : ℕ) < 2 ^ 32 := by norm_num
  have hC0 : ruC0 ∈ ruC := subset_closure (Set.mem_insert _ _)
  have hC1 : ruC1 ∈ ruC := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hg : ∀ l < ruCTab.size, Rep 4060 ruCTab[l]! ([ruC0, ruC1].getD l 1) ∧
      Rep 4060 ruCInvTab[l]! ([ruC0, ruC1].getD l 1)⁻¹ ∧ [ruC0, ruC1].getD l 1 ∈ ruC := by
    intro l hl
    have hl2 : l < 2 := by simpa [ruCTab] using hl
    interval_cases l
    · exact ⟨by simpa [ruCTab] using rep_arrTable hn rep_ruC0,
        by simpa [ruCInvTab] using rep_arrTable hn (rep_ruInv rep_ruC0 ruBasic_check.2.2.2.2.2.2.1),
        by simpa using hC0⟩
    · exact ⟨by simpa [ruCTab] using rep_arrTable hn rep_ruC1,
        by simpa [ruCInvTab] using
          rep_arrTable hn (rep_ruInv rep_ruC1 ruBasic_check.2.2.2.2.2.2.2.1),
        by simpa using hC1⟩
  have hgen : ruC ≤ closure {g | ∃ l < ruCTab.size, g = [ruC0, ruC1].getD l 1} := by
    rw [ruC, closure_le]
    rintro g (rfl | rfl)
    · exact subset_closure ⟨0, by simp [ruCTab], rfl⟩
    · exact subset_closure ⟨1, by simp [ruCTab], rfl⟩
  set LG : ℤ → Equiv.Perm (Fin 4060) := fun z => if z = 1 then ruC0 else ruC1 with hLG
  have hL : ∀ z, Rep 4060 (ruLetterTab z) (LG z) := by
    intro z
    by_cases hz : z = 1
    · simpa [ruLetterTab, hLG, hz] using rep_arrTable hn rep_ruC0
    · simpa [ruLetterTab, hLG, hz] using rep_arrTable hn rep_ruC1
  have hwmem : ∀ w : List ℤ, wordG LG w ∈ ruC := by
    intro w
    induction w with
    | nil => exact ruC.one_mem
    | cons z w ih =>
      have hz : LG z ∈ ruC := by
        by_cases h : z = 1
        · simpa [hLG, h] using hC0
        · simpa [hLG, h] using hC1
      simpa [wordG] using ruC.mul_mem hz ih
  have hq := (Rep.wordT hn ruQWord fun l _ => hL l).powT hn 60
  have hy := (Rep.wordT hn ruYWord fun l _ => hL l).powT hn 2
  exact compsSatisfy_of_threeWitnessOK_of_rep ruC hg hgen (ruC.pow_mem (hwmem _) _)
    (ruC.pow_mem (hwmem _) _) hq hy ru_three_witness_check (by rw [card_ruC]; norm_num)

theorem ru_centralizerIn_comps : ∀ u ∈ ruP, orderOf u = 2 →
    CompsSatisfy (centralizerIn ruP u) fun Y _ => ¬ 3 ∣ Nat.card Y := by
  intro u hu ho
  have hmem : u ∈ {t | t ∈ ruP ∧ orderOf t = 2} := ⟨hu, ho⟩
  rw [ruInvolutions_eq] at hmem
  rcases hmem with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
  · rw [centralizerIn_conj ruP hg, centralizerIn, ← ruC_eq_centralizer]
    exact CompsSatisfy.of_mulEquiv isoInvariant_not_three_dvd (conjEquiv ruC g).symm ruC_comps
  · rw [centralizerIn_conj ruP hg, centralizerIn, ruCentralizer_a]
    exact CompsSatisfy.of_mulEquiv isoInvariant_not_three_dvd (conjEquiv ruL g).symm
      (compsSatisfy_not_three_of_card (by rw [card_ruL]; norm_num))

end CFSG.ComponentClassification.RestrictedStd.Spor
