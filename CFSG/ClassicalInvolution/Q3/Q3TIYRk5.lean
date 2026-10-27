module

public import CFSG.ClassicalInvolution.Q3.Q3TIYRk1
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk2
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk3
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk4
public import CFSG.ClassicalInvolution.Q3.Q3TIVOr2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.TWY
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD


theorem twinYModel3_plus (n : ℕ) : twinYModel 3 .POmegaPlus n = (.POmegaMinus, n + 1) := by
  simp [twinYModel]

theorem twinYModel3_minus (n : ℕ) : twinYModel 3 .POmegaMinus n = (.POmegaPlus, n + 1) := by
  simp [twinYModel]

theorem twinYModel3_odd (n : ℕ) : twinYModel 3 .POmegaOdd n = (.POmegaOdd, n + 1) := by
  simp [twinYModel]

theorem frames_eq_of_count {Fr Fr' N O : ℕ} (hY : N * O = 2 * Fr)
    (h : 2 * Fr' + O = (1 + N) * O) : Fr' = Fr := by
  rw [add_mul, one_mul, hY] at h
  omega

section Rank

theorem twinRank3Model_plus {nY : ℕ} (hn : 5 ≤ nY) : TwinRank3Model .POmegaPlus nY := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq' t' n' hrow hadm hnsmall R₀ hR₀ hcard
  have hY := card_fund_centralizing3_plus hn hd hãR hã'R hsq hsq'
  rw [twinYModel3_plus]
  rcases hrow with ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, -, hk⟩ := layerCount3_plus hadm hR₀ hcard
    exact (framesPlus_ne_framesMinus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
      (by norm_num) j (nY - 4) (frames_eq_of_count hY hk)).elim
  · exact (hnsmall (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_odd hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesMinus_ne_zero (q := 3) (by norm_num) (nY - 4) (by rw [← hc]; rfl)).elim
    · exact (framesOdd_ne_framesMinus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) j (nY - 4) hc).elim
  · exact (hnsmall (Or.inl ⟨rfl, rfl⟩)).elim
  · obtain ⟨j, hj, hk⟩ := layerCount3_minus hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesMinus_ne_zero (q := 3) (by norm_num) (nY - 4) (by rw [← hc]; rfl)).elim
    · have hj' : j = nY - 4 := framesMinus_inj3 Nat.prime_three (by norm_num) le_rfl
        (by norm_num) (by norm_num) hc
      exact ⟨rfl, by show _ = nY + 1; omega⟩
  · exact (hnsmall (Or.inr (Or.inr ⟨rfl, rfl⟩))).elim

theorem twinRank3Model_minus {nY : ℕ} (hn : 4 ≤ nY) : TwinRank3Model .POmegaMinus nY := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq' t' n' hrow hadm hnsmall R₀ hR₀ hcard
  have hY := card_fund_centralizing3_minus hn hd hãR hã'R hsq hsq'
  rw [twinYModel3_minus]
  rcases hrow with ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, hj, hk⟩ := layerCount3_plus hadm hR₀ hcard
    have hj' : j = nY - 3 := framesPlus_inj3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
      (by norm_num) (frames_eq_of_count hY hk)
    exact ⟨rfl, by show _ = nY + 1; omega⟩
  · exact (hnsmall (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_odd hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesPlus_ne_zero (q := 3) (by norm_num) (nY - 3) (by rw [← hc]; rfl)).elim
    · exact (framesOdd_ne_framesPlus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) j (nY - 3) hc).elim
  · exact (hnsmall (Or.inl ⟨rfl, rfl⟩)).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_minus hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesPlus_ne_zero (q := 3) (by norm_num) (nY - 3) (by rw [← hc]; rfl)).elim
    · exact (framesPlus_ne_framesMinus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) (nY - 3) j hc.symm).elim
  · exact (hnsmall (Or.inr (Or.inr ⟨rfl, rfl⟩))).elim

theorem twinRank3Model_odd {nY : ℕ} (hn : 3 ≤ nY) : TwinRank3Model .POmegaOdd nY := by
  intro R R' x x' ã ã' hd hãR hã'R hsq hsq' t' n' hrow hadm hnsmall R₀ hR₀ hcard
  have hY := card_fund_centralizing3_odd hn hd hãR hã'R hsq hsq'
  rw [twinYModel3_odd]
  rcases hrow with ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hn'⟩ | ⟨-, rfl, rfl⟩
  · obtain ⟨j, -, hk⟩ := layerCount3_plus hadm hR₀ hcard
    exact (framesOdd_ne_framesPlus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
      (by norm_num) (nY - 3) j (frames_eq_of_count hY hk).symm).elim
  · exact (hnsmall (Or.inr (Or.inl ⟨rfl, rfl⟩))).elim
  · obtain ⟨j, hj, hk⟩ := layerCount3_odd hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesOdd_ne_zero (q := 3) (by norm_num) (nY - 3) (by rw [← hc]; rfl)).elim
    · have hj' : j = nY - 3 := framesOdd_inj3 Nat.prime_three le_rfl (by norm_num) (by norm_num) hc
      exact ⟨rfl, by show _ = nY + 1; omega⟩
  · exact (hnsmall (Or.inl ⟨rfl, rfl⟩)).elim
  · obtain ⟨j, -, hk⟩ := layerCount3_minus hadm hR₀ hcard
    have hc := frames_eq_of_count hY hk
    rcases j with _ | j
    · exact (framesOdd_ne_zero (q := 3) (by norm_num) (nY - 3) (by rw [← hc]; rfl)).elim
    · exact (framesOdd_ne_framesMinus3 Nat.prime_three (by norm_num) le_rfl (by norm_num)
        (by norm_num) (nY - 3) j hc.symm).elim
  · exact (hnsmall (Or.inr (Or.inr ⟨rfl, rfl⟩))).elim

theorem twinRank3Model_large {tY : StatedLieTag} {nY : ℕ} (h : TwinRowLarge3 tY nY) :
    TwinRank3Model tY nY := by
  rcases h with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩
  · exact twinRank3Model_plus hn
  · exact twinRank3Model_minus (by omega)
  · exact twinRank3Model_odd (by omega)

end Rank

end CFSG.ClassicalInvolution.Q3.Q3TIY
