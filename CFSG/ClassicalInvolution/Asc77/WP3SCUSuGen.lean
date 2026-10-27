module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUGenC

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.BorelTits

theorem suPairGen : SuPairGen := by
  intro p _ e n hp2 h5 hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hK := CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq h5
  have hq : p ^ e ≠ 2 := by omega
  rw [eq_top_iff, ← iSup_range_blockEmb2 hK hq m]
  refine iSup_le fun i => ?_
  have hij : (Fin.castSucc i : Fin (m + 1)) ≠ Fin.succ i := by
    intro h
    have := congrArg Fin.val h
    simp at this
  refine le_trans ?_ (le_iSup_of_le (Fin.castSucc i) (le_iSup_of_le (Fin.succ i)
    (le_iSup_of_le hij le_rfl)))
  rintro _ ⟨A, rfl⟩
  rw [mem_coordBlockSU_iff]
  intro a b hab
  have hnot : ¬ (((i : ℕ) ≤ a.val ∧ a.val < (i : ℕ) + 2) ∧
      ((i : ℕ) ≤ b.val ∧ b.val < (i : ℕ) + 2)) := by
    rintro ⟨ha, hb⟩
    rcases hab with h | h
    · apply h
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_succ]
      omega
    · apply h
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_castSucc,
        Fin.val_succ]
      omega
  show (blockMat (m + 1) (i : ℕ) _ : Matrix (Fin (m + 1)) (Fin (m + 1)) _) a b = _
  rw [blockMat_apply, dite_eq_right hnot]
  simp [Matrix.one_apply]

end CFSG.ClassicalInvolution.Asc77
