module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCExcl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCls3

public section

namespace CFSG.QuasithinUnique.AppC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem c56A5Case : C56A5Case := by
  intro G _ _ T M H S L hcs h5 hj M₀ hSM hMT h2
  obtain ⟨C⟩ := nonempty_cfg hcs hj h5
  have hne : S ≠ M₀ := fun h => by
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have m₀ : Mate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hU0 : blockU0 S L = blockU L := A5.blockU0_eq_blockU hj
  have hBD : baumD S L = blockD S L := m₀.baumD_eq C
  refine ⟨?_, ?_, hBD, ?_, m₀.Q_isMax C, (m₀.J_eq_B C).symm, ?_⟩
  · rw [hU0, hj]
    exact (m₀.blockQ_eq_blockU C).symm
  · rw [hBD]
    exact m₀.D_elem C
  · rw [hBD, hU0, sup_comm]
    exact C.Q_eq
  · intro x hx hxS
    have m : Mate S T M₀ x := ⟨hSM, hMT, h2, hx, hxS⟩
    have hVN : conjR (blockU L) x ≤ Subgroup.normalizer (L : Set G) := (m.V_le_S C).trans C.hSN
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hBD]
      exact m.D_inf_conj C
    · rw [hBD, hU0]
      exact m.B_eq C
    · intro _ hty
      exfalso
      rcases hty with h3 | ⟨n, hn, hlin⟩
      · exact not_alt3_of_alt5 h5 h3
      · exact not_lin2_of_alt5 C.hL h5 hn hlin
    · intro _ _ r hr hrB
      have hrS : r ∈ S := hr.1
      have hrL : r ∈ L := by
        have := hr.2
        rwa [hj] at this
      have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im (conjR (blockU L) x) := by
        rw [m.im_V C]; exact (mem_Estd _).2 t1_mem_Eset
      obtain ⟨v, hv, hπ⟩ := (C.P.mem_im_pf hVN).1 ht1
      obtain ⟨hYmax, hYidx⟩ := m.Yv_isMax C hv hπ
      refine ⟨Yv S L v, hYidx, fun B' => ⟨fun hB' => ?_, fun hB' => ?_⟩⟩
      · rcases m.type_cases C hB' with h | h | h | h
        · exact Or.inl (m.eq_Q_of_type_bot C hB' h)
        · exact Or.inr (Or.inr (Or.inl (m.eq_Yv_of_type_t1 C hB' h hv hπ)))
        · exact Or.inr (Or.inr (Or.inr (m.eq_conj_Yv_of_type_t2 C hrS hrL hrB hB' h hv hπ)))
        · exact Or.inr (Or.inl ((m.eq_VD_of_type_E C hB' h).trans (m.Qx_eq C).symm))
      · rcases hB' with rfl | rfl | rfl | rfl
        · exact m.Q_isMax C
        · exact m.Qx_isMax C
        · exact hYmax
        · exact C56.isMaxElemAbelian_conjSubgroup hYmax (Subgroup.le_normalizer hrS)
    · intro hne'
      exact absurd hj hne'

end CFSG.QuasithinUnique.AppC
