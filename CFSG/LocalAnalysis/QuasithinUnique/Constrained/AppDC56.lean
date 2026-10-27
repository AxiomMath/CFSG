module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD8

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G]

theorem c56_gen_double {T M H S L : Subgroup G} (C : GCfg T M H S L)
    (hO2 : blockU0 S L = pCoreOf 2 (conjJoin S L)) (hne : conjJoin S L ≠ L)
    {M₀ : Subgroup G} (hSM : S ≤ M₀) (hMT : M₀ ≤ T) (h2 : S.relIndex M₀ = 2) :
    C56_7Concl S H L M₀ := by
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    have hne' : S ≠ M₀ := fun h => by
      rw [← h] at h2
      simp at h2
    exact hne' (le_antisymm hSM hcon)
  have m₀ : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hBD : baumD S L = blockD S L := m₀.baumD_eq C
  have hQ4 : pCoreOf 2 H = baumD S L ⊔ blockU0 S L := by
    rw [hBD, ← C.hUdef, sup_comm]
    exact C.hQeq
  refine ⟨hO2, ?_, hBD, hQ4, m₀.Q_isMax C, (m₀.J_eq_B C).symm, ?_⟩
  · rw [hBD]
    exact m₀.D_elem C
  · intro x hx hxS
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hx, hxS⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hBD]
      exact m.D_inf_conj C
    · rw [hBD, ← C.hUdef]
      exact m.B_eq C
    · intro hj
      exact absurd hj hne
    · intro hj
      exact absurd hj hne
    · intro _ A hA
      have hQx : conjR (pCoreOf 2 H) x = baumD S L ⊔ conjR (blockU0 S L) x := by
        rw [m.Qx_eq C, hBD, ← C.hUdef, sup_comm]
      constructor
      · intro hinv
        rcases m.invariant_members C hA hinv with h | h
        · exact Or.inl (h.trans hQ4)
        · exact Or.inr (h.trans hQx)
      · rintro (h | h)
        · intro s hs
          rw [h, ← hQ4]
          exact C5.conjSubgroup_eq_self (C.S_le_normalizer_Q hs)
        · intro s hs
          rw [h, ← hQx]
          exact C5.conjSubgroup_eq_self (m.S_le_N_conj (fun s hs => C.S_le_normalizer_Q hs) hs)

end CFSG.QuasithinUnique.AppD
