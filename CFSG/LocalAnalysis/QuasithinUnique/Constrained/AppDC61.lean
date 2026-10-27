module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD9

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC

variable {G : Type} [Group G] [Finite G]

theorem c61_gen {T M H S L : Subgroup G} (C : GCfg T M H S L)
    (hO2 : blockU0 S L = pCoreOf 2 (conjJoin S L))
    (hvac : conjJoin S L = L → ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 3) → False)
    (hcase : (IsAltType L 5 ∧ conjJoin S L = L) ∨ (IsAltType L 3 ∧ conjJoin S L ≠ L))
    (hA3 : IsAltType L 3 → conjJoin S L = L → False) : C61Concl T H S L := by
  obtain ⟨M₀, hSM, hMT, h2⟩ := C56.exists_index_two C.hcs
  have hne : S ≠ M₀ := fun h => by
    rw [← h] at h2
    simp at h2
  obtain ⟨x₀, hx₀, hx₀S⟩ : ∃ x ∈ M₀, x ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hSM hcon)
  have m₀ : GMate S T M₀ x₀ := ⟨hSM, hMT, h2, hx₀, hx₀S⟩
  have hNT : normT T S = M₀ := m₀.normT_eq C
  have hJ : thompsonJ M₀ = thompsonJ S := thompsonJ_M₀_eq C hSM hMT h2
  have hbaum : ∀ x ∈ M₀, x ∉ S → baum S = pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x := by
    intro x hx hxS
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hx, hxS⟩
    refine C56.baum_eq_sup_conj (L := L) (normalizer_of_relIndex_two hSM h2 hx) ?_ ?_
    · rw [m.baumD_eq C, ← C.hUdef, C.hQeq, sup_comm]
    · rw [m.baumD_eq C, ← C.hUdef]
      exact m.B_eq C
  refine ⟨⟨by rw [hNT]; exact h2, fun x hxN hxS => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [hNT] at hxN
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hxN, hxS⟩
    exact ⟨m.J_eq_B C, hbaum x hxN hxS⟩
  · intro hj hor
    exact (hvac hj hor).elim
  · intro _ x hxN hxS r hrS hrJ
    rw [hNT] at hxN
    have m : GMate S T M₀ x := ⟨hSM, hMT, h2, hxN, hxS⟩
    exact m.a5_classification C hrS (by rw [← m.J_eq_B C]; exact hrJ)
  · rw [C.hQeq, C.hUdef, hO2, sup_comm]
  · by_cases hTM : M₀ = T
    · left
      refine ⟨?_, ?_, fun h3 hj => (hA3 h3 hj).elim⟩
      · rw [← hTM]; exact h2
      · rw [← hTM]; exact hJ.symm
    · right; right
      obtain ⟨F⟩ := m₀.nonempty_four C
      refine ⟨hcase, ?_, ?_, ?_⟩
      · rw [hNT]; exact hJ.symm
      · rw [hNT, m₀.J_eq_B C]
        exact m₀.rho_dihedral C F C.hcs.setting.sylow.isPGroup hTM
      · intro A₁ hA₁ hAQ _
        obtain ⟨i, rfl⟩ := (m₀.members C F).1 hA₁
        have hi : i ≠ 0 := fun h => hAQ (by rw [h]; rfl)
        exact m₀.card_normalizer_pair C F C.hcs.setting.sylow.isPGroup hTM hi

end CFSG.QuasithinUnique.AppD
