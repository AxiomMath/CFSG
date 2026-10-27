module

public import CFSG.ClassicalInvolution.Q3.Q3T7SectB
public import CFSG.ClassicalInvolution.Q3.Q3T7SectC1
public import CFSG.ClassicalInvolution.Uniform.U9G2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open hiding StatedLieTag
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Q3.Disc3
open scoped MatrixGroups commutatorElement

section Sect


variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem dEdgeless_of_top_mem3 (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L)
    (htop : (⊤ : Subgroup X) ∈ Φ) : DEdgeless Φ := by
  have h1 : ∀ L ∈ Φ, L = ⊤ := by
    intro L hL
    obtain ⟨g, hg⟩ := htrans ⊤ htop L hL
    rw [← hg]
    ext x
    rw [mem_conjSub_iff]
    simp
  intro K hK J hJ hadj
  exact ne_of_dAdj hadj ((h1 K hK).trans (h1 J hJ).symm)

theorem thm8SectBelowU_of {n : ℕ} (hn : CITBelowT (.sl2 3 1) n) :
    ∀ (X : Type) [Group X] [Finite X], Nat.card X < n →
      ∀ Φ : Set (Subgroup X), TransSect3 Φ → Φ.Nonempty → ¬ DEdgeless Φ → ¬ DConnected Φ →
        ∃ d : ℕ, ∃ ε : Bool, 5 ≤ d ∧ d ≤ 8 ∧ HasOrthTypeU 3 1 Φ d ε := by
  intro X _ _ hlt Φ h hne hNE hNC
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨D, hcard⟩ := exists_omegaLieU_sect hn hlt h.hyp h.oddCore h.gen h.trans hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Φ t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    let M := toIh8ModelSect D h.hyp h.gen hcard i ht hadm he hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exfalso
      have : IsSimpleGroup X := M.isSimpleGroup_of_g2d4 hp2 hG2d4
      rcases ih8G2D4EdgeU_proved X Φ h.hyp h.aEmpty h.trans t k e ⟨M⟩ hG2d4 with h' | h'
      · exact hNE h'
      · exact hNC h'
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have hthree : ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → False := fun h3' => by
      have : IsSimpleGroup X := isSimpleGroup_of_ih8Model_three M h3'
      exact hNE (ih8ThreeU_proved X Φ h.hyp h.trans t k 1 ⟨M⟩ h3')
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact (hNC (dConnected_of_connectedU M h.hyp hne hG2 hD4 hconn)).elim
    · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hk2 : 2 ≤ k := hadm.2.2.1
        have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases this with rfl | rfl | rfl
        · exact (hA1 ⟨rfl, rfl⟩).elim
        · exact (hthree (Or.inl ⟨rfl, rfl⟩)).elim
        · exact ⟨6, true, by norm_num, by norm_num, .PSL, 4,
            Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩), hLie⟩
      · have hk3 : 3 ≤ k := hadm.2.2.1
        have : k = 3 ∨ k = 4 := by omega
        rcases this with rfl | rfl
        · exact (hthree (Or.inr ⟨rfl, rfl⟩)).elim
        · exact ⟨6, false, by norm_num, by norm_num, .PSU, 4,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)), hLie⟩
      · exact ⟨5, true, by norm_num, by norm_num, .PSp, 2, Or.inl ⟨rfl, rfl, rfl⟩, hLie⟩
      · exact ⟨7, true, by norm_num, by norm_num, .POmegaOdd, 3,
          Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl⟩))), hLie⟩
      · exact ⟨8, true, by norm_num, by norm_num, .POmegaPlus, 4,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
          hLie⟩
      · exact ⟨8, false, by norm_num, by norm_num, .POmegaMinus, 4,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
          hLie⟩
  · exact (hNE (dEdgeless_of_top_mem3 h.trans
      (top_mem_of_sl23_component_sect D hne h.gen hcard i hc))).elim
  · obtain ⟨e⟩ := exists_mulEquiv_m11_sect D h.gen hcard i hc
    exact (hNE (dEdgeless_of_mulEquiv_m11 e h.hyp (D.card_eq h3))).elim

end Sect

end CFSG.ClassicalInvolution.Q3.Q3T7
