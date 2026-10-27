module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZCnt
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.M6ZIff

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem m6z_odd_pocketed_omegaStar {X : Type} [Group X] {n : ℕ} {ε : ℤˣ}
    (h : IsOmegaStar X n ε)
    (hn : (n = 5 ∧ ε = 1) ∨ (n = 6 ∧ ε = 1) ∨ (n = 6 ∧ ε = -1) ∨ (n = 7 ∧ ε = 1) ∨
      (n = 8 ∧ ε = -1) ∨ (n = 8 ∧ ε = 1)) :
    Odd (Nat.card {x : X // IsI4PlusIn (⊤ : Subgroup X) x}) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := h
  letI := i1
  letI := i2
  letI := i3
  rw [m6z_card_pocketed_of_mulEquiv e]
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hπ : piOrth Q ∉ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
      decide
    rw [m6z_card_pocketed_omegaProj_of_not_mem hQ (by omega) hπ,
      m6z_card_four_plus_five hQ hdim]
    decide
  · have hπ : piOrth Q ∉ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
      decide
    rw [m6z_card_pocketed_omegaProj_of_not_mem hQ (by omega) hπ,
      m6z_card_four_plus_six_plus hQ hdim hs]
    decide
  · rw [m6z_card_pocketed_omegaProj_six hQ hdim hs, m6z_card_four_plus_six_minus hQ hdim hs]
    decide
  · have hπ : piOrth Q ∉ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
      decide
    rw [m6z_card_pocketed_omegaProj_of_not_mem hQ (by omega) hπ,
      m6z_card_four_plus_seven hQ hdim]
    decide
  · have hπ : piOrth Q ∉ omegaGroup hQ := by
      rw [piOrth_mem_omegaGroup_iff hQ, hdim, hs]
      decide
    rw [m6z_card_pocketed_omegaProj_of_not_mem hQ (by omega) hπ,
      m6z_card_four_plus_eight_minus hQ hdim hs]
    decide
  · have h2 := m6z_card_pocketed_omegaProj_eight hQ hdim hs
    have h4 := m6z_card_four_plus_eight_plus hQ hdim hs
    have hN : Nat.card {x : omegaProj hQ // IsI4PlusIn (⊤ : Subgroup (omegaProj hQ)) x} =
        14926275 := by omega
    rw [hN]
    decide

theorem m6z_odd_pocketed_omegaCover {X : Type} [Group X] (h : IsOmegaCover X 6 (-1)) :
    Odd (Nat.card {x : X // IsI4PlusIn (⊤ : Subgroup X) x}) := by
  obtain ⟨V, i1, i2, i3, Q, hQ, hdim, hs, ⟨e⟩⟩ := h
  letI := i1
  letI := i2
  letI := i3
  rw [m6z_card_pocketed_of_mulEquiv e]
  rw [m6z_card_pocketed_omega hQ (by omega) (fun h8 => by omega)]
  rw [m6z_card_four_plus_six_minus hQ hdim hs]
  decide

end CFSG.OddStandard.SmallF3.Omega
