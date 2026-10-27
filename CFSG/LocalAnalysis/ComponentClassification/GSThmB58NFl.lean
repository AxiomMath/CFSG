module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bRows
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp52

theorem T_eq_of_le_zpowers_sup {H : Type} [Group H] [Finite H] (h : Hyp52 H)
    (hle : h.T ≤ zpowers h.a ⊔ h.B) : h.T = h.B ⊔ zpowers h.a := by
  have haT : h.a ∈ h.T :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨h.a_mem_S, h.a_mem_normalizer⟩, h.a_mem_P⟩
  refine le_antisymm ?_ (sup_le h.B_le_T (zpowers_le.mpr haT))
  rw [sup_comm]
  exact hle

theorem row515_or_row516Inner_of_T_ne {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : Hyp52 X) (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCFi : CFProp23IndexElim) (hCFr : CFProp23IndexReduced)
    (hSol : SolomonTwoSubgroupAltInput) (hB6 : SylowKernelStatement) (hCF24 : CFProp24c)
    (hT : h.T ≠ h.B ⊔ zpowers h.a) :
    h.Row515 ∨ (h.Row516 ∧ h.a ∈ h.K ⊔ coreActionKernel h.K) := by
  have hTr : ¬ h.Table517 := fun h17 => hT (h.T_eq_of_le_zpowers_sup (hCFr X h h17))
  have hTi := fun hrow => hT (h.T_eq_of_le_zpowers_sup (hCFi X h hrow))
  obtain ⟨hKC, hKpc⟩ := h.isPComponent_K_centralizer
  have hsol := hSol X hnonab hKP hz hU h.B h.K h.isPGroup_B hKC hKpc
  rcases h.table hB1 hCF23 with ⟨n, hn, hJ, (⟨hKa, hK | hK⟩ | ⟨hKa, hZ, hK⟩)⟩ |
      h2 | h3 | h4 | h5 | h6 | h7
  ·
    exact absurd (Or.inl ⟨n, hn, hJ, hKa, hK⟩) hTi
  ·
    rcases hn with rfl | rfl | rfl
    · obtain ⟨e9⟩ := hK
      have hZK : center (OddBar h.K) = ⊥ :=
        center_eq_bot_of_mulEquiv e9.symm (alternatingGroup.center_eq_bot (by simp))
      exact absurd (Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq
        (fusionZStar_eq_of_center_eq_bot hZK)).trans e9⟩) hsol
    · exact Or.inl ⟨hJ, hKa, hK⟩
    · exact absurd (Or.inr hK) hsol
  ·
    exact absurd (Or.inl ⟨hKa, hZ, Or.inl ⟨n, hn, hJ, hK⟩⟩) hTr
  ·
    exact absurd (Or.inr (Or.inl h2)) hTi
  ·
    exact absurd h3 (h.not_suz hB6 hCF24)
  ·
    by_cases ha : h.a ∈ h.K ⊔ coreActionKernel h.K
    · exact Or.inr ⟨h4, ha⟩
    · exact absurd (Or.inr (Or.inr ⟨h4, ha⟩)) hTi
  ·
    exact absurd (Or.inr (Or.inl h5)) hTr
  ·
    obtain ⟨p, f, hp, hp2, hf, h5f, hJ, hKa, hZ, hK⟩ := h6
    exact absurd (Or.inl ⟨hKa, hZ, Or.inr ⟨p, f, hp, hp2, hf, h5f, hJ, hK⟩⟩) hTr
  ·
    exact absurd (Or.inr (Or.inr (Or.inr h7))) hTr

end Hyp52

end CFSG.ComponentClassification.GSThmB
