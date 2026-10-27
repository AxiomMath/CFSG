module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57K

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem four_lt_card_Q (hGH : GH74.GH74Statement) (hKG : Foote5KnownGroups)
    (hB4 : GoldschmidtCorB4) (hAut : Foote5AutStructure) (hMW : MacWilliamsStatement)
    (hFC : Foote5FieldCentralizer) : 4 < Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hQ
  push Not at hQ
  obtain ⟨E, hEQ, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := 2) (H := Q) (k := 2) (by rw [h.open_pRank_Q])
  have hE4 : Nat.card E = 4 := by rw [hEc]; norm_num
  have hQ4 : Nat.card Q = 4 := le_antisymm hQ (by rw [← hE4]; exact card_le_of_le hEQ)
  have hEeq : E = Q := eq_of_le_of_card_ge hEQ (by rw [hQ4, hE4])
  have hQsq : ∀ q ∈ Q, q * q = 1 := fun q hq => by
    rw [← sq]
    exact hE.2 q (hEeq ▸ hq)
  have hST := h.not_isSylowOf_top hGH hKG hB4 hAut
  have hna := h.nonabelian_R_of_not_sylow hGH hKG hAut hMW hST
  have hSlt : S < T := lt_of_le_of_ne h.ST fun h1 => hST (by rw [h1]; exact h.sylT)
  obtain ⟨s, hsT, -, hsN, hss, -, hbot, hcomm⟩ := h.exists_s_of_lt hSlt
  obtain ⟨Lin, hD⟩ := h.exists_autData hAut
  obtain ⟨ε⟩ := h.quotient_simple.2
  exact h.false_of_lin_conjugate_Q ε hGH hKG hMW hD hna hQ4 hQsq hsT hsN hss hbot
    (h.lin_of_mem_conjugate_Q ε hFC h.sec4.footeFamilyType hD hQ4 hQsq hsN hbot hcomm)

end Sec5

end CFSG.ComponentClassification.Foote5
