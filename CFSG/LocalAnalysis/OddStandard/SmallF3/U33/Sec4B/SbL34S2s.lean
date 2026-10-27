module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34Stmt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S6a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


theorem isSylSL34_of_Ctx4L (hl : Ctx4L t L S x₁ x₂ lam rho tau) :
    IsSylSL34 (ctxQ t tau x₁ x₂ rho) := by
  rcases hl.dich with h | h
  · exfalso
    obtain ⟨e⟩ := h
    have hcomm : ∀ a ∈ ctxQ t tau x₁ x₂ rho, ∀ b ∈ ctxQ t tau x₁ x₂ rho, a * b = b * a := by
      intro a ha b hb
      have h1 : e (⟨a, ha⟩ * ⟨b, hb⟩ : ctxQ t tau x₁ x₂ rho) =
          e (⟨b, hb⟩ * ⟨a, ha⟩ : ctxQ t tau x₁ x₂ rho) := by
        rw [map_mul, map_mul, mul_comm]
      exact congrArg Subtype.val (e.injective h1)
    have hQV : ctxQ t tau x₁ x₂ rho ≤ fourGrp x₁ x₂ := by
      intro q hq
      have hmem : q ∈ ctxQ t tau x₁ x₂ rho ⊓
          centralizer ((ctxQ t tau x₁ x₂ rho : Subgroup G) : Set G) :=
        ⟨hq, Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm b hb q hq⟩
      rw [hl.Z_Q] at hmem
      exact hmem
    have hle := Subgroup.card_le_of_le hQV
    rw [hl.card_Q, card_fourGrp hl.toCtx4Q] at hle
    norm_num at hle
  · exact h

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
