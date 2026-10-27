module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGenOrbit

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Gen
open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

theorem E0_card_normalizer_ge :
    2 ^ 11 * 443520 ≤ Nat.card (normalizer (E0 : Set ↥Cd)) := by
  set N := normalizer (E0 : Set ↥Cd) with hN
  set K := E0 ⊔ closure {y | y ∈ N ∧ Odd (orderOf y)} with hK
  have hKN : K ≤ N := sup_le Subgroup.le_normalizer ((Subgroup.closure_le N).2 fun y hy => hy.1)
  let t0 : Fin 5 → Fin 3510 := ![190, 195, 526, 594, 752]
  have horb : 443520 ≤ Nat.card (MulAction.orbit K t0) := orbit_t0_ge
  have hidx : (MulAction.stabilizer K t0).index = Nat.card (MulAction.orbit K t0) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hcardK := Subgroup.card_mul_index (MulAction.stabilizer K t0)
  have ht0U : ∀ i, t0 i ∈ uPts := by
    intro i
    rw [mem_uPts]
    revert i
    decide
  have hE : Nat.card E0 ≤ Nat.card (MulAction.stabilizer K t0) := by
    refine Nat.card_le_card_of_injective
      (fun e => (⟨⟨e.1, Subgroup.mem_sup_left e.2⟩, ?_⟩ : MulAction.stabilizer K t0)) ?_
    · rw [MulAction.mem_stabilizer_iff]
      funext i
      exact E0_smul_eq e.2 (ht0U i)
    · intro e e' h
      exact Subtype.ext (congrArg (fun x : MulAction.stabilizer K t0 => (x : K).1) h)
  have hbig : 2 ^ 11 * 443520 ≤ Nat.card K := by
    have hidx' : 443520 ≤ (MulAction.stabilizer K t0).index := hidx ▸ horb
    have h1 := Nat.mul_le_mul hE hidx'
    rw [hcardK, card_E0] at h1
    exact h1
  exact hbig.trans (Subgroup.card_le_of_le hKN)

theorem E0_card_normalizer :
    Nat.card (normalizer (E0 : Set ↥Cd)) = 2 ^ 11 * 443520 :=
  le_antisymm card_normalizer_le E0_card_normalizer_ge

end CFSG.EvenSporadicStandard.TwoFi22.DS81
