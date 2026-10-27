module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mem_commutator_of_cube_of_inverts {Y : Subgroup G} {t w : G}
    (ht : t ∈ Y) (hw : w ∈ Y) (hw3 : w ^ 3 = 1) (hinv : t * w * t⁻¹ = w⁻¹) :
    w ∈ ⁅Y, Y⁆ := by
  have hc : ⁅t, w⁆ = w := by
    rw [commutatorElement_def, hinv]
    have hww : w * w * w = 1 := by simpa [pow_succ, pow_two] using hw3
    calc w⁻¹ * w⁻¹ = (w * w)⁻¹ := by rw [mul_inv_rev]
      _ = w := (inv_eq_iff_mul_eq_one).2 hww
  rw [← hc]
  exact Subgroup.commutator_mem_commutator ht hw

theorem IsE27InvConfig.le_commutator {Y V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hc : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) (hV : V ≤ Y)
    (ht₁ : t₁ ∈ Y) (ht₂ : t₂ ∈ Y) (ht₃ : t₃ ∈ Y) : V ≤ ⁅Y, Y⁆ := by
  have hW₁ : W₁ ≤ V := hc.join ▸ le_sup_left.trans le_sup_left
  have hW₂ : W₂ ≤ V := hc.join ▸ le_sup_right.trans le_sup_left
  have hW₃ : W₃ ≤ V := hc.join ▸ le_sup_right
  rw [hc.join]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro w hw
    exact mem_commutator_of_cube_of_inverts ht₁ (hV (hW₁ hw))
      (hc.elem.2 w (hW₁ hw)) (hc.inv₁ w hw)
  · intro w hw
    exact mem_commutator_of_cube_of_inverts ht₂ (hV (hW₂ hw))
      (hc.elem.2 w (hW₂ hw)) (hc.inv₂ w hw)
  · intro w hw
    exact mem_commutator_of_cube_of_inverts ht₃ (hV (hW₃ hw))
      (hc.elem.2 w (hW₃ hw)) (hc.inv₃ w hw)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
