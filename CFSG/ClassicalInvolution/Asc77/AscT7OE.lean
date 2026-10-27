module

public import CFSG.ClassicalInvolution.Asc77.AscT7OD
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerAbs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

namespace T7O

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap CFSG.Assembly.Dichotomy
open scoped MatrixGroups

section Layer

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V] {X : Type} [Group X] [Finite X]

theorem layerData_frame (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) (hV : 5 ≤ Module.finrank F V)
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal] :
    LayerData e.range ⊥ (e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩)
      (img e (elemOn Q fr.span ⊔ elemOn Q fr.perp)) := by
  have h2 := two_ne_zero_of_odd_card hodd
  have D : LocalData e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩ fr.span fr.perp :=
    ⟨splitInv_frame fr hQ, hker, span_ne_bot fr, perp_ne_bot fr hV⟩
  have layS := layerGenOn_of_regular hodd h5 D.split.ndS
  have layT := layerGenOn_of_regular hodd h5 D.split.ndT
  exact ⟨le_inf (img_le_range e _) (img_join_le_centralizer D),
    fun x hx p hp => conj_mem_img h2 D hx hp, img_join_perfect D layS layT,
    exists_layers_img D layS layT, bot_le⟩

end Layer

end T7O

end CFSG.ClassicalInvolution.ModelFacts.Orth15
