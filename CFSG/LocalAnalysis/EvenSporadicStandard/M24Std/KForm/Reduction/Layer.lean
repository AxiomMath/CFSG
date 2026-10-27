module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Input
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporLocal

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Reduction

open Subgroup

theorem egaLayer_eq_layer (Y : Type) [Group Y] : egaLayer Y = CFSG.layer Y := by
  unfold egaLayer CFSG.layer CFSG.WholeGroup.layerOf
  refine le_antisymm (iSup₂_le fun K hK => le_sSup ((CFSG.isComponent_iff_open K).2 hK)) ?_
  exact sSup_le fun K hK => le_iSup₂_of_le K ((CFSG.isComponent_iff_open K).1 hK) le_rfl

theorem layer_eq_of_simple_normal {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a)
    (hC : ∀ x ∈ centralizer (S : Set Y), ∀ y ∈ centralizer (S : Set Y), x * y = y * x) :
    CFSG.layer Y = S := by
  have hnab' : ∃ a b : ↥S, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hcomm : ∀ x y : ↥(centralizer (S : Set Y)), x * y = y * x :=
    fun x y => Subtype.ext (hC x x.2 y y.2)
  have hsolv : Group.IsSolvable ↥(centralizer (S : Set Y)) := Group.isSolvable_of_comm hcomm
  unfold CFSG.layer CFSG.WholeGroup.layerOf
  refine le_antisymm (sSup_le fun K hK => ?_) ?_
  · exact (CFSG.ComponentClassification.RestrictedStd.Spor.eq_of_isComponent_of_simple_normal
      hS hsolv hK).le
  · have hq : CFSG.IsQuasisimple ↥S := (LocalCores.isQuasisimple_of_isSimpleGroup hnab').1
    have hcomp : CFSG.IsComponent S := ⟨hq, (inferInstance : S.Normal).isSubnormal⟩
    exact le_sSup hcomp

theorem egaLayer_eq_of_simple_normal {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hS : IsSimpleGroup ↥S) (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a)
    (hC : ∀ x ∈ centralizer (S : Set Y), ∀ y ∈ centralizer (S : Set Y), x * y = y * x) :
    egaLayer Y = S := by
  exact (egaLayer_eq_layer Y).trans (layer_eq_of_simple_normal S hS hnab hC)

end CFSG.EvenSporadicStandard.M24Std.KForm.Reduction
