module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6


theorem curtisD42_twinE4 {Y : Type} [Group Y] [Nontrivial Y] (t : Fin 8 → Y)
    (hrel : ∀ r ∈ curtisRels, curtisEval (List.ofFn t) r = 1)
    (hgen : Subgroup.closure (Set.range t) = ⊤) : TwinE4 Y := by
  refine ⟨Y, inferInstance, MonoidHom.id Y, Function.surjective_id, ?_,
    Or.inr (curtisD42_lieModel t hrel hgen)⟩
  rw [MonoidHom.ker_id]
  exact IsPGroup.of_card (n := 0) (by simp)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
