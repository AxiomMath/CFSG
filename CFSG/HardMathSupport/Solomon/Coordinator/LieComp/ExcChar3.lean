module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnipotentThree
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md42047359a2a

@[expose] def ExcChar3OuterExport : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ idx : TauCeti.ValidLieTypeIndex, lieFamily idx.1 = .exceptional →
      lieIndexChar idx.1 = 3 → Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ∀ β : MulAut S, β ^ 3 = 1 → (∀ a : S, MulAut.conj a ≠ β) →
        LieCompExport 3 β ∨ NoThreeComponents β

theorem excChar3Export_of_outer (hQ : YS08.LieQ.LieQConstrainedInner 3)
    (hO : ExcChar3OuterExport) : ExcChar3Export := by
  intro S _ _ hs hna idx hF h3 he β hβ hβ1
  haveI := hs
  by_cases hin : ∃ t : S, MulAut.conj t = β
  · obtain ⟨t, rfl⟩ := hin
    obtain ⟨x, hx, hx3, hx1⟩ :=
      CFSG.HardMathSupport.Dickson.SuzukiReeB.exists_eq_conj_of_mem_range
        (b3Lie_center_eq_bot hna) ⟨t, rfl⟩ hβ hβ1
    have hS : IsChevOfChar 3 S := ⟨idx, YS08.isChevIndexOfChar_of_lieIndexChar_eq h3, he⟩
    rw [hx]
    exact Or.inr (noThreeComponents_of_conj hQ hs hna hS hx1 hx3)
  · exact hO S hs hna idx hF h3 he β hβ fun a h => hin ⟨a, h⟩

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
