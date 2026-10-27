
module

public import CFSG.GF2Type.Smith1979.GammaU.StepABase

@[expose] public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU Module

@[expose] def RowsSet (C : List (Array ℕ)) (l : V12 ≃ₗ[ZMod 2] V12) : Prop :=
  ∃ r ∈ C, ∀ x, l x = linOfRows r x

theorem mem_spanOf_d0_of_rows {r : Array ℕ} (hr : ∀ d ∈ d0, appN r d ∈ spanList d0) {y : V12}
    (hy : y ∈ spanOf d0) : linOfRows r y ∈ spanOf d0 := by
  have hle : (spanOf d0).map (linOfRows r) ≤ spanOf d0 := by
    rw [← spanOf_map_appN]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
    exact (mem_spanList_iff d0_lt (spanList_lt d0_lt _ (hr d hd))).1 (hr d hd)
  exact hle ⟨y, hy, rfl⟩

end CFSG.GF2Type.Smith1979.GammaU.StepA
