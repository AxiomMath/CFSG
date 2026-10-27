module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X]

theorem component_perfect {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (h : IsComponentOf Ls ⊤) : Group.IsPerfect ↥Ls :=
  ⟨h.2.2.1⟩

@[expose] noncomputable def exists_map_to_component {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {K : Subgroup X} (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype) :
    K →* ↥Ls where
  toFun k :=
    ⟨QuotientGroup.mk (k : X),
      (Subgroup.map_subtype_le (Subgroup.center ↥Ls))
        (hKcen (Subgroup.mem_map_of_mem (QuotientGroup.mk' (gnC T)) k.2))⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' k l := by
    apply Subtype.ext
    rfl

@[simp] theorem exists_map_to_component_apply {T : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {K : Subgroup X} (hKcen : gnImg T K ≤ (Subgroup.center ↥Ls).map Ls.subtype) (k : K) :
    (exists_map_to_component hKcen k : X ⧸ gnC T) = QuotientGroup.mk (k : X) :=
  rfl

end CFSG.LocalAnalysis.RankThreeUC.S15

end
