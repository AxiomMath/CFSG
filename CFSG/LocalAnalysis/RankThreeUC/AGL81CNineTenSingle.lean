module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenOrbit
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenComp

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem exists_isComponent_of_pLayerIn_ne_bot {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {H : Subgroup G} (hL : pLayerIn p H ≠ ⊥) :
    ∃ J : Subgroup (StarGroup p H), CFSG.IsComponent J := by
  by_contra h
  exact hL ((pLayerIn_eq_bot_iff hp H).mpr
    (CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => h ⟨K, hK⟩))

theorem layer_eq_of_forall_isComponent_iff {X : Type*} [Group X] {J : Subgroup X}
    (hJ : ∀ D : Subgroup X, CFSG.IsComponent D ↔ D = J) : CFSG.layer X = J := by
  rw [CFSG.layer.eq_sSup]
  have hset : {K : Subgroup X | CFSG.IsComponent K} = {J} := by
    ext K
    simp [hJ K]
  rw [hset, sSup_singleton]

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
