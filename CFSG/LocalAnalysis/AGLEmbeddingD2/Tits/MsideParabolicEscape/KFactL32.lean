module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.SylowL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

theorem nonempty_equiv_gl32_of_model {N : Type} [Group N]
    (h : StatedClassicalModel N .PSL 3 2 1) :
    Nonempty (N ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨-, K, hK, hKf, hcard, ⟨e⟩⟩ := h
  exact ⟨e.trans ((CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 K
    (by rw [hcard]; norm_num)).trans (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3))⟩

theorem l32_case {N : Type} [Group N] [Finite N] (hs : IsSimpleGroup N)
    (hnc : ¬ IsMulCommutative N) (hmod : StatedClassicalModel N .PSL 3 2 1)
    (Y : Subgroup (MulAut N)) (hY : innSub N ≤ Y) (h1 : (innSub N).relIndex Y = 1)
    (S : Subgroup (MulAut N)) (hS : IsSylowTwoOf S Y) :
    ∃ P : Subgroup (MulAut N), P ≤ innSub N ∧ Nat.card P = 3 ∧
      (S : Set (MulAut N)) * P = (P : Set (MulAut N)) * S := by
  obtain ⟨e⟩ := nonempty_equiv_gl32_of_model hmod
  have hYZ : Y ≤ innSub N := Subgroup.relIndex_eq_one.mp h1
  have hinj := conj_injective_of_simple hs hnc
  have hYeq : Y = innSub N := le_antisymm hYZ hY
  let g : ↥Y ≃* N :=
    ((MulEquiv.subgroupCongr hYeq).trans (MonoidHom.ofInjective hinj).symm)
  haveI := hs
  have hsG : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := MulEquiv.isSimpleGroup e.symm
  refine sylow_permute_transport (Z := innSub N) hS (g.trans e) ?_
  intro T hT2 hTi
  obtain ⟨P0, hP03, hP0⟩ := exists_order_three_permuting_sylow_two_gl32 hsG T hT2 hTi
  refine ⟨P0, ?_, hP03, hP0⟩
  intro x _
  refine ⟨(g.trans e).symm x, ?_, by simp⟩
  exact Subgroup.mem_subgroupOf.mpr (hYZ ((g.trans e).symm x).2)

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
