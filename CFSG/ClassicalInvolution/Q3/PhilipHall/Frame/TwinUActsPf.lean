module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPfCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

theorem twinFrameUActs_of_hyp {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) : TwinVtx.TwinFrameUActs Ω :=
  fun _ _ _ _ _ _ hf => twinFrame_u_mem_centralizerModOdd hΩ hf

section Core


theorem twinFrameUActs_of_core {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (h : TwinCoreHyp n Y R S t) :
    TwinVtx.TwinFrameUActs (CoreAssembly.conjClass (tightCore R)) :=
  twinFrameUActs_of_hyp h.hyp

end Core

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf

end
