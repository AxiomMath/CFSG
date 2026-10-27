module

public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Stage2Ctx.toCtx0 (h : Stage2Ctx G z k S) : Stage2Ctx0 G z k S :=
  ⟨h.std.toStd0, h.central, h.sylow, h.data, h.detail, h.rank_three⟩

theorem Stage2Ctx0.toCtx (h : Stage2Ctx0 G z k S) (hlb : IsLB2Type G)
    (hnu : ¬ HasTwoUniquenessSubgroup G) : Stage2Ctx G z k S :=
  ⟨⟨h.std.kps, h.std.gen4, h.std.kgh, h.std.rank, h.std.nonab, hlb, hnu⟩, h.central, h.sylow, h.data,
    h.detail, h.rank_three⟩

theorem Stage2Ctx0.toCtx' (h : Stage2Ctx0 G z k S) (hs : Std G) : Stage2Ctx G z k S :=
  h.toCtx hs.lb2 hs.noUniq

end CFSG.GH74.GLS.Stage2.Local
