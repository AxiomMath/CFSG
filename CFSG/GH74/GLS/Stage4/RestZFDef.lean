module

public import CFSG.GH74.GLS.Stage4.RestZB
public import CFSG.GH74.GLS.Stage4.RestL92D
public import CFSG.GH74.GLS.Stage4.RestMirror

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4

variable {G : Type} [Group G]

@[expose] def Ch6Notation.HIdx (D : Ch6Notation G) : Prop :=
  ((D.H ⊓ D.K₁) ⊔ (D.H ⊓ D.K₂)).relIndex D.H = 2

theorem Ch6Notation.HIdx.mirror {D : Ch6Notation G} (h : D.HIdx) : D.mirror.HIdx := h

@[expose] def Ch6ZFusionAll : Prop :=
  ∀ (G : Type) [Group G] (D : Ch6Notation G), Ch6Core D → D.ShapeStd → D.HIdx → D.ZFusion

end CFSG.GH74.GLS.Stage4.Rest
