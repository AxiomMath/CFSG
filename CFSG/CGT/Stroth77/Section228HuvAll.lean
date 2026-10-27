module

public import CFSG.CGT.Stroth77.Section228Huv
public import CFSG.CGT.Stroth77.Section228Uv110
public import CFSG.CGT.Stroth77.Section228Uv111
public import CFSG.CGT.Stroth77.Section228Uv121
public import CFSG.CGT.Stroth77.Section228Uv120
public import CFSG.CGT.Stroth77.Section228Uv130
public import CFSG.CGT.Stroth77.Section228Uv131
public import CFSG.CGT.Stroth77.Section228Uv210
public import CFSG.CGT.Stroth77.Section228Uv211
public import CFSG.CGT.Stroth77.Section228Uv220
public import CFSG.CGT.Stroth77.Section228Uv221
public import CFSG.CGT.Stroth77.Section228Uv230
public import CFSG.CGT.Stroth77.Section228Uv231
public import CFSG.CGT.Stroth77.Section228Uv320
public import CFSG.CGT.Stroth77.Section228Uv321
public import CFSG.CGT.Stroth77.Section228Uv330
public import CFSG.CGT.Stroth77.Section228Uv331

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem isConj_uv_xyuv_of_not_five (h : F.IsD D dD)
    (hfive : ¬ ((∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
      (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n)) :
    IsConj F.dA.uv (F.dA.toConfig.x * F.dA.toConfig.y * F.dA.uv) := by
  cases τ with
  | t200 m => exact absurd (Or.inl ⟨m, rfl⟩) hfive
  | t201 m => exact absurd (Or.inr (Or.inl ⟨m, rfl⟩)) hfive
  | t100 m => exact absurd (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))) hfive
  | t101 s => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, rfl⟩)))) hfive
  | t300 n => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩)))) hfive
  | t110 t => exact t110_isConj_uv_xyuv h
  | t111 t => exact t111_isConj_uv_xyuv h
  | t120 m hm => exact t120_isConj_uv_xyuv hm h
  | t121 m hm => exact t121_isConj_uv_xyuv hm h
  | t130 m hm => exact t130_isConj_uv_xyuv (hm := hm) h
  | t131 m hm => exact t131_isConj_uv_xyuv hm h
  | t210 m hm => exact t210_isConj_uv_xyuv hm h
  | t211 m hm => exact t211_isConj_uv_xyuv (hm := hm) h
  | t220 s hs => exact t220_isConj_uv_xyuv (hs := hs) h
  | t221 s hs => exact t221_isConj_uv_xyuv (hs := hs) h
  | t230 s hs => exact t230_isConj_uv_xyuv (hs := hs) h
  | t231 s hs => exact t231_isConj_uv_xyuv (hs := hs) h
  | t310 m hm => exact t310_isConj_uv_xyuv hm h
  | t320 m hm => exact t320_isConj_uv_xyuv hm h
  | t330 m hm => exact t330_isConj_uv_xyuv hm h
  | t321 => exact t321_isConj_uv_xyuv h
  | t331 => exact t331_isConj_uv_xyuv h

theorem stroth_2_28_frame_unconditional (h : F.IsD D dD)
    (hnotall : ∃ x : G, x ∈ omegaIn 1 D ∧ orderOf x = 2 ∧
      ∃ y : G, y ∈ omegaIn 1 D ∧ orderOf y = 2 ∧ ∀ g : G, y ≠ g * x * g⁻¹) :
    (∃ m, τ = .t200 m) ∨ (∃ m, τ = .t201 m) ∨ (∃ m, τ = .t100 m) ∨
      (∃ s, τ = .t101 s) ∨ ∃ n, τ = .t300 n :=
  h.stroth_2_28_frame_of_huv hnotall (fun hfive => h.isConj_uv_xyuv_of_not_five hfive)

end StrothFrame.IsD

end CFSG.CGT.Stroth77
