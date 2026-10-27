module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs6

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
open CFSG.ShultStronglyClosedTI.InvolutionCounting

namespace Ctx

variable {G : Type} [Group G] [Finite G] {C : Ctx G}

@[expose] def xG (C : Ctx G) : ↥(centralizer ({C.s} : Set G)) := ⟨C.x, x_mem_gamma⟩

@[expose] def Y1.yG (Y : C.Y1) : ↥(centralizer ({C.s} : Set G)) :=
  ⟨Y.y1, mem_centralizer_singleton_iff.2 Y.y1_comm_s⟩

omit [Finite G] in
theorem isConj_gamma_iff {a b : ↥(centralizer ({C.s} : Set G))} :
    IsConj a b ↔ ∃ c : G, c * C.s = C.s * c ∧ c * (a : G) * c⁻¹ = (b : G) := by
  rw [isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.1, mem_centralizer_singleton_iff.1 c.2, congrArg Subtype.val hc⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨⟨c, mem_centralizer_singleton_iff.2 hc⟩, Subtype.ext h⟩

theorem isConj_xG_iff (hF : FFacts) (hH : HFacts) (Y : C.Y1) (b : ↥(centralizer ({C.s} : Set G))) :
    IsConj C.xG b ↔ (b : G) ∈ C.Acl := by
  rw [isConj_gamma_iff, ← mem_Acl_iff hF hH Y]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, mem_centralizer_singleton_iff.2 hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, mem_centralizer_singleton_iff.1 hc, h⟩

theorem isConj_yG_iff (hF : FFacts) (hH : HFacts) (Y : C.Y1) (b : ↥(centralizer ({C.s} : Set G))) :
    IsConj Y.yG b ↔ (b : G) ∈ C.Bcl := by
  rw [isConj_gamma_iff, ← mem_Bcl_iff hF hH Y]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨c, mem_centralizer_singleton_iff.2 hc, h⟩
  · rintro ⟨c, hc, h⟩
    exact ⟨c, mem_centralizer_singleton_iff.1 hc, h⟩

omit [Finite G] in
theorem orderOf_xG : orderOf C.xG = 2 := by
  rw [← Subgroup.orderOf_coe]; exact C.hx

omit [Finite G] in
theorem orderOf_yG (Y : C.Y1) : orderOf Y.yG = 2 := by
  rw [← Subgroup.orderOf_coe]; exact Y.orderOf_y1

theorem not_isConj_xG_yG (hF : FFacts) (hH : HFacts) (Y : C.Y1) : ¬ IsConj C.xG Y.yG := by
  intro h
  have := (isConj_xG_iff hF hH Y Y.yG).1 h
  exact Y.not_isConj_x this.2.2

theorem hcl_gamma (hF : FFacts) (hH : HFacts) (Y : C.Y1) (w : ↥(centralizer ({C.s} : Set G)))
    (hw : orderOf w = 2) : IsConj C.xG w ∨ IsConj Y.yG w := by
  have hw' : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hws : (w : G) * C.s = C.s * (w : G) := mem_centralizer_singleton_iff.1 w.2
  by_cases hx : IsConj C.x (w : G)
  · exact Or.inl ((isConj_xG_iff hF hH Y w).2 ⟨hws, hw', hx⟩)
  · exact Or.inr ((isConj_yG_iff hF hH Y w).2 ⟨hws, hw', hx⟩)

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
