module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts
public import CFSG.GH74.GLS.C3.Prop121.Card7Gen
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.InvolutionCountingOrderFormula

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

structure Ctx (G : Type) [Group G] where
  x : G
  hx : orderOf x = 2
  ι : ↥(centralizer ({x} : Set G)) ≃* F7
  hιx : ι ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ = x0F
  y0 : G
  hy0 : orderOf y0 = 2
  hxy0 : ¬ IsConj x y0
  hcl : ∀ w : G, orderOf w = 2 → IsConj x w ∨ IsConj y0 w
  Ψ0 : ↥(centralizer ({y0} : Set G)) ≃* H11
  lab : ∀ c : ↥(centralizer ({x} : Set G)), orderOf c = 2 →
    (IsConj (c : G) x ↔ nm7 (ι c : Amb 7) = 4)
  s : G
  hs : s ∈ centralizer ({x} : Set G)
  hsF : ι ⟨s, hs⟩ = f0

namespace Ctx

variable {G : Type} [Group G] (C : Ctx G)

theorem s_comm_x : C.s * C.x = C.x * C.s := mem_centralizer_singleton_iff.1 C.hs

theorem s_pow_three : C.s ^ 3 = 1 := by
  have h1 : (⟨C.s, C.hs⟩ : ↥(centralizer ({C.x} : Set G))) ^ 3 = 1 := by
    apply C.ι.injective
    rw [map_pow, C.hsF, map_one]
    exact f0_pow_three
  have := congrArg Subtype.val h1
  simpa using this

theorem s_ne_one : C.s ≠ 1 := by
  intro h
  have h1 : (⟨C.s, C.hs⟩ : ↥(centralizer ({C.x} : Set G))) = 1 := Subtype.ext h
  have h2 := congrArg C.ι h1
  rw [C.hsF, map_one] at h2
  exact f0_ne_one h2

@[expose] def ιh (h : G) : ↥(centralizer ({h * C.x * h⁻¹} : Set G)) ≃* F7 :=
  (conjCentEquiv C.x h).trans C.ι

@[expose] def Ψh (h : G) : ↥(centralizer ({h * C.y0 * h⁻¹} : Set G)) ≃* H11 :=
  (conjCentEquiv C.y0 h).trans C.Ψ0

theorem lab_h (h : G) (c : ↥(centralizer ({h * C.x * h⁻¹} : Set G))) (hc : orderOf c = 2) :
    IsConj (c : G) (h * C.x * h⁻¹) ↔ nm7 (C.ιh h c : Amb 7) = 4 := by
  have hc' : orderOf (conjCentEquiv C.x h c) = 2 := by
    rw [MulEquiv.orderOf_eq]; exact hc
  have h0 := C.lab (conjCentEquiv C.x h c) hc'
  rw [conjCentEquiv_apply] at h0
  have e1 : IsConj (h⁻¹ * (c : G) * h) C.x ↔ IsConj (c : G) C.x := by
    have h2 := CFSG.ShultStronglyClosedTI.InvolutionCounting.isConj_conj_iff (a := C.x)
      (b := h⁻¹ * (c : G) * h) h
    have e : h * (h⁻¹ * (c : G) * h) * h⁻¹ = (c : G) := by group
    rw [e] at h2
    exact isConj_comm.trans (h2.symm.trans isConj_comm)
  have e2 : IsConj (c : G) (h * C.x * h⁻¹) ↔ IsConj (c : G) C.x :=
    CFSG.ShultStronglyClosedTI.InvolutionCounting.isConj_conj_iff h
  rw [e2, ← e1]
  exact h0

theorem exists_conj_x (hF : FFacts) (h : G) (hsw : C.s ∈ centralizer ({h * C.x * h⁻¹} : Set G))
    (h3 : Ty3 (C.ιh h ⟨C.s, hsw⟩)) :
    ∃ c : G, c * C.s = C.s * c ∧ c * C.x * c⁻¹ = h * C.x * h⁻¹ := by
  obtain ⟨k, hk⟩ := hF.conj3 _ h3
  refine exists_cent_conj (e := C.ι) (a := C.x) C.hs hsw k ?_
  rw [C.hsF]
  exact hk

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
