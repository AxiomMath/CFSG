module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def transportAut {G H : Type*} [Group G] [Group H] (e : G ≃* H) (α : MulAut G) :
    MulAut H :=
  (e.symm.trans α).trans e

@[expose] def fixSubTransportEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) : ↥(fixSub α) ≃* ↥(fixSub (transportAut e α)) where
  toFun g := ⟨e g, by
    rw [mem_fixSub]
    simp only [transportAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [mem_fixSub.1 g.2]⟩
  invFun g := ⟨e.symm g, by
    rw [mem_fixSub]
    have := mem_fixSub.1 g.2
    simp only [transportAut, MulEquiv.trans_apply] at this
    apply e.injective
    rw [this, MulEquiv.apply_symm_apply]⟩
  left_inv g := Subtype.ext (e.symm_apply_apply _)
  right_inv g := Subtype.ext (e.apply_symm_apply _)
  map_mul' g h := Subtype.ext (map_mul e _ _)

theorem transportAut_mul_self {G H : Type*} [Group G] [Group H] (e : G ≃* H) {α : MulAut G}
    (h : α * α = 1) : transportAut e α * transportAut e α = 1 := by
  ext x
  have := congrArg (fun φ : MulAut G => φ (e.symm x)) h
  simp only [MulAut.mul_apply, MulAut.one_apply] at this
  simp [transportAut, this]

theorem transportAut_not_mem_inner {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {α : MulAut G} (h : α ∉ inner G) : transportAut e α ∉ inner H := by
  rintro ⟨y, hy⟩
  apply h
  refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
  have := congrArg (fun φ : MulAut H => e.symm (φ (e x))) hy
  simp only [transportAut, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at this
  simp only [MulAut.conj_apply, ← this, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem mem_inner_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hH : ∀ β : MulAut H, ∃ h : H, β = MulAut.conj h) (α : MulAut G) : α ∈ inner G := by
  by_contra hα
  obtain ⟨g, hg⟩ := hH (transportAut e α)
  exact transportAut_not_mem_inner e hα ⟨g, hg.symm⟩

end CFSG.ComponentClassification.RestrictedStd.Spor
