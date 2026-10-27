module

public import CFSG.CGT.Stroth77.TypePredicates

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] {B C : Subgroup S} {τ τ' : StrothTypeIndex}

@[expose] def HasStrothTypeOver (D : StrothTypeData B τ) (C : Subgroup S)
    (τ' : StrothTypeIndex) : Prop :=
  ∃ D' : StrothTypeData C τ', D'.uv = D.uv ∧ D'.t = D.t ∧ D'.u = D.u ∧ D'.ρ = D.ρ

theorem HasStrothTypeOver.hasStrothType {D : StrothTypeData B τ}
    (h : HasStrothTypeOver D C τ') : HasStrothType C τ' := by
  obtain ⟨D', -⟩ := h
  exact ⟨D'⟩

theorem HasStrothTypeOver.of_gen_eq {B₁ B₂ : Subgroup S} {τ₁ τ₂ : StrothTypeIndex}
    {D₁ : StrothTypeData B₁ τ₁} {D₂ : StrothTypeData B₂ τ₂} (huv : D₁.uv = D₂.uv)
    (ht : D₁.t = D₂.t) (hu : D₁.u = D₂.u) (hρ : D₁.ρ = D₂.ρ)
    (h : HasStrothTypeOver D₁ C τ') : HasStrothTypeOver D₂ C τ' := by
  obtain ⟨D', h1, h2, h3, h4⟩ := h
  exact ⟨D', h1.trans huv, h2.trans ht, h3.trans hu, h4.trans hρ⟩

end CFSG.CGT.Stroth77
