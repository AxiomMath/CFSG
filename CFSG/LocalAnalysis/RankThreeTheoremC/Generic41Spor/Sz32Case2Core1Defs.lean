module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

structure Szh1Two {Y : Type} [Group Y] [Finite Y] (Pb : Subgroup Y) (L₁ L₂ : Subgroup Y) (t : Y) :
    Prop where
  comp₁ : IsComponentOf L₁ ⊤
  comp₂ : IsComponentOf L₂ ⊤
  ne : L₁ ≠ L₂
  cen₁ : Subgroup.center ↥L₁ = ⊥
  cen₂ : Subgroup.center ↥L₂ = ⊥
  all : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = L₁ ∨ L = L₂
  norm₁ : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L₁ : Set Y)
  norm₂ : ∀ g ∈ Pb, g ∈ Subgroup.normalizer (L₂ : Set Y)
  cent : Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup Y) : Set Y) = ⊥
  t_norm : t ∈ Subgroup.normalizer (Pb : Set Y)
  t₁ : L₁.map (MulAut.conj t).toMonoidHom = L₂
  t₂ : L₂.map (MulAut.conj t).toMonoidHom = L₁

structure Szh1Cyc {Y : Type} [Group Y] (Pb : Subgroup Y) (a c y : Y) (L₁ L₂ : Subgroup Y) : Prop where
  cyc₁ : ∃ g : Y, orderOf g = 25 ∧ Pb ⊓ L₁ = Subgroup.zpowers g
  cyc₂ : ∃ g : Y, orderOf g = 25 ∧ Pb ⊓ L₂ = Subgroup.zpowers g
  Q0 : sz32Q0 a c = (Pb ⊓ L₁) ⊔ (Pb ⊓ L₂)
  y_not : y ∉ L₁ ⊔ L₂

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
