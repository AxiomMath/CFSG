module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.GH74.Generic.BProg.B2.GenLoc4Defs
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup

namespace GenLocBasic

section Iso4

variable {J J' : Type} [Group J] [Group J'] {A : Type} [Group A]

theorem map_congr_inn (e : J ≃* J') :
    (MulAut.conj : J →* MulAut J).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : J' →* MulAut J').range := by
  ext φ
  constructor
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    refine ⟨e g, ?_⟩
    ext y
    simp [MulAut.congr_apply]
  · rintro ⟨g, rfl⟩
    refine ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, ?_⟩
    ext y
    simp [MulAut.congr_apply]

theorem innJoin_map_congr (e : J ≃* J') (α : A →* MulAut J) (α' : A →* MulAut J')
    (hc : ∀ a x, α' a (e x) = e (α a x)) :
    innJoin α' = (innJoin α).map (MulAut.congr e).toMonoidHom := by
  unfold innJoin
  rw [Subgroup.map_sup, map_congr_inn]
  congr 1
  ext φ
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨α a, ⟨a, rfl⟩, ?_⟩
    ext y
    simp [MulAut.congr_apply, ← hc]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    ext y
    simp [MulAut.congr_apply, ← hc]

end Iso4

end GenLocBasic

section Iso4

variable {J : Type} [Group J]

theorem GenLoc4.of_mulEquiv {J' : Type} [Group J'] (e : J ≃* J') (h : GenLoc4 J) : GenLoc4 J' := by
  intro A _ _ α' hA hSec
  let α : A →* MulAut J := (MulAut.congr e.symm).toMonoidHom.comp α'
  have hc : ∀ a x, α' a (e x) = e (α a x) := by
    intro a x
    simp [α, MulAut.congr_apply]
  have hSec' : SectionalTwoRankLE ↥(innJoin α) 4 := by
    have heq := GenLocBasic.innJoin_map_congr e α α' hc
    have iso := (innJoin α).equivMapOfInjective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
    exact SectionalTwoRankLE.of_mulEquiv ((MulEquiv.subgroupCongr heq).trans iso.symm) hSec
  rcases h A α hA hSec' with hg | ⟨h1, h2, h3⟩
  · left
    rw [GenLocBasic.gammaAct_map_equiv e α α' hc, hg, Subgroup.map_top_of_surjective _ e.surjective]
  · right
    exact ⟨(GenLocBasic.locE1_map_equiv e α α' hc).2 h1, (GenLocBasic.locE2_map_equiv e α α' hc).2 h2,
      (GenLocBasic.locE3_map_equiv e α α' hc).2 h3⟩

end Iso4

end CFSG.GH74.Generic.BProg.B2
