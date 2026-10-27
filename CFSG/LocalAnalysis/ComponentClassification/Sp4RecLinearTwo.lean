module

public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport

public noncomputable section

namespace CFSG.ComponentClassification.Sp4Rec

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem PairConfig.false_of_solvable {M : Type*} [Group M] [Finite M] {x : M}
    {K K' : Subgroup M} (hc : PairConfig M x K K')
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set M))) : False :=
  CatalogueBLinearTwoInvolution.no_pComponent_of_solvable 2 _ hc.isPComponent_K

theorem PairConfig.false_of_embedding {M Y : Type*} [Group M] [Finite M] [Group Y] {x : M}
    {K K' : Subgroup M} (hc : PairConfig M x K K') (φ : M →* Y) (hφ : Function.Injective φ)
    (hs : Group.IsSolvable ↥(centralizer ({φ x} : Set Y))) : False := by
  refine hc.false_of_solvable ?_
  let ψ : ↥(centralizer ({x} : Set M)) →* ↥(centralizer ({φ x} : Set Y)) :=
    { toFun := fun g => ⟨φ (g : M), by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          mem_centralizer_singleton_iff.mp g.2]⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun g h => Subtype.ext (map_mul φ (g : M) (h : M)) }
  exact Group.isSolvable_of_isSolvable_injective (f := ψ) fun g h hgh =>
    Subtype.ext (hφ (congrArg Subtype.val hgh))

theorem pairConfig_psl_two_false {F : Type} [Field F] [Finite F]
    {x : StatedProj (StatedSL 2 F)} {K K' : Subgroup (StatedProj (StatedSL 2 F))}
    (hc : PairConfig _ x K K') : False := by
  set φ : StatedProj (StatedSL 2 F) →* Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL.comp
      (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.toMonoidHom with hφ
  have hφi : Function.Injective φ :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp
      (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.injective
  have hx1 : φ x ≠ 1 := by
    intro h
    have h1 : x = 1 := hφi (h.trans (map_one φ).symm)
    have := hc.orderOf_x
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hxx := pow_orderOf_eq_one x
  rw [hc.orderOf_x] at hxx
  have hx2 : φ x ^ 2 = 1 := by rw [← map_pow, hxx, map_one]
  exact hc.false_of_embedding φ hφi
    (CatalogueBLinearTwo.pgl_involution_centralizer_structure (φ x) hx1 hx2).2.2

namespace Config

variable {H : Type} [Group H] [Finite H] (c : Sp4Rec.Config H)

include c in
theorem false_of_psl_two {p f : ℕ}
    (hG : StatedClassicalModel ↥(generalizedFitting H) .PSL 2 p f) : False := by
  obtain ⟨-, F, _, _, -, ⟨φ⟩⟩ := hG
  have : Finite (StatedProj (StatedSL 2 F)) := Finite.of_equiv _ φ.toEquiv
  exact pairConfig_psl_two_false (c.pairConfig φ)

end Config

end CFSG.ComponentClassification.Sp4Rec
