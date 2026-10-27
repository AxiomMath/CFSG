module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoSemilinear

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.GorensteinWalter (PSL2 PGL2 IsOddPrimePower)

theorem sec5sh8_pgl_layer {X : Type} [Group X] {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (e : X ≃* PGL2 F) :
    ∃ J : Subgroup X, J.Normal ∧ J.index = 2 ∧ Subgroup.centralizer (J : Set X) = ⊥ ∧
      Nonempty (J ≃* PSL2 F) := by
  let H : Subgroup (PGL2 F) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hHnormal : H.Normal :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglPSLRange_normal F
  have hmap : (H.comap e.toMonoidHom).map e.toMonoidHom = H :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective H
  let eJ : H.comap e.toMonoidHom ≃* H :=
    (Subgroup.equivMapOfInjective (H.comap e.toMonoidHom) e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨H.comap e.toMonoidHom, hHnormal.comap e.toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.index_comap_of_surjective H e.surjective]
    exact CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF
  · apply le_bot_iff.mp
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : e x ∈ Subgroup.centralizer (H : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro h hh
      let j : X := e.symm h
      have hj : j ∈ H.comap e.toMonoidHom := by
        change e j ∈ H
        simpa [j] using hh
      have hcomm := hx j hj
      simpa [j] using congrArg (⇑e) hcomm
    have hx1 : e x = 1 := by
      have hxbot := hx'
      rw [CFSG.GorensteinWalter.pgl2_psl2Range_centralizer_eq_bot F hF] at hxbot
      simpa using hxbot
    exact e.injective (by rw [hx1, map_one])
  · exact ⟨eJ.trans (CFSG.GorensteinWalter.psl2EquivToPGLRange F).symm⟩

end CFSG.OddStandard.SmallF3.Omega
