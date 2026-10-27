module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {S : Type*} [Group S]

theorem perfectInLayer_of_perfectResidual (β : MulAut S) [Finite ↥(fixSubgroup β)]
    (h : CFSG.perfectResidual ↥(fixSubgroup β) = ⊥ ∨
      CFSG.IsQuasisimple ↥(CFSG.perfectResidual ↥(fixSubgroup β))) : PerfectInLayer β := by
  rcases h with h | h
  · exact perfectInLayer_of_isSolvable_fixSubgroup β
      ((CFSG.perfect_residual_characterization (G := ↥(fixSubgroup β))).2.2.2.2.2.mp h)
  · set C := fixSubgroup β with hC
    set R : Subgroup ↥C := CFSG.perfectResidual ↥C with hR
    set J : Subgroup S := R.map C.subtype with hJ
    have hJC : J ≤ C := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hJR : J.subgroupOf C = R :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective R
    haveI : (J.subgroupOf C).Normal := by
      rw [hJR]
      infer_instance
    let e : ↥R ≃* ↥J := R.equivMapOfInjective C.subtype C.subtype_injective
    have hJq : CFSG.IsQuasisimple ↥J := CFSG.IsQuasisimple.of_mulEquiv e.symm h
    have hsol : Group.IsSolvable (↥C ⧸ J.subgroupOf C) := by
      have hs := (CFSG.perfect_residual_characterization (G := ↥C)).2.2.2.1
      let q : ↥C ⧸ R ≃* ↥C ⧸ J.subgroupOf C := QuotientGroup.quotientMulEquivOfEq hJR.symm
      exact Group.isSolvable_of_surjective (f := q.toMonoidHom) q.surjective
    exact perfectInLayer_of_normal_quasisimple hJC hJq hsol

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
