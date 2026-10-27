module

public import CFSG.CharacterTheory.Semidihedral.FourPointLifts
public import CFSG.CharacterTheory.Semidihedral.FourPointUniversal

public section

namespace CFSG.Semidihedral.FourPointCover

open Matrix

variable {H : Type*} [Group H] [Finite H]

theorem quaternion_four_point_central_cover_matrix_identification (z : H)
    (hz : z ∈ Subgroup.center H) (hord : orderOf z = 2)
    (pi : H →* Equiv.Perm (Fin 4)) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (hQ : Nonempty (FourPointLifts.fourKlein.comap pi ≃* QuaternionGroup 2))
    (hu : ∃ u : H, orderOf u = 2 ∧ (pi u).IsSwap) :
    ∃ theta : H ≃* GeneralLinearGroup (Fin 2) (ZMod 3),
      (theta z : Matrix (Fin 2) (Fin 2) (ZMod 3)) = -1 ∧
      (∀ x : H, (GeneralLinearGroup.det (theta x) : ZMod 3) = 1 ↔
        pi x ∈ alternatingGroup (Fin 4)) ∧
      ((alternatingGroup (Fin 4)).comap pi).map theta.toMonoidHom =
        (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker ∧
      ∃ e : (alternatingGroup (Fin 4)).comap pi ≃*
          (GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) (ZMod 3) →* (ZMod 3)ˣ).ker,
        ∀ x, (e x : GeneralLinearGroup (Fin 2) (ZMod 3)) = theta x := by
  obtain ⟨hcard, a, b, c, ha, hb, hc, hrel, _, hgen⟩ :=
    FourPointLifts.exists_normalized_relations z hz hord pi hpi hker hQ hu
  have hzpi : pi z = 1 :=
    MonoidHom.mem_ker.mp (hker.symm ▸ Subgroup.mem_zpowers z)
  obtain ⟨theta, _, _, _, htheta_z, hdet, hmap, e, he⟩ :=
    FourPointUniversal.exists_matrix_equiv_with_alternating hrel hgen hcard pi ha hb hc hzpi
  refine ⟨theta, ?_, hdet, hmap, e, he⟩
  rw [htheta_z]
  exact FourPointMatrices.Z_matrix

end CFSG.Semidihedral.FourPointCover
