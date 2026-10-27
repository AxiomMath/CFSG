module

public import CFSG.LargeExtraspecial.BridgeForms
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicFixed
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module CFSG.Open

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem nonempty_isometryGroup_equiv_statedSp {β : LinearMap.BilinForm (ZMod 2) V}
    (hβ : β.IsAlt) (hnd : β.Nondegenerate) (hdim : finrank (ZMod 2) V = 6) :
    Nonempty (TauCeti.BilinForm.isometryGroup β ≃* CFSG.Sporadic.Co2Smith.Sp62) := by
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hβ hnd
  obtain rfl : s = 3 := by omega
  have hmap : (CFSG.LocalAnalysis.ComponentInitial.sesqUnitaryGroup β).map
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom =
      TauCeti.BilinForm.isometryGroup β := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => hg x y
    · intro hf
      refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm f,
        fun x y => TauCeti.BilinForm.mem_isometryGroup_iff.mp hf x y, ?_⟩
      exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).apply_symm_apply f
  exact ⟨(Bridge.equivOfMapEq _ hmap).symm.trans e⟩

theorem nonempty_omegaGroup_equiv_omegaPlus {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : finrank (ZMod 2) V = 2 * m) (hm : 3 ≤ m)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    Nonempty (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ ≃* timmesfeldOmegaPlus m) := by
  obtain ⟨f⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ hdim hplus
  let F : V ≃ₗ[ZMod 2] (Fin m → ZMod 2) × (Fin m → ZMod 2) :=
    f.toLinearEquiv.trans (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin m) (ZMod 2) (ZMod 2))
  have hF : ∀ v, timmesfeldPlusForm m (F v) = Q v := fun v => by
    have h1 := f.map_app v
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply] at h1
    rw [← h1]
    rfl
  have hO : TauCeti.QuadraticMap.orthogonalGroup Q = timmesfeldIsometries (⇑Q) := by
    ext g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    rfl
  have hΩ := CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ
    (show 6 ≤ finrank (ZMod 2) V by omega)
  have hmap : (CFSG.RankThree.OrthogonalInvolutions.omegaGroup Q hQ).map
      (Bridge.conjLinearEquiv F).toMonoidHom = timmesfeldOmegaPlus m := by
    rw [← hΩ, Subgroup.map_commutator, hO, Bridge.isometries_map F hF]
    rfl
  exact ⟨Bridge.equivOfMapEq _ hmap⟩

end CFSG.LargeExtraspecial.S14
