module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410FusKX

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

theorem fz410x_fz410_fusk_normalizes_of_le {G : Type} [Group G] [Finite G] {Z : Subgroup G}
    {k : G} (h : Z.map (MulAut.conj k⁻¹).toMonoidHom ≤ Z) :
    ∀ z : G, k * z * k⁻¹ ∈ Z ↔ z ∈ Z := by
  have hZkay_eq_Z : Z.map (MulAut.conj k⁻¹).toMonoidHom = Z := by
    refine Subgroup.eq_of_le_of_card_ge h ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]
  have hZkay_eq_Z' : Z.map (MulAut.conj k).toMonoidHom = Z := by
    have h' := congrArg (fun X : Subgroup G => X.map (MulAut.conj k).toMonoidHom) hZkay_eq_Z
    rw [Subgroup.map_map] at h'
    have hcomp : (MulAut.conj k).toMonoidHom.comp (MulAut.conj k⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext u
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]
      group
    rw [hcomp, Subgroup.map_id] at h'
    exact h'.symm
  intro z
  constructor
  · intro hz
    have hmem : (MulAut.conj k⁻¹).toMonoidHom (k * z * k⁻¹) ∈ Z.map (MulAut.conj k⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    have hz' : z ∈ Z.map (MulAut.conj k⁻¹).toMonoidHom := by
      rwa [show (MulAut.conj k⁻¹).toMonoidHom (k * z * k⁻¹) = z by
        rw [fz410x_fz410_fusk_conj_apply]; group] at hmem
    rwa [hZkay_eq_Z] at hz'
  · intro hz
    have hmem : (MulAut.conj k).toMonoidHom z ∈ Z.map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hz
    rw [hZkay_eq_Z'] at hmem
    simpa [MulAut.conj_apply] using hmem

end CFSG.OddStandard.SmallF3.FritzII
