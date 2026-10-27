module

public import CFSG.ClassicalInvolution.Q3.TA3SmallConcrete
public import CFSG.GH74.Generic.S45.LEvSporM12Spec

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint


theorem smallSimpleLeaf_of_exactModel {M : Type} [Group M] {P R : Subgroup M}
    (hA : Sporadic.SmallOddCore.AutModel P R) {Pr : ∀ (F : Type) [Group F], Prop}
    (hshape : ∀ (F : Type) [Group F], Pr F → Nonempty (F ≃* P)) (hC : ConcreteLeaf M P R) :
    SmallSimpleLeaf Pr := by
  intro Y _ _ _ hY hnab hG hF R' S t hd hc hE2
  obtain ⟨θ⟩ := hshape _ hF
  have := genFittingFStar_normal Y
  have hinj := hA.embed_injective (genFittingFStar Y) θ
    (Nobq.centralizer_genFittingFStar_eq_bot hnab)
  refine tightExOrGood_of_map_equiv (MonoidHom.ofInjective hinj) hd hc hE2
    fun S' hd' hc' hE2' => hC _ ?_ ?_ _ S' _ hd' hc' hE2'
  · intro p hp
    refine ⟨((θ.symm ⟨p, hp⟩ : ↥(genFittingFStar Y)) : Y), ?_⟩
    rw [hA.embed_coe (genFittingFStar Y) θ (θ.symm ⟨p, hp⟩), MulEquiv.apply_symm_apply]
  · rintro _ ⟨y, rfl⟩
    exact hA.embed_mem _ θ y

theorem smallSimpleLeaf_m12
    (hC : ConcreteLeaf (Equiv.Perm (Fin 24)) ComponentClassification.M12Cover.blockGroup
      ComponentClassification.M12Cover.autModel) : SmallSimpleLeaf SmallM12 :=
  smallSimpleLeaf_of_exactModel GH74.Generic.S45.EvSpor.m12_smallAutModel
    (fun _ _ ⟨e⟩ => ⟨e.trans Sporadic.Schreier.m12EquivD⟩) hC

end CFSG.ClassicalInvolution.Q3.TA3
