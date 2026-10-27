module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7SecBLin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp

public section

namespace CFSG.QuasithinUnique.Setup.X7Sec

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Family CFSG.Assembly.LowTwoRank

theorem actualSymplecticFourData : X7b.ActualSymplecticFourData := by
  intro V _ _ H T M E hFF hns L hL f K iK iKfin iKch hf hKcard θ
  classical
  obtain ⟨W, _, _, _, ⟨θv⟩⟩ := Layer.Actor.exists_binModel_of_binary hFF.elementary
  obtain ⟨ho2, hsyl, hnn, hmax, hE⟩ := Layer.Actor.map_hypotheses θv hFF.o2_trivial hFF.sylow
    hFF.not_normal hFF.max hFF.offender
  have hns' : ¬ Group.IsSolvable ↥(H.map (binPsi θv).toMonoidHom) := fun h =>
    hns ((solvable_map_mulEquiv_iff (binPsi θv)).1 h)
  have hL' : IsComponentIn (L.map (binPsi θv).toMonoidHom) (H.map (binPsi θv).toMonoidHom) :=
    (Layer.Actor.isComponentIn_map_iff (binPsi θv)).2 ((Layer.Actor.isComp_iff L H).1 hL)
  let eψ : ↥L ≃* ↥(L.map (binPsi θv).toMonoidHom) :=
    L.equivMapOfInjective (binPsi θv).toMonoidHom (binPsi θv).injective
  have hZL : Subgroup.center ↥L = ⊥ := CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv θ
  have hZ : Subgroup.center ↥(L.map (binPsi θv).toMonoidHom) = ⊥ := by
    have := Subgroup.map_center_eq eψ
    rw [hZL, Subgroup.map_bot] at this
    exact this.symm
  exact data_linear hns' ho2 hsyl hnn hmax.1 hmax.2.1 hmax.2.2 hE.1 hE.2.1 hE.2.2.1 hE.2.2.2 hL'
    (eψ.symm.trans θ) hZ

end CFSG.QuasithinUnique.Setup.X7Sec
