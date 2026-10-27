module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece

theorem natCCompProp : NatCCompProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hcore hcan hA j
  obtain ⟨t, ht, hj⟩ := hcan.surj j
  have h2 := hcan.ident t ht j hj
  have hlin : IsLin2Type (blockOf (⊤ : Subgroup G) R V ctx.hX (Lc j)) n := by
    rw [h2]
    exact IsLin2Type.map_of_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
      hcore.ad.lin
  exact mem_cComp_iff.1 (L238.mem_cComp_of_isChi0Block_nonsolvable (hA.chi0 j).1
    (Or.inl ⟨n, ctx.setting.two_le, hlin⟩))

end CFSG.QuasithinUnique.Setup.Lift
