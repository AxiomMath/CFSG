module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransferHyp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceBlockTransferOut

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

theorem natural_canonical_of_top (hTop : NaturalCanonicalLin2BlocksTop) :
    NaturalCanonicalLin2Blocks := by
  intro G _ _ X R M V n F _ hS hchar hnoc hle r Lc hLc
  have hVX : V ≤ X := hS.reduced.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hS.reduced.2.1
  have hRX : R ≤ X := hS.sylow.1
  exact evenSL2BlockOutput_of_top hS
    (hTop ↥X (R.subgroupOf X) (M.subgroupOf X) (V.subgroupOf X) n F (evenSL2Setting_top hS)
      (charTwo_top hchar) (noChar_top hRX hnoc) ((autOn_le_top_iff hVX hX hRX).2 hle) r
      (fun i => (Lc i).map (autEmbed hVX).toMonoidHom) (isCompList_top hVX hX hLc))

theorem deleted_canonical_of_top (hTop : DeletedCanonicalAlt5BlocksTop) :
    DeletedCanonicalAlt5Blocks := by
  intro G _ _ X R M V n F _ hS hchar hnoc hn hnle r Lc hLc
  have hVX : V ≤ X := hS.reduced.1
  have hX : X ≤ Subgroup.normalizer (V : Set G) := hS.reduced.2.1
  have hRX : R ≤ X := hS.sylow.1
  exact evenSL2BlockOutput_of_top hS
    (hTop ↥X (R.subgroupOf X) (M.subgroupOf X) (V.subgroupOf X) n F (evenSL2Setting_top hS)
      (charTwo_top hchar) (noChar_top hRX hnoc) hn
      (fun h => hnle ((autOn_le_top_iff hVX hX hRX).1 h)) r
      (fun i => (Lc i).map (autEmbed hVX).toMonoidHom) (isCompList_top hVX hX hLc))

theorem blockTransferProp : BlockTransferProp :=
  ⟨natural_canonical_of_top, deleted_canonical_of_top⟩

end CFSG.QuasithinUnique.Setup.Lift
