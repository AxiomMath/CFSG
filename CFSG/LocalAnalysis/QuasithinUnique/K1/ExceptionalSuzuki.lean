module

public import CFSG.Open.FusionDefs
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.QuasithinUnique.K1

open TauCeti

theorem fusionIsBenderGroup_of_mulEquiv_tcSuzuki {X : Type} [Group X] {m : ℕ}
    (hv : (LieTypeIndex.suzuki m).Valid)
    (e : X ≃* ValidLieTypeIndex.Group ⟨.suzuki m, hv⟩) : CFSG.Open.fusionIsBenderGroup X := by
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  have hmodel : CFSG.Theory.Comparator.SzModel m = CFSG.Open.Sz m := CFSG.Models.benderSzModel_eq_sz m
  let toSz : X ≃* CFSG.Open.Sz m :=
    (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
      ((MulEquiv.subgroupCongr (hmodel.symm.trans
        (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm)
  exact Or.inr (Or.inr ⟨m, hm, ⟨toSz⟩⟩)

end CFSG.QuasithinUnique.K1
