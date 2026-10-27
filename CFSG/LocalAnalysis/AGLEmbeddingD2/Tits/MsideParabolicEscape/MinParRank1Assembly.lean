module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParOneNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParModel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParC4

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin
  CFSG.Open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

theorem kFact_of_oneNode {Y : Type} [Group Y] [Finite Y] {L R P : Subgroup Y}
    (hL : Open.IsQuasisimple ↥L) (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (hOne : OneNode (↥L ⧸ Subgroup.center ↥L)
      (((R ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)))) :
    (∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M) ∧
      (conjClosure P R ≠ L →
        ⁅pCoreOf 2 (twoResidual (pElementSubgroup 2 (conjClosure P R))),
          twoResidual (pElementSubgroup 2 (conjClosure P R))⁆ ≠ ⊥) := by
  let D0 := minParData_of_oneNode hL.2 hOne
  let DW := minParData_of_center D0 hS
  refine ⟨minParabolic_of_minParData hR hR2 hS hP DW, fun hne => ?_⟩
  exfalso
  apply hne
  obtain ⟨J, hJne, hQ⟩ := exists_iSup_conjClosure hR hP DW
  rw [hQ]
  have hPk : ∀ k, DW.P k = L := fun k => by
    show (((⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L))).comap
      (QuotientGroup.mk' (Subgroup.center ↥L))).map L.subtype = L
    rw [Subgroup.comap_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨j, hj⟩ := hJne
  refine le_antisymm (iSup₂_le fun k _ => (hPk k).le) ?_
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ J) => DW.P k) j hj (hPk j).ge

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
