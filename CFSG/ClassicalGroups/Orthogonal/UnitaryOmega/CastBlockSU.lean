module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Defs
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.Certificates.CosetTableShort
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType
open CFSG.GH74.Generic.S1.SymBlocksUni

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem map_uniCast_blockSU_le (h : UnitaryFieldData 2 f K) {m : ℕ} (S : Finset (Fin m)) :
    (TableBUE.blockSU (K := K) (n := f) S).map (uniCast h m) ≤
      TableBUE.blockSU (K := K) (n := f) (S.map Fin.castSuccEmb) := by
  rintro _ ⟨g, hg, rfl⟩
  rw [TableBUE.mem_blockSU]
  have hmat : (((uniCast h m g : unitarySU 2 f K (m + 1)) : GL (Fin (m + 1)) K) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
      blkMat Fin.castSucc (((g : GL (Fin m) K)) : Matrix (Fin m) (Fin m) K) := by
    simp only [uniCast, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, suEquiv,
      MulEquiv.subgroupCongr_apply, MulEquiv.subgroupCongr_symm_apply, coe_coe_blkEmb]
  rw [hmat]
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
    · have hab : a ∉ S ∨ b ∉ S :=
        hij.imp (fun h' ha => h' (Finset.mem_map_of_mem Fin.castSuccEmb ha))
          (fun h' hb => h' (Finset.mem_map_of_mem Fin.castSuccEmb hb))
      rw [blkMat_apply_ι (Fin.castSucc_injective m), TableBUE.mem_blockSU.mp hg a b hab]
      simp [Matrix.one_apply]
    · exact blkMat_apply_of_not_mem_right _ _ fun y => (Fin.castSucc_lt_last y).ne'
  · exact blkMat_apply_of_not_mem_left _ (fun x => (Fin.castSucc_lt_last x).ne') _

theorem range_comp_uniCast_le_of_iSup_blockSU {G : Type} [Group G] (h : UnitaryFieldData 2 f K)
    {m k : ℕ} (σ : ↥(unitarySU 2 f K (m + 1)) →* G)
    (hgen : (⨆ (S : Finset (Fin m)) (_ : S.card = k), TableBUE.blockSU (K := K) (n := f) S) = ⊤)
    {M : Subgroup G}
    (hM : ∀ S : Finset (Fin m), S.card = k →
      (TableBUE.blockSU (K := K) (n := f) (S.map Fin.castSuccEmb)).map σ ≤ M) :
    (σ.comp (uniCast h m)).range ≤ M := by
  rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun S hS => ?_
  rw [← Subgroup.map_le_iff_le_comap, ← Subgroup.map_map]
  exact (Subgroup.map_mono (map_uniCast_blockSU_le h S)).trans (hM S hS)

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
