module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Good
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux3
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers
public import Certificates.Certificate43

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

variable {k : Type} [Field k]

theorem mem_c25Fix_zpowers_iff {Y : Type*} [Group Y] (x : MulAut Y) (y : Y) :
    y ∈ c25Fix (Subgroup.zpowers x) ↔ x y = y := by
  have : y ∈ c25Fix (Subgroup.zpowers x) ↔ Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut Y) y := by
    constructor
    · intro h α hα
      exact (MulAction.mem_stabilizer_iff).2 (h α hα)
    · intro h α hα
      exact (MulAction.mem_stabilizer_iff).1 (h hα)
  rw [this, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
  rfl

theorem conjAut_proj_eq_of_comm (B : GL (Fin 3) k) (g : SpecialLinearGroup (Fin 3) k)
    (h : (B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (g : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)) :
    conjAut' 3 k B (proj 3 k g) = proj 3 k g := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, h, Matrix.mul_assoc]
  have : (B : Matrix (Fin 3) (Fin 3) k) * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [this, Matrix.mul_one]

theorem aux_smul_comm {B Bi G : Matrix (Fin 3) (Fin 3) k} (hBB : Bi * B = 1) (c : k)
    (hg : G = c • (B * G * Bi)) : G * B = c • (B * G) := by
  calc G * B = (c • (B * G * Bi)) * B := by conv_lhs => rw [hg]
    _ = c • (B * G * (Bi * B)) := by rw [Matrix.smul_mul, Matrix.mul_assoc _ Bi B]
    _ = c • (B * G) := by rw [hBB, Matrix.mul_one]

theorem exists_smul_of_conjAut_fix (B : GL (Fin 3) k) (g : SpecialLinearGroup (Fin 3) k)
    (h : conjAut' 3 k B (proj 3 k g) = proj 3 k g) :
    ∃ c : kˣ, (B : Matrix (Fin 3) (Fin 3) k) * (g : Matrix (Fin 3) (Fin 3) k) =
      (c : k) • ((g : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k)) := by
  rw [conjAut_proj, proj_eq_proj_iff] at h
  obtain ⟨c, -, hc⟩ := mem_scalars.1 h
  set T := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k B g with hT
  have hTm : (T : Matrix (Fin 3) (Fin 3) k) = (B : Matrix (Fin 3) (Fin 3) k) *
      (g : Matrix (Fin 3) (Fin 3) k) * ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) :=
    coe_slConjugation B g
  have hg : (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • (T : Matrix (Fin 3) (Fin 3) k) := by
    have h1 : (g : Matrix (Fin 3) (Fin 3) k) =
        (T : Matrix (Fin 3) (Fin 3) k) * ((T⁻¹ * g : SpecialLinearGroup (Fin 3) k) :
          Matrix (Fin 3) (Fin 3) k) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [h1, hc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have hBB : ((B⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) * (B : Matrix (Fin 3) (Fin 3) k) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 := aux_smul_comm hBB (c : k) (hTm ▸ hg)
  refine ⟨c⁻¹, ?_⟩
  rw [h3, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
