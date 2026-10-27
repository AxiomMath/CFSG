module

public import CFSG.ClassicalInvolution.Asc77.AscR10E6
public import CFSG.ClassicalInvolution.Asc77.AscR10E7
public import CFSG.ClassicalInvolution.Asc77.AscR10E11
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthE7
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.Asc77.TwinLookup
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.Balance.BootNoTripleStrong
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SSec
public import CFSG.ClassicalInvolution.Models.TwistedPairs
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8
public import CFSG.ClassicalInvolution.RouteD.G2D4Ih8G2
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Walter.J1
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.ClassicalInvolution.Asc77.T3CII (ne_two_of_pow_eq_three neZero_of_pow_eq_three
  StdDich3)



section Main

variable {p e : ℕ} [Fact p.Prime]

theorem orthBranch_e7_three (hadm : StatedLieAdmissible .E7 0 p e) : OrthBranch3 p .E7 0 e := by
  intro h3
  have hp2 := ne_two_of_pow_eq_three h3
  have : NeZero e := neZero_of_pow_eq_three h3
  have hlong := isLongestRoot_single .E7 0 p e Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E7 0 p e Fact.out).D thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p e)).2
        isRoot_thetaE7)
  refine (orthBranch_of_adjointEmbedding3 (t := .E7) h3 trivial (by decide) (by decide) hadm
    (excEmbed .E7 p e) (fun x => (e7Isogeny (GaloisField p e) x).2) ?_ ?_ (excSignGroup .E7 p e)
    (fun c hc => mem_excSignGroup.1 hc) (pairFrame_e7 hp2 hadm)
    (fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide))
    (Rθ := stdRankOne (Generic.modelUniv .E7 0 p e Fact.out).D thetaE7)
    ⟨1, thetaE7, Or.inl hθ, (Generic.conjSub_one _).symm⟩
    (isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) isRoot_thetaE7)
    map_stdRankOne_excEmbed_e7
    fun _ γ hγ _ => isLongRoot_of_isRoot_of_simplyLaced (Or.inr (Or.inl rfl)) hγ.1) h3
  · intro x hx
    have h1 : ((e7Isogeny (GaloisField p e) x : ↥(adjointGroup .E7 (GaloisField p e))) :
        ModGL .E7 (GaloisField p e)) = 1 := MonoidHom.mem_ker.1 hx
    exact (ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField p e))
      (exists_e7Isogeny_ne_one (GaloisField p e))) (MonoidHom.mem_ker.2 (Subtype.ext h1))
  · intro x hx
    have h1 : e7Isogeny (GaloisField p e) x = 1 := Subtype.ext hx
    exact e7Isogeny_ker_sq x (MonoidHom.mem_ker.2 h1)

theorem a2BranchLeft_e7_three (hadm : StatedLieAdmissible .E7 0 p e) :
    A2BranchLeft3 p .E7 0 e :=
  fun h3 _ h₁ _ h₂ _ _ hc₁ hc₂ ho₁ ho₂ hcomm hn =>
    Levi.a2BranchLeft_e7_aux_three hadm Levi.a2UnitaryE7_three (ne_two_of_pow_eq_three h3) h3
      h₁ h₂ hc₁ hc₂ ho₁ ho₂ hcomm hn

theorem stdDich3Gen_e7 (hadm : StatedLieAdmissible .E7 0 p e) : StdDich3Gen p .E7 0 e :=
  stdDich3Gen_of_branches (orthBranch_e7_three hadm) (a2BranchLeft_e7_three hadm).a2Branch3

theorem stdDich3_e7 (hadm : StatedLieAdmissible .E7 0 3 1) : StdDich3 .E7 0 :=
  stdDich3_of_gen (stdDich3Gen_e7 hadm)

end Main

end CFSG.ClassicalInvolution.ModelFacts
