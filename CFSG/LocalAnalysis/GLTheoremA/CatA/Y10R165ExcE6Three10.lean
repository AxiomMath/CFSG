module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.TwE6Step3.SylowTorusSix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.ExcHighThree.E6InF4Sylow
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThree
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.RankThree.PartOne.KE6.E6LData
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Steinberg.Isogeny
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus adjEmb adjEmb_injective
  adjEmb_mem adjEmb_frobenius sigma_embedding_data subtorusImage mem_subtorusImage_iff
  twistedTorusOf mem_twistedTorusOf twistedFixedPoints mem_twistedFixedPoints subtorusSigma)
open CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit
  rootSpan_torusRootKernel_le_centralizer rootChar_neg')
open CFSG.HardMathSupport.Lang.TwE6Step3
open CFSG.RankThree.Lattice (e6T3W)
open scoped Matrix MatrixGroups Pointwise

theorem commute_of_psi_commute {F : Type} [Field F] [Algebra F (AlgebraicClosure F)]
    {x c : adjointGroup Tag.E6 F} {g0 : ModGL Tag.E6 (AlgebraicClosure F)}
    {ψ : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F)) →*
      ModGL Tag.E6 (AlgebraicClosure F)}
    (hψ : ∀ y, ψ y = g0⁻¹ * adjEmb Tag.E6 F (AlgebraicClosure F)
      (c * (y : Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F))) * c⁻¹) * g0)
    {a b : adjointGroup Tag.E6 F}
    {ha : a ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F))}
    {hb : b ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 F))}
    (h : Commute (ψ ⟨a, ha⟩) (ψ ⟨b, hb⟩)) : Commute a b := by
  have h2 : Commute (g0 * ψ ⟨a, ha⟩ * g0⁻¹) (g0 * ψ ⟨b, hb⟩ * g0⁻¹) := by
    have h2' : (g0 * ψ ⟨a, ha⟩ * g0⁻¹) * (g0 * ψ ⟨b, hb⟩ * g0⁻¹) =
        (g0 * ψ ⟨b, hb⟩ * g0⁻¹) * (g0 * ψ ⟨a, ha⟩ * g0⁻¹) := by
      calc (g0 * ψ ⟨a, ha⟩ * g0⁻¹) * (g0 * ψ ⟨b, hb⟩ * g0⁻¹)
          = g0 * (ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩) * g0⁻¹ := by group
        _ = g0 * (ψ ⟨b, hb⟩ * ψ ⟨a, ha⟩) * g0⁻¹ := by rw [h.eq]
        _ = (g0 * ψ ⟨b, hb⟩ * g0⁻¹) * (g0 * ψ ⟨a, ha⟩ * g0⁻¹) := by group
    exact h2'
  rw [hψ ⟨a, ha⟩, hψ ⟨b, hb⟩] at h2
  have h3 : Commute (adjEmb Tag.E6 F (AlgebraicClosure F) (c * a * c⁻¹))
      (adjEmb Tag.E6 F (AlgebraicClosure F) (c * b * c⁻¹)) := by
    simpa [mul_assoc] using h2
  have h4 : Commute (c * a * c⁻¹) (c * b * c⁻¹) := by
    apply adjEmb_injective (K := F) (L := AlgebraicClosure F)
    simpa only [map_mul] using h3.eq
  have h5 : a * b = b * a := by
    have h := congrArg (fun z => c⁻¹ * z * c) h4.eq
    simpa [mul_assoc] using h
  exact h5

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Three
