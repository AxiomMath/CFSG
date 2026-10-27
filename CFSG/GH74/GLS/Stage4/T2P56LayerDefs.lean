module

public import CFSG.GH74.GLS.Stage4.T2P56bRed
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Lifted.Outer14
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Prop41
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.Closed2
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Defs
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Ext
public import CFSG.GH74.GLS.Stage4.RestP93
public import CFSG.GH74.GLS.Stage4.T2LeafC
public import CFSG.GH74.GLS.Stage4.T2LeafO
public import CFSG.GH74.GLS.Stage4.T2OddAut
public import CFSG.GH74.GLS.Stage4.T2P53
public import CFSG.GH74.GLS.Stage4.T6Defs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
public import CFSG.Walter.J1.Inv

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK

@[expose] def HasSDSylow (X : Type) [Group X] : Prop :=
  ∃ S : Sylow 2 X, ∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.SemidihedralGroup m)

@[expose] def HasWreathedSylow (X : Type) [Group X] : Prop :=
  ∃ S : Sylow 2 X, ∃ m : ℕ, 2 ≤ m ∧ Nonempty (↥(S : Subgroup X) ≃* CFSG.Open.WreathedTwoGroup m)

theorem hasSDOrWreathedSylow_iff {X : Type} [Group X] :
    HasSDOrWreathedSylow X ↔ HasSDSylow X ∨ HasWreathedSylow X := by
  constructor
  · rintro ⟨S, ⟨m, hm, h⟩ | ⟨m, hm, h⟩⟩
    · exact Or.inl ⟨S, m, hm, h⟩
    · exact Or.inr ⟨S, m, hm, h⟩
  · rintro (⟨S, m, hm, h⟩ | ⟨S, m, hm, h⟩)
    · exact ⟨S, Or.inl ⟨m, hm, h⟩⟩
    · exact ⟨S, Or.inr ⟨m, hm, h⟩⟩

@[expose] def SDWreathedLayer : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsKGroupNative X → pPrimeCore 2 X = ⊥ → HasSDOrWreathedSylow X →
    ∀ p n : ℕ, p.Prime → p ≠ 2 → 3 ≤ p ^ n → ∀ z : X, orderOf z = 2 →
      ∀ K : Subgroup X, z ∈ K → HasSL2Model ↥K (fun q => q = p ^ n) →
        (∀ c : X, c * z = z * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
          (∃ a : X, a * z * a⁻¹ ≠ z ∧ (a * z * a⁻¹) * z = z * (a * z * a⁻¹)) →
            ∃ E : Subgroup X, E.Normal ∧ K ≤ E ∧ Odd E.index ∧
              ((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 ↥E ε (p ^ n)) ∨
                (p ^ n = 3 ∧ Nonempty (↥E ≃* CFSG.Open.StatedM11)))

end CFSG.GH74.GLS.Stage4.Rest
