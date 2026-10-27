module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Center
public import CFSG.ClassicalInvolution.Q3.Q3WSimply
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.Assembly.LowTwoRank CFSG.Timmesfeld
  CFSG.ClassicalInvolution.ModelFacts.D4Rigid CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.LieType.HighestRoot CFSG.ClassicalInvolution.G2D4Models.Twin
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

theorem exists_triality3 (hadm : StatedLieAdmissible .POmegaPlus 4 3 1) :
    ∃ ρ : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃),
      ∀ k : Fin 4, (rankOne (plusDatum 4 𝔽₃ (by norm_num)).rootGroup k).map ρ.toMonoidHom =
        rankOne (plusDatum 4 𝔽₃ (by norm_num)).rootGroup (triPerm k) := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hF : Nat.card 𝔽₃ = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have : Finite 𝔽₃ := Nat.finite_of_card_ne_zero (by omega)
  have hgen : ⨆ k, rankOne (plusDatum 4 𝔽₃ hn3).rootGroup (triPerm k) = ⊤ := by
    have h := Balance.iSup_rankOne_eq_top (plusDatum 4 𝔽₃ hn3)
      (Spin.plusDatum_isCTGroupDatum hn3 (Spin.plusDatum_iSup_eq_top 4 _ hn3))
    rw [← h]
    exact (Equiv.iSup_comp (g := fun k => rankOne (plusDatum 4 𝔽₃ hn3).rootGroup k) triEquiv)
  obtain ⟨Ψ, hΨsurj, -, -, -, -, hΨ⟩ := Q3.Q3W.weakCT3_spinPlus hadm hn3 hF
    (X := spinGroup (quadPlus 4 𝔽₃))
    (fun k => rankOne (plusDatum 4 𝔽₃ hn3).rootGroup (triPerm k)) hgen
    (fun i j hij h1 h2 a ha b hb => by
      have h0 := (LevisSpin.cartanD_of_not_edgeD hij h1 h2).1
      rw [← cartanD_triPerm] at h0
      exact commutes_rankOne_plusDatum hn3 h0 a ha b hb)
    (fun i j h => by
      have h0 := (LevisSpin.cartanD_of_edgeD h).1
      rw [← cartanD_triPerm] at h0
      exact standardPair_plusDatum_of_cartan hn3 h0)
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup (quadPlus 4 𝔽₃)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hinj : Function.Injective Ψ := Finite.injective_iff_surjective.mpr hΨsurj
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hΨsurj⟩, hΨ⟩

section Ordinary


theorem exists_aut_ordinary3 (hadm : StatedLieAdmissible .POmegaPlus 4 3 1)
    {c : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ Subgroup.center _) (hc2 : c * c = 1) :
    ∃ σ : spinGroup (quadPlus 4 𝔽₃) ≃* spinGroup (quadPlus 4 𝔽₃),
      PreservesFund 3 1 σ ∧ spinAction (quadPlus 4 𝔽₃) (σ c) = 1 := by
  obtain ⟨ρ, hρ⟩ := exists_triality3 hadm
  exact exists_aut_ordinary (by norm_num) hadm ρ hρ hc hc2

end Ordinary

end CFSG.ClassicalInvolution.ModelFacts.TG3
