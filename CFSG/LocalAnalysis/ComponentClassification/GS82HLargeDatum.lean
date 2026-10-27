module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSLitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUGlue
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotIso
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTwoComp
public import CFSG.GH74.GLS.TwoThin.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB10
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem mem_coreActionKernel_of_mem_fusionZStar {K T : Subgroup X} (hTK : T ≤ K) {w : X}
    (hwT : w ∈ T) (hwK : w ∈ (Open.fusionZStar ↥K).map K.subtype) : w ∈ coreActionKernel T := by
  obtain ⟨k, hk, rfl⟩ := hwK
  refine mem_coreActionKernel.mpr ⟨le_normalizer hwT, fun j hj => ?_⟩
  have h1 : ⁅k, (⟨j, hTK hj⟩ : ↥K)⁻¹⁆ ∈ pPrimeCore 2 ↥K := OddQuot.mem_fusionZStar_iff.mp hk _
  have h2 : (k : ↥K)⁻¹ * ⁅k, (⟨j, hTK hj⟩ : ↥K)⁻¹⁆ * k ∈ pPrimeCore 2 ↥K :=
    by simpa using (pPrimeCore_normal (p := 2) (G := ↥K)).conj_mem _ h1 k⁻¹
  have h3 : (k : ↥K)⁻¹ * ⁅k, (⟨j, hTK hj⟩ : ↥K)⁻¹⁆ * k =
      (⟨j, hTK hj⟩ : ↥K)⁻¹ * k⁻¹ * ⟨j, hTK hj⟩ * k := by
    simp only [commutatorElement_def]
    group
  rw [h3] at h2
  have h4 : j⁻¹ * (k : X)⁻¹ * j * k ∈ (pPrimeCore 2 ↥K).map K.subtype :=
    ⟨_, h2, by simp⟩
  have hle : ((pPrimeCore 2 ↥K).map K.subtype).subgroupOf T ≤ pPrimeCore 2 ↥T := by
    refine le_sSup ⟨?_, ?_⟩
    · constructor
      intro x hx g
      rw [mem_subgroupOf] at hx ⊢
      have hgK : ((g : ↥T) : X) ∈ K := hTK g.2
      have hN := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K)
        (le_normalizer hgK)
      simpa using (mem_normalizer_iff.mp hN _).mp hx
    · have h5 : Nat.card ↥(((pPrimeCore 2 ↥K).map K.subtype).subgroupOf T) ∣
          Nat.card ↥(pPrimeCore 2 ↥K) := by
        rw [← Subgroup.card_map_of_injective T.subtype_injective, subgroupOf_map_subtype,
          ← Subgroup.card_map_of_injective K.subtype_injective]
        exact Subgroup.card_dvd_of_le inf_le_left
      exact Nat.Coprime.coprime_dvd_right h5 pPrimeCore_coprime_card
  have h6 : (⟨j⁻¹ * (k : X)⁻¹ * j * k, mul_mem (mul_mem (mul_mem (inv_mem hj)
      (inv_mem hwT)) hj) hwT⟩ : ↥T) ∈ pPrimeCore 2 ↥T := hle (mem_subgroupOf.mpr h4)
  exact ⟨_, h6, rfl⟩

theorem isDatum_of_gs82HConfig {q : ℕ} {t : X} {K R T : Subgroup X} {w : X}
    (h : GS82HConfig q t K R T w) :
    GS82PumpInputs.IsDatum q t K (GSLit.fixedLayer T (zpowers w)) w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht, hKt, hKc, -, -, -, hTKR, hTc, hSL, hw, hwT, hwK⟩ := h
  have hTK : T ≤ K := hTKR.trans inf_le_left
  have hTq : IsQuasisimple (↥T ⧸ pPrimeCore 2 ↥T) := by
    have h1 := GH74.GLS.TwoThin.isQuasisimple_hat_of_isPComponent hTc
    let e := subgroupOfEquivOfLe hTKR
    exact LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e))
      h1
  have hE : zpowers w ≤ coreActionKernel T :=
    (zpowers_le (G := X)).mpr (mem_coreActionKernel_of_mem_fusionZStar hTK hwT hwK)
  have hE2 : IsPGroup 2 (zpowers w) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hw, pow_one]
  have hTT : (T.subgroupOf T).IsSubnormal := by
    rw [subgroupOf_self]
    exact Subgroup.IsSubnormal.top
  have hNc := GSLit.fixedLayer_isPComponent le_rfl hTT (zpowers_le.mpr hwT) hE hE2 hTq
  have hNle := GSLit.fixedLayer_le_inf T (zpowers w)
  have hNq := ((HarrisLit.isTwoComponentIn_iff hNle).mpr hNc).2.2
  refine ⟨ht, hKt, hKc, (hNle.trans inf_le_left).trans hTK, Subgroup.isPerfect_iff.mp hNq.1,
    ?_, hw, ?_, hNle.trans (inf_le_right.trans (centralizer_le ?_)), hwK⟩
  · obtain ⟨F, hF, hFt, hFq, ⟨eA⟩⟩ := hSL
    obtain ⟨e⟩ := QPUJ.nonempty_fixedLayer_quot_equiv hTq hE hE2
    exact ⟨F, hF, hFt, hFq, ⟨e.trans eA⟩⟩
  · rw [GSLit.fixedLayer_eq_closure hTq hE hE2]
    refine subset_closure ⟨mem_inf.mpr ⟨hwT, ?_⟩, 1, by rw [hw, pow_one]⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_left (Commute.refl w) k).eq
  · exact Set.singleton_subset_iff.mpr (mem_zpowers w)

end CFSG.ComponentClassification.GSThmB
