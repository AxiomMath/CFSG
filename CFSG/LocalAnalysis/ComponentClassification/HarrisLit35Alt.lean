module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltUniq
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.GH74.Generic.Front.Final
public import CFSG.GH74.Generic.FrontEnd
public import CFSG.GH74.Generic.S1.LinFull
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OrdU2
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitInitial
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Outer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltId
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Inputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36MType
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Open.QuasithinDefs
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
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import Certificates.Certificate3085Base

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup Equiv Equiv.Perm GrSLit.L34Facts

theorem rowFor_alt
    (hCI : GSLit.ClassicalInvolutionInput) : RowFor N36.IsAlt := by
  intro G _ _ p w v L K h ⟨m, hm5, ⟨e⟩⟩
  by_cases hm7 : m ≤ 7
  · exact (h.false_of_alt_small hCI hm5 hm7 e).elim
  push Not at hm7
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  set e' := eZ.symm.trans e with he'
  obtain ⟨π, hππ, hmemC⟩ := h.exists_perm (by omega) e'
  obtain ⟨k, hk, hs5, hLsl⟩ := h.slTwo
  have hlay := h.eq_layerIn e' hππ hmemC
  have hpar := h.params e' hππ hmemC hk hs5 hLsl
  have hZ2 : Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) = 2 := by
    have hq := h.quasisimple_quot
    have : Group.IsPerfect (↥K ⧸ pPrimeCore 2 ↥K) := hq.1
    let η : (↥K ⧸ pPrimeCore 2 ↥K) →* alternatingGroup (Fin m) :=
      e'.toMonoidHom.comp (QuotientGroup.mk' (center (↥K ⧸ pPrimeCore 2 ↥K)))
    have hη : Function.Surjective η := e'.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : η.ker = center (↥K ⧸ pPrimeCore 2 ↥K) := by
      ext x
      rw [MonoidHom.mem_ker]
      change e' (QuotientGroup.mk x) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have h2 :=
      LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
        (by omega) η hη (hker ▸ le_rfl)
        (hker ▸ N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2))
    rw [hker] at h2
    obtain ⟨r, hr⟩ := h.even_card_center
    have hpos : 0 < Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K)) := Nat.card_pos
    omega
  have hT : (π.supportᶜ).card = m - π.support.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  have hsupp : 2 ∣ π.support.card := Equiv.Perm.two_dvd_card_support (by rw [pow_two]; exact hππ)
  have hsle : π.support.card ≤ m := by
    have := Finset.card_le_univ π.support
    rwa [Fintype.card_fin] at this
  refine ⟨hlay, ?_⟩
  rcases hpar with ⟨hT5, hp5, hk1⟩ | ⟨hT6, hp3, hk2⟩
  ·
    right
    left
    obtain ⟨n, hn⟩ : ∃ n, m = 2 * n + 1 := ⟨(m - 1) / 2, by omega⟩
    refine ⟨hp5, ?_, n, by omega, h.quasisimple_quot, hZ2, ?_⟩
    · rw [hp5, hk1, pow_one] at hLsl
      exact hLsl
    · subst hn
      exact ⟨e'⟩
  ·
    right
    right
    obtain ⟨n, hn⟩ : ∃ n, m = 2 * n := ⟨m / 2, by omega⟩
    refine ⟨hp3, ?_, n, by omega, h.quasisimple_quot, hZ2, ?_⟩
    · rw [hp3, hk2] at hLsl
      exact hLsl
    · subst hn
      exact ⟨e'⟩

end CFSG.ComponentClassification.HarrisLit.L35

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

@[expose] def Harris81Lemma35IdentNonAltFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) → L35.Concl p v L K

theorem harris81Lemma35IdentFact_of_nonAlt
    (hCI : GSLit.ClassicalInvolutionInput) (hNA : Harris81Lemma35IdentNonAltFact) :
    Harris81Lemma35IdentFact := by
  intro G _ _ hs hnonab hK hcat p hp hp2 w v hw hv2 hvw hvM L hL hM k hk hs5 hLsl hwL K hKeq hLK
    hKc hwK hKM hKv
  have hc : L35.Config G p w v L K :=
    ⟨hs, hnonab, hK, hcat, hp, hp2, hw, hv2, hvw, hvM, hL, hM, ⟨k, hk, hs5, hLsl⟩, hwL, hKeq, hLK,
      hKc, hwK, hKM, hKv⟩
  by_cases halt : N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K)
  · exact L35.rowFor_alt hCI G p w v L K hc halt
  · exact hNA G p w v L K hc halt

end CFSG.ComponentClassification.HarrisLit
