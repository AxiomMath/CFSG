module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Planes
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Planes
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Fusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3P34Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6_lemma42_of_wc (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hA1 : A6SylowData) (hAct : KFactA6SylowAction) (hA34 : GL83GenericPrimeThreeA6Prop34 G)
    (hU34 : GL83GenericPrimeThreeU3Fusion G) (hE34 : GL83GenericPrimeThreeL28Prop34S G)
    (hp : 3 ∈ rankThreeSigmaA G) (hIH : LargerPrimesUnique G 3) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) (hfail : ¬ rankThreeGamma 1 3 (P : Subgroup G) ≤ M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hR : A6Prop34 3 P J x)
    (hwc : LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    M11Lemma42 3 P M x := by
  obtain ⟨hxP, ⟨-, hx1, hx3, -, -⟩, -, -⟩ := id hgen
  have hinf : (P : Subgroup G) ⊓ centralizer ({x} : Set G) = (P : Subgroup G) :=
    inf_eq_left.mpr (a6fus_le_centralizer_of_wc hxP hx1 hx3 hwc)
  have hPab : IsMulCommutative (P : Subgroup G) := hinf ▸ hR.1
  rw [hinf] at hwc
  exact lemma42_of_fusion_abelian hS hp hM hxP hx1 hx3 hPab hwc fun u hugen =>
    linesNotWeaklyClosed_of_abelian hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA1 hAct hA34
      hU34 hE34 hp hIH hM hfail hPab hugen

theorem GL83GenericPrimeThreeA6.of_planes (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hS1 : A6SylowData) (hS2 : KFactA6TwoSignalizer) (hS3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction)
    (hU34 : GL83GenericPrimeThreeU3Fusion G) (hE34 : GL83GenericPrimeThreeL28Prop34S G)
    (h34 : GL83GenericPrimeThreeA6Prop34 G) (h43 : GL83GenericPrimeThreeA6Lemma43 G) :
    GL83GenericPrimeThreeA6 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsA6Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have h34' := h34 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  obtain ⟨U, hV, h43'⟩ := h43 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ
    hψ hker hQ h34'
  have h42' : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M := by
    by_cases hwc : LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
    · have h := a6_lemma42_of_wc hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hSig hL hS1 hAct h34 hU34
        hE34 hp hIH hM hfail hgen h34' hwc
      exact fun u hu hux => h U (hV.1.trans inf_le_left) hV.2.1 hV.2.2.1 hV.2.2.2.1 u hu hux
    · exact fun u hu hux => a6_lemma42_of_not_wc hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hS1 hS3 hE1
        hE3 hAct hp hM hgen hJ h34' hwc U hV u hu hux
  exact a6_false_of_config hS hU0 hD1 hInn hWC hS1 hS2 hS3 hp hM hgen hJ h34' hV h42' h43'

theorem GL83GenericPrimeThreeU3.of_planes (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hKT : KFactM11SylowTransitive) (hSig : SignalizerTwoGroupKFact) (hL : KFactsL34Full)
    (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore)
    (hAct : KFactA6SylowAction) (hUAct : KFactU3SylowInversion)
    (hA34 : GL83GenericPrimeThreeA6Prop34 G) (hE34 : GL83GenericPrimeThreeL28Prop34S G)
    (hS1 : U3SylowData) (hS2 : KFactU3TwoSignalizer) (hS3 : U3BorelCore) (hS4 : U3AutData)
    (h34 : GL83GenericPrimeThreeU3Fusion G) (h43 : GL83GenericPrimeThreeU3Lemma43 G) :
    GL83GenericPrimeThreeU3 G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  have hJ : IsU3Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  have h34' := GL83GenericPrimeThreeU3Prop34.of_fusion hS hU0 hS1 hS4 h34 3 hp P M hM hfail hIH x
    hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
  have h43' := h43 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ
    h34'
  exact u3_false_of_config hS hU0 hD1 hInn hWC hS1 hS2 hS3 hp hM hgen hJ h34'
    (u3_lemma42_of_planes hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hKT hSig hL hA1 hA3 hE1 hE3 hAct
      hUAct hA34 h34 hE34 hp hIH hM hgen hJ h34') h43'

end CFSG.LocalAnalysis.RankThreeTheoremC
