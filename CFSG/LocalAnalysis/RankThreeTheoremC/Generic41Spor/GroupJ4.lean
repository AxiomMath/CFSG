module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupHeis
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicJ4
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open Subgroup CFSG.AGLEmbeddingD2 CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.AGLEmbeddingD2.Wilson.Coordinator
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial


structure J4Facts : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → SylowIsHeisenberg 11 K
  noOuter : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NoOuterP 11 K
  irreducible : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerIrreducibleQuotient 11 K
  maximal : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerMaximal 11 K
  sigTriv : SignalizerTrivialX IsJ4Type 11

structure J4OpenFacts : Prop where
  transCenter : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerTransitiveCenter 11 K
  lemma45 : Lemma45Facts IsJ4Type 11 J4Shape

theorem j4_data {K : Type} [Group K] (hK : IsJ4Type 11 K) :
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.J4).Group) ∧
      Subgroup.center K = ⊥ := by
  obtain ⟨-, ⟨e⟩⟩ := hK
  have eKJ : K ≃* J :=
    e.trans ((CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv.some).symm.trans
      (seedEquiv j4Facts.mat))
  exact ⟨⟨e⟩, @center_eq_bot_of_mulEquiv K _ J (Subgroup.toGroup J) eKJ center_J⟩

theorem j4_extra :
    (∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → SylowIsHeisenberg 11 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NoOuterP 11 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerMaximal 11 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerIrreducibleQuotient 11 K) :=
  extra_of_d2Heis (T := IsJ4Type) (by norm_num) d2HeisLocalAt_J4 fun _ _ _ hK => j4_data hK

theorem j4_sylow : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → SylowIsHeisenberg 11 K :=
  j4_extra.1

theorem j4_noOuter : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NoOuterP 11 K :=
  j4_extra.2.1

theorem j4_maximal : ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerMaximal 11 K :=
  j4_extra.2.2.1

theorem j4_irreducible :
    ∀ (K : Type) [Group K] [Finite K], IsJ4Type 11 K → NormalizerIrreducibleQuotient 11 K :=
  j4_extra.2.2.2

theorem j4_sigTriv : SignalizerTrivialX IsJ4Type 11 :=
  signalizerTrivialX_of_on (by norm_num) fun K _ _ hK => signalizerTrivialJ4_holds K hK.2

theorem j4Facts_holds : J4Facts :=
  ⟨j4_sylow, j4_noOuter, j4_irreducible, j4_maximal, j4_sigTriv⟩

theorem extraFacts_j4 (h : J4Facts) (o : J4OpenFacts) : ExtraFacts IsJ4Type 11 J4Shape :=
  ⟨h.sylow, h.noOuter, o.transCenter, h.irreducible, h.maximal, h.sigTriv, o.lemma45⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
