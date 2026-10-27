module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupHeis
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialSporadicMcL
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial


structure McLFacts : Prop where
  sylow : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → SylowIsHeisenberg 5 K
  noOuter : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NoOuterP 5 K
  irreducible : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerIrreducibleQuotient 5 K
  maximal : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerMaximal 5 K
  sigTriv : SignalizerTrivialX IsMcLType 5

structure McLOpenFacts : Prop where
  transCenter : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerTransitiveCenter 5 K
  lemma45 : Lemma45Facts IsMcLType 5 McLShape

theorem mcl_data {K : Type} [Group K] (hK : IsMcLType 5 K) :
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.McL).Group) ∧
      Subgroup.center K = ⊥ := by
  obtain ⟨-, ⟨e⟩⟩ := hK
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact ⟨⟨e⟩, center_eq_bot_of_mulEquiv_mcl (e.trans eC.symm)⟩

theorem mcl_extra :
    (∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → SylowIsHeisenberg 5 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NoOuterP 5 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerMaximal 5 K) ∧
    (∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerIrreducibleQuotient 5 K) :=
  extra_of_d2Heis (T := IsMcLType) Nat.prime_five d2HeisLocalAt_mcl fun _ _ _ hK => mcl_data hK

theorem mcl_sylow : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → SylowIsHeisenberg 5 K :=
  mcl_extra.1

theorem mcl_noOuter : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NoOuterP 5 K :=
  mcl_extra.2.1

theorem mcl_maximal : ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerMaximal 5 K :=
  mcl_extra.2.2.1

theorem mcl_irreducible :
    ∀ (K : Type) [Group K] [Finite K], IsMcLType 5 K → NormalizerIrreducibleQuotient 5 K :=
  mcl_extra.2.2.2

theorem mcl_sigTriv : SignalizerTrivialX IsMcLType 5 :=
  signalizerTrivialX_of_on Nat.prime_five fun K _ _ hK => signalizerTrivialMcL_holds K hK.2

theorem mclFacts_holds : McLFacts :=
  ⟨mcl_sylow, mcl_noOuter, mcl_irreducible, mcl_maximal, mcl_sigTriv⟩

theorem extraFacts_mcl (h : McLFacts) (o : McLOpenFacts) : ExtraFacts IsMcLType 5 McLShape :=
  ⟨h.sylow, h.noOuter, o.transCenter, h.irreducible, h.maximal, h.sigTriv, o.lemma45⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
