module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3U43
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def zbarC (K : Type*) [Group K] (z : K) :
    ↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K)) :=
  QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

@[expose] def SolomonM10Hyp (K : Type*) [Group K] (z : K) : Prop :=
  ∃ Ab : Subgroup (↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K))),
    Nonempty (↥Ab ≃* alternatingGroup (Fin 6)) ∧ zbarC K z ∉ Ab ∧
      (Ab ⊔ zpowers (zbarC K z)).index = 2 ∧
      ∀ h : ↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K)),
        h * h ∈ zpowers (zbarC K z) → h ∈ Ab ⊔ zpowers (zbarC K z)

@[expose] def SolomonM10Conclusion (K : Type) [Group K] (z : K) : Prop :=
  (∃ U : Subgroup (↥(centralizer ({z} : Set K)) ⧸ fusionOddCore ↥(centralizer ({z} : Set K))),
      Disjoint U (zpowers (zbarC K z)) ∧ U ⊔ zpowers (zbarC K z) = ⊤) ∧
    ((∃ N : Subgroup K, N.Normal ∧
        Nonempty (↥N ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) ∧
        centralizer (N : Set K) = ⊥) ∨
      Nonempty (K ≃* ↥U43Ext))

@[expose] def SolomonM10 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.SectionRank.IsKGroupCat K → ∀ z : K, orderOf z = 2 →
    fusionZStar K = ⊥ → fusionOddCore ↥(centralizer ({z} : Set K)) = ⊥ →
    SolomonM10Hyp K z → SolomonM10Conclusion K z

@[expose] def Lemma96Conclusion (K : Type) [Group K] (zb : K ⧸ fusionOddCore K) : Prop :=
  SolomonM10Conclusion (K ⧸ fusionOddCore K) zb

end CFSG.EvenSporadicStandard.Fin76b
