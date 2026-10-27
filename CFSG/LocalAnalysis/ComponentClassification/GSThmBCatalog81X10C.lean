module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10B
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def GS81Step10CInput : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p (2 * f) →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 p f → 3 < p ^ f →
      layerIn (centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) = ⊥ →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f → ∀ J₁ J₂ : Subgroup H, J₁ ≠ J₂ →
        X10.AzComp K d J₁ → X10.AzComp K d J₂ →
        ¬ ((J₁.subgroupOf (centralizer {h.a * d.z})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))).IsSubnormal →
        ¬ ((J₂.subgroupOf (centralizer {h.a * d.z})).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))).IsSubnormal →
        ∃ (z₀ : H) (J₀ : Subgroup H), orderOf z₀ = 2 ∧ z₀ ∈ J₀ ∧
          Open.IsSubnormal J₀ (centralizer ({z₀} : Set H)) ∧
          (∃ S : Sylow 2 J₀, ∃ r : ℕ, 3 ≤ r ∧
            Nonempty ((S : Subgroup J₀) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
          Open.classicalInvolutionWitness J₀

theorem gs81Step10Input_of
    (I : In81) (hC : GS81Step10CInput) : GS81Step10Input := by
  intro H _ _ h H₁ d v hst p f hp hp2 hf hJ hK hq h9
  obtain ⟨K, _, _, J₁, J₂, hKc, hne, hJ₁, hJ₂⟩ := X10.gs81Step10A I hst.facts hp hp2 hK hq
  have h5 : 5 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := (hp.odd_of_ne_two hp2).pow (n := f)
    omega
  by_cases hs₁ : ((J₁.subgroupOf (centralizer {h.a * d.z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))).IsSubnormal
  · exact X10.gs81Step10B hp hp2 hf hKc h5 hJ₁ hs₁
  by_cases hs₂ : ((J₂.subgroupOf (centralizer {h.a * d.z})).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({h.a * d.z} : Set H))))).IsSubnormal
  · exact X10.gs81Step10B hp hp2 hf hKc h5 hJ₂ hs₂
  exact hC H h H₁ d v hst p f hp hp2 hf hJ hK hq h9 K hKc J₁ J₂ hne hJ₁ hJ₂ hs₁ hs₂

theorem gs81Exit10Input_of_C
    (I : In81) (hC : GS81Step10CInput) (hrec : CF81Exit10Recognition) : GS81Exit10Input :=
  gs81Exit10Input_of (gs81Step10Input_of I hC) hrec

end CFSG.ComponentClassification.GSThmB
