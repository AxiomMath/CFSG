module

public import Certificates.Certificate441697
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.CentHomSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModelClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

section Cert


theorem tabX_pCoreOf (hP : Nat.card ↥P1408 = 177408000) (hle : wordSubgroupP nWords1 ≤ Gx pZ)
    (hN : Nat.card ↥(wordSubgroupP nWords1) = 256) :
    CFSG.Open.pCoreOf 2 (Gx pZ) = wordSubgroupP nWords1 := by
  obtain ⟨ψ, hsurj, hker, -⟩ := HaradaModel27.exists_hom_centralizer_pZ hP
  have hrange : Nat.card ↥ψ.range = 120 := by
    rw [MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    rfl
  refine pCoreOf_eq_of_hom_sym5 hle (natCard_centralizer_pZ hP) hN ψ hrange ?_
  intro n hn
  have : (⟨n, hle hn⟩ : ↥(Gx pZ)) ∈ ψ.ker := by
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr hn
  exact MonoidHom.mem_ker.1 this

theorem tableX_P (hP : Nat.card ↥P1408 = 177408000)
    (hK : IsShapeK ↥(_root_.commutator ↥P1408 ⊓ Gx pZ)) : TableXData pA pZ pB pZ₁ := by
  have h := Certificates.certificate441697 hP
  exact tableX_of_facts pA_mem_center' (not_isConj_inv hP) hK (natCard_centralizer_pZ hP)
    (tabX_pCoreOf hP h.R_le h.card_R) h

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
