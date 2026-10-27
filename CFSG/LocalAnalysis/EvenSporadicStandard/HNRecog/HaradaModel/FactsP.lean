module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.HarCoreP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FuseSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.E64P
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert


noncomputable def iotaP : Multiplicative V6 →* ↥P1408 := Classical.choose exists_iotaP

theorem iotaP_apply (v : V6) : iotaP (Multiplicative.ofAdd v) = iotaFun v :=
  Classical.choose_spec exists_iotaP v

theorem haradaFacts_P (hB1 : TwoHSFacts ↥P1408 pA pZ pB pZ₁) {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) (hEn : Ep.Normal) :
    HaradaFacts ↥P1408 Ep pA pZ pB pZ₁ (wordSubgroupP sWords) (wordSubgroupP sWords ⊓ Ep)
      (wordSubgroupP tpWords) (wordSubgroupP (tpWords ++ w0Extra)) iotaP := by
  have hP : Nat.card ↥P1408 = 177408000 := by
    have := hB1.card_eq
    norm_num at this
    exact this
  have hι := iotaP_apply
  exact
    { toTwoHSFacts := hB1
      harCore := harCoreP hB1 hEp hEn
      isPGroup_S := sylowP_isPGroup
      card_S := sylowP_card
      injective_ι := injective_iota iotaP hι
      ι_tv := iota_tv iotaP hι
      coords_z := coords_z_A iotaP hι
      coords_b := coords_b_A iotaP hι
      coords_z₁ := coords_z₁_A iotaP hι
      mem_E_iff := mem_E_iff_A iotaP hι hEp
      conj_E64 := fun B hB he => by
        rw [range_iota iotaP hι]
        exact conj_E64_P hP hB he
      centralizer_le := centralizer_le_A iotaP hι hP
      card_normalizer := card_normalizer_A iotaP hι hP
      fuse := fun v w hv0 hvt hw0 hwt hl hq => fuse_A iotaP hι v w hv0 hvt hw0 hwt hl hq }

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
