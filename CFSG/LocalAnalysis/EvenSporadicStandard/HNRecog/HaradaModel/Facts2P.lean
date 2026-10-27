module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FactsP
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Eich
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.R0Max
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.FSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.Facts2

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert


theorem haradaFacts2_P (hB1 : TwoHSFacts ↥P1408 pA pZ pB pZ₁) {Ep : Subgroup ↥P1408}
    (hEp : ∀ x : ↥P1408, x ∈ Ep ↔ (x : Equiv.Perm (Fin 1408)) ∈ blocks1408) (hEn : Ep.Normal) :
    HaradaFacts2 ↥P1408 Ep pA pZ pB pZ₁ (wordSubgroupP sWords) (wordSubgroupP sWords ⊓ Ep)
      (wordSubgroupP tpWords) (wordSubgroupP (tpWords ++ w0Extra)) iotaP (Pi.single 0 1)
      (wordSubgroupP nWords1) (wordSubgroupP fWords) := by
  have hP : Nat.card ↥P1408 = 177408000 := by
    have := hB1.card_eq
    norm_num at this
    exact this
  have hι := iotaP_apply
  exact
    { haradaFacts_P hB1 hEp hEn with
      ι_zv := iota_zv iotaP hι
      lam_zv := by decide +kernel
      qm_zv := by decide +kernel
      card_R0 := r0_card hP
      R0_le_centralizer := r0_le_centralizer hP
      R0_le_normalizer := r0_le_normalizer hP iotaP hι
      R0_normal := r0_normal hP
      R0_max := r0_max hP
      R0_sq := r0_sq hP
      R0_comm := r0_comm hP
      R0_inter := r0_inter hP iotaP hι
      R0_eichler := r0_eichler hP iotaP hι
      R0_surj := r0_surj hP iotaP hι
      R0_faith := r0_faith hP
      F_le_centralizer := f_le_centralizer hP
      F_le_normalizer := f_le_normalizer iotaP hι hP
      F_iso := f_iso hP }

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
