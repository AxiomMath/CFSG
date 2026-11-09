module

public import CFSG.Certificates.Kernel.SporSch.ThirdLowerBase

public import CFSG.Sporadic.Co2Schreier.ThirdEBase1
public import CFSG.Certificates.NativeSchreierLowerBound

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

variable (h : ECheckH)
include h

@[expose] def chainEH : RawSchreierDatum 2300 :=
  rawOfArrays 2300 eRec.origArrs eRec.strongArrs eRec.baseArr eRec.wordArrs (by norm_num)
    (by rw [(eRec_shapeH h).origArrs_size, (eRec_shapeH h).strongArrs_size]; norm_num)
    (baseArr_lt_of_shape (eRec_shapeH h) thirdBase_lt)
    (baseArr_nodup_of_shape (eRec_shapeH h) thirdBase_nodup)

theorem chainEH_records : eRec.Records (chainEH h) :=
  records_rawOfArrays_of_shape (eRec_shapeH h) _ _ _ _ (by norm_num)

theorem chainEH_original : (chainEH h).originalSubgroup = locE := by
  unfold chainEH
  refine originalSubgroup_rawOfArrays_of_eqA (repTuple_gH h) ?_ (fun k hk => ?_) fun k hk => ?_
  · rw [eRec_origArrs, gA_sizeH h, gTuple_length]
  · have hk' : k < 15 := by rwa [eRec_origArrs, gA_sizeH h] at hk
    exact (rep_permOfArr ((eRec_shapeH h).orig_inv hk')).1
  · have hk' : k < 15 := by rwa [eRec_origArrs, gA_sizeH h] at hk
    rw [eRec_origArrs]
    exact (eqA_iff (rep_gPermH h hk') (rep_gPermH h hk')).2 rfl

theorem le_card_locEH : 1474560 ≤ Nat.card locE := by
  have h' := rawOrbitSizes_prod_le_card (chainEH_records h).2.2 (eFactsH h).eOK
  rw [chainEH_original h] at h'
  change (recordOrbits 2300 eRec).prod ≤ _ at h'
  rw [beq_iff_eq.1 (eFactsH h).eOrb] at h'
  exact h'

end CFSG.Sporadic.Co2Schreier
