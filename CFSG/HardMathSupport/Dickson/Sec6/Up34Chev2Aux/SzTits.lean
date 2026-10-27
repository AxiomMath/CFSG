module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.FamSz
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf


theorem up34C2_sz : Up34Chev2At FamSz := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα
  cases d with
  | suzuki m =>
    have hadm : StatedLieAdmissible .twistedB2 0 2 (2 * m + 1) :=
      ⟨Nat.prime_two, by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
        omega, rfl, rfl, odd_two_mul_add_one m, by
        have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at h
        omega⟩
    have hm := blueprintLieModel_suzuki m hv e
    obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
      .twistedB2 0 2 (2 * m + 1) hadm hm
    have h3 : 3 ∣ Nat.card S := (by norm_num : 3 ∣ 20160).trans hα.card_dvd
    have h3' : 3 ∣ lieOrderNumerator .twistedB2 0 (2 ^ (2 * m + 1)) := by
      rw [← hord]
      exact Dvd.dvd.mul_right h3 _
    exact absurd h3' (I923.not_three_dvd_suzuki_numerator (odd_two_mul_add_one m))
  | _ => exact hF.elim

theorem up34C2_tits : Up34Chev2At FamTits := by
  intro S _ _ hs hnab ⟨d, hv⟩ hF hc ⟨e⟩ α hα
  cases d with
  | tits =>
    have hadm : StatedLieAdmissible .Tits 0 2 1 := ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩
    have hm := blueprintLieModel_tits hv e
    obtain ⟨-, hord, -⟩ := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput S
      .Tits 0 2 1 hadm hm
    have h7 : 7 ∣ Nat.card S := (by norm_num : 7 ∣ 20160).trans hα.card_dvd
    have : Nat.card S = 17971200 := by
      simpa [lieOrderDivisor, lieOrderNumerator] using hord
    rw [this] at h7
    exact absurd h7 (by norm_num)
  | _ => exact hF.elim

end CFSG.HardMathSupport.Dickson.Sec6
