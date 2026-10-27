module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1211

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

namespace Lemma1211Cyc

theorem input_cyc3_holds : Lemma1211.Input_cyc3 := by
  intro X _ _ hX hE
  by_contra hnc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 X) := ⟨hX⟩
  obtain ⟨S, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have h := hE S (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hel)
  rw [hcard] at h
  norm_num at h

end Lemma1211Cyc

open Lemma1211 in
theorem lemma1211_of_inputs' (hI : Input31_2_three)
    (h129 : Lemma129PrintedStatement) (h1210 : Lemma1210Statement)
    (hα : Claim1211_alpha) (hR3 : Claim1211_R3)
    (hm3 : Claim1211_m3) (hTI : Claim1211_TI) (hOM : Claim1211_OM) :
    Lemma1211Statement :=
  lemma1211_of_inputs hI Lemma1211Cyc.input_cyc3_holds h129 h1210 hα hR3 hm3 hTI hOM

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
