module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM22
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM23Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM24Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM12
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenJ2
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenHS
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHeNine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRuNine
public import CFSG.RankThree.PartTwo.Sec4.T444.ONanItem434SporJ4Nine

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.RankThree.PartTwo.Sec4.Item434SporGen
  CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint CFSG.RankThree.Native CFSG.Sporadic.HeldB
  CFSG.Sporadic.RuSchreier

theorem sporPlaneKill_M22_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .M22 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : NativeSporadic.M22 ≃* Spor .M22 := b
  exact sporPlaneKill_three hOut (by decide) b' kill9_m22 b' offPair_M22


theorem sporPlaneKill_M23_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .M23 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : NativeSporadic.M23 ≃* Spor .M23 := b
  exact sporPlaneKill_three hOut (by decide) b' kill9_m23 b' offPair_M23

theorem sporPlaneKill_M24_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .M24 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  have b' : NativeSporadic.M24 ≃* Spor .M24 := b
  exact sporPlaneKill_three hOut (by decide) b' kill9_m24 b' offPair_M24

theorem sporPlaneKill_M12_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .M12 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  exact sporPlaneKill_three hOut (by decide) b' kill9_m12 b' offPair_M12


theorem sporPlaneKill_J2_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .J2 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  have b₀ : NativeSporadic.J2 ≃* Spor .J2 := b
  have eJ : NativeSporadic.J2 ≃* CFSG.ComponentClassification.J2Cover.P :=
    CFSG.ComponentClassification.J2Cover.nativeEquivP
  exact sporPlaneKill_three hOut (by decide) (eJ.symm.trans b₀) kill9_j2 b₀ offPair_J2

theorem sporPlaneKill_HS_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .HS 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have eH : NativeSporadic.Carrier .HS ≃* hs100P := hs100Equiv
  exact sporPlaneKill_three hOut (by decide) (eH.symm.trans b₀) kill9_hs b₀ offPair_HS

theorem sporPlaneKill_He_three
    (hOut : SporadicOuterLeTwo) :
    SporPlaneKill .He 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .He ≃* Spor .He := b
  have eH : NativeSporadic.Carrier .He ≃* heP := heEquivP
  exact sporPlaneKill_three hOut (by decide) (eH.symm.trans b₀) kill9_he b₀ offPair_He

theorem sporPlaneKill_Ru_three
    (hOut : SporadicOuterLeTwo) :
    SporPlaneKill .Ru 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have bP : ruP ≃* Spor .Ru := ruEquivP.symm.trans b
  have b₀ : NativeSporadic.Carrier .Ru ≃* Spor .Ru := b
  exact sporPlaneKill_three hOut (by decide) bP kill9_ru b₀ offPair_Ru


theorem sporPlaneKill_J4_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .J4 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .J4 ≃* Spor .J4 := b
  have hcard : Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 :=
    CFSG.Sporadic.J4.card_J4
  have hcard' : Nat.card NativeSporadic.J4 = 86775571046077562880 := hcard
  have : Finite NativeSporadic.J4 := Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
  have hL : (Nat.card NativeSporadic.J4).factorization 3 = 3 := by
    rw [hcard', show (86775571046077562880 : ℕ) = 3 ^ 3 * 3213910038743613440 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
  exact sporPlaneKill_three hOut (by decide) b'
    (fun P _ hP9 => Or.inl (ONanJ4Nine.fixGen_j4 hL P hP9)) b' offPair_J4


theorem sporPlaneKill_M11_three
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .M11 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have b' : NativeSporadic.M11 ≃* Spor .M11 := b
  exact sporPlaneKill_of_noSig_model hOut Nat.prime_three (by norm_num) (by decide) b'
    (fun R Y hR hR9 hY3 hRY =>
      Item434SporM11.eq_bot_of_le_normalizer_mulAut hR (by rw [hR9]; norm_num) hY3 hRY) b'
    offPair_M11


theorem sporPair_M22_three
    (hOut : SporadicOuterLeTwo) : SporPair .M22 3 :=
  sporPair_of_planeKill (sporPlaneKill_M22_three hOut)

theorem sporPair_M23_three
    (hOut : SporadicOuterLeTwo) : SporPair .M23 3 :=
  sporPair_of_planeKill (sporPlaneKill_M23_three hOut)

theorem sporPair_M24_three
    (hOut : SporadicOuterLeTwo) : SporPair .M24 3 :=
  sporPair_of_planeKill (sporPlaneKill_M24_three hOut)

theorem sporPair_M12_three
    (hOut : SporadicOuterLeTwo) : SporPair .M12 3 :=
  sporPair_of_planeKill (sporPlaneKill_M12_three hOut)

theorem sporPair_J2_three
    (hOut : SporadicOuterLeTwo) : SporPair .J2 3 :=
  sporPair_of_planeKill (sporPlaneKill_J2_three hOut)

theorem sporPair_HS_three
    (hOut : SporadicOuterLeTwo) : SporPair .HS 3 :=
  sporPair_of_planeKill (sporPlaneKill_HS_three hOut)

theorem sporPair_He_three
    (hOut : SporadicOuterLeTwo) : SporPair .He 3 :=
  sporPair_of_planeKill (sporPlaneKill_He_three hOut)

theorem sporPair_Ru_three
    (hOut : SporadicOuterLeTwo) : SporPair .Ru 3 :=
  sporPair_of_planeKill (sporPlaneKill_Ru_three hOut)

theorem sporPair_J4_three
    (hOut : SporadicOuterLeTwo) : SporPair .J4 3 :=
  sporPair_of_planeKill (sporPlaneKill_J4_three hOut)

theorem sporPair_M11_three
    (hOut : SporadicOuterLeTwo) : SporPair .M11 3 :=
  sporPair_of_planeKill (sporPlaneKill_M11_three hOut)

end CFSG.HardMathSupport.Dickson.I271
