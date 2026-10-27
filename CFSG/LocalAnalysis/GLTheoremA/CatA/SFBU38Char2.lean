module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatSingle
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.Models.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2018

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem I2018U38Char2_holds : I2018U38Char2 := by
  intro X _ _ hX r hr
  by_contra hr2
  obtain ⟨q, hv, hq8, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU3eight hX
  have hcard : Nat.card X = 5515776 :=
    CFSG.LocalAnalysis.GLTheoremA.CatSingle.card_isU3eight
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hX
  obtain ⟨hq2, hq3⟩ :=
    primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num) (hq8.trans (by norm_num))
  have hm2 := CFSG.Models.lieModel_twistedA 2 q hv e
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [hc, hf, hq2, hq3] at hm2
  have hb2 : CFSG.Blueprint.LieModel X .PSU (2 + 1) 2 3 :=
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm2
  rcases hr with ⟨i, hi, ⟨e'⟩⟩ | ⟨i, hi, ⟨e'⟩⟩
  ·
    cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie idx =>
      obtain ⟨d, hvd⟩ := idx
      have hd : d.characteristic = r := hi
      obtain ⟨t, n, p, f, hp, hL⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char ⟨d, hvd⟩
      have hLX : CFSG.Models.LieModel X t n p f := CFSG.Models.LieModel.of_mulEquiv e'.symm hL
      have hBX : CFSG.Blueprint.LieModel X t n p f :=
        CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hLX
      have hpd : p = d.characteristic := hp
      have hpprime : p.Prime := by
        rw [hpd]
        exact d.characteristic_prime
      have hp2 : p ≠ 2 := by
        rw [hpd, hd]
        exact hr2
      have hodd : CFSG.Blueprint.OddLieType X := ⟨t, n, p, f, hpprime, hp2, hBX.admissible, hBX⟩
      rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
          CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hb2 hodd with
        ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ | ⟨-, h2, h3⟩ <;> omega
  ·
    cases i with
    | cyclic p hp => simp [ambiguousChev] at hi
    | sporadic s => simp [ambiguousChev] at hi
    | alternating n hn =>
      have hn' : (n = 5 ∧ (r = 2 ∨ r = 5)) ∨ (n = 6 ∧ (r = 2 ∨ r = 3)) ∨ (n = 8 ∧ r = 2) := by
        simpa [ambiguousChev] using hi
      rcases hn' with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, h⟩
      · have h60 := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hn e'
        norm_num [Nat.factorial] at h60
        omega
      · have h360 := CFSG.LocalAnalysis.GLTheoremA.CatDistinct.card_alternating_of_iso hn e'
        norm_num [Nat.factorial] at h360
        omega
      · exact hr2 h
    | lie idx =>
      obtain ⟨d, hvd⟩ := idx
      have hord := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds
        ⟨d, hvd⟩ X ⟨e'⟩
      cases d with
      | A n q =>
        by_cases hn1 : n = 1
        · subst hn1
          have hi' : (q.card = 7 ∧ r = 2) ∨ (q.card = 8 ∧ r = 3) := by
            simpa [ambiguousChev] using hi
          rcases hi' with ⟨-, h⟩ | ⟨hq, -⟩
          · exact hr2 h
          · have h504 : Nat.card X = 504 := by
              rw [hord]
              show orderA 1 q.card = 504
              rw [hq]
              decide
            omega
        · simp [ambiguousChev, hn1] at hi
      | twistedA n q =>
        rcases (show n = 2 ∨ n = 3 ∨ (n ≠ 2 ∧ n ≠ 3) from by omega) with rfl | rfl | hn23
        · have hi' : q.card = 3 ∧ r = 2 := by simpa [ambiguousChev] using hi
          exact hr2 hi'.2
        · have hi' : q.card = 2 ∧ r = 3 := by simpa [ambiguousChev] using hi
          have h25920 : Nat.card X = 25920 := by
            rw [hord]
            show orderTwistedA 3 q.card = 25920
            rw [hi'.1]
            decide
          omega
        · obtain ⟨h2, h3⟩ := hn23
          simp only [ambiguousChev] at hi
          split at hi <;> first | omega | simp_all | exact absurd hi id
      | _ => simp [ambiguousChev] at hi

end CFSG.LocalAnalysis.GLTheoremA.I2018

end
