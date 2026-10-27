module

public import CFSG.HardMathSupport.Dickson.BMRows.CensusB3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusB7
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM3
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM5
public import CFSG.HardMathSupport.Dickson.BMRows.CensusM7
public import CFSG.HardMathSupport.Dickson.BMRows.Rows
import CFSG.HardMathSupport.Dickson.BMRows.ConcreteAll
import CFSG.HardMathSupport.Dickson.BMRows.NotSqDvd
import CFSG.HardMathSupport.Dickson.BMRows.RowsB
import CFSG.HardMathSupport.Dickson.BMRows.RowsM
import CFSG.HardMathSupport.Dickson.BMRows.Types
import CFSG.HardMathSupport.Dickson.BMRows.TypesLie80640
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows

public section

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.HardMathSupport.Dickson.I271 (TabBThreeBNoComp TabBFiveBNoComp M3ResBNoComp
  CentFiveBNoComp)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable LieOrderBridge
  sporadicOrdersTable_holds lieOrderBridge_holds)
open CFSG.HardMathSupport.Timmesfeld.Proving (sporadicOuterLeTwo_holds)

section Model

variable {s : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]

theorem crow_of_census (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    {P : TauCeti.CFSGIndex → Prop} (hC : PCompCensus p Q P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → Chev2Rows.CTypeOK p T) :
    Chev2Rows.CRow s p :=
  Chev2Rows.crow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

theorem crow_of_cardCensus
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a) {N : ℕ}
    (hC : PCardCensus p Q N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → Chev2Rows.CTypeOK p T) :
    Chev2Rows.CRow s p :=
  Chev2Rows.crow_of_model hOut b hnc fun k hk I hI => hT _ (hC k hk I hI)

end Model

theorem ctypeOK_B3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .Fi22) → Chev2Rows.CTypeOK p T := by
  intro T _ h hC
  have hc := card_of_catalogIs_Fi22 hOrd h
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact (not_isChevSimple_of_card_fi22 hb hc 2 hC).elim

theorem ctypeOK_B5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HS) → Chev2Rows.CTypeOK p T := by
  intro T _ h hC
  have hc := card_of_catalogIs_HS hOrd h
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact (not_isChevSimple_of_card_hs hb hc 2 hC).elim

theorem ctypeOK_B7 (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], Nat.card T ∣ 80640 → Chev2Rows.CTypeOK p T := by
  intro T _ hd hC
  have : Finite T := Nat.finite_of_card_ne_zero fun h0 => by rw [h0] at hd; norm_num at hd
  rcases hC with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      obtain ⟨q, ⟨rfl, hq⟩ | ⟨rfl, hq⟩⟩ :=
        Lie80640.lieOrderFormula_dvd_80640 hv (hb ⟨d, hv⟩ T ⟨e⟩ ▸ hd)
      · exact ⟨.lie ⟨.A 1 q, hv⟩, Or.inl hq, ⟨e⟩⟩
      · exact ⟨.lie ⟨.A 2 q, hv⟩, Or.inr hq, ⟨e⟩⟩
    | _ => exact hi.elim
  · exact ⟨i, Or.inl (LieGrid.chev2Small_of_ambiguous hi), ⟨e⟩⟩

theorem ctypeOK_M3 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T],
      catalogIs T (fun i => i = .sporadic .Fi24Prime ∨ i = .sporadic .Th) →
        Chev2Rows.CTypeOK p T := by
  rintro T _ ⟨i, hi | hi, he⟩ hC
  · have hc := card_of_catalogIs_Fi24Prime hOrd ⟨i, hi, he⟩
    have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact (I1416Rows.not_isChevSimple_two_of_card hb (a := 21) (m := 598528723330813275)
      (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num) (by norm_num) hC).elim
  · have hc := card_of_catalogIs_Th hOrd ⟨i, hi, he⟩
    have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
    exact (I1416Rows.not_isChevSimple_two_of_card hb (a := 15) (m := 2769346432125)
      (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num) (by norm_num) hC).elim

theorem ctypeOK_M5 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .HN) → Chev2Rows.CTypeOK p T := by
  intro T _ h hC
  have hc := card_of_catalogIs_HN hOrd h
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact (I1416Rows.not_isChevSimple_two_of_card hb (a := 14) (m := 16664484375)
    (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num) (by norm_num) hC).elim

theorem ctypeOK_M7 (hOrd : SporadicOrdersTable) (hb : LieOrderBridge) {p : ℕ} :
    ∀ (T : Type) [Group T], catalogIs T (· = .sporadic .He) → Chev2Rows.CTypeOK p T := by
  intro T _ h hC
  have hc := card_of_catalogIs_He hOrd h
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact (I1416Rows.not_isChevSimple_two_of_card hb (a := 10) (m := 3935925)
    (hc.trans (by norm_num)) (Nat.odd_iff.2 (by norm_num)) (by norm_num) (by norm_num) hC).elim

section Rows

theorem crow_B_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop}
    (hC : PCompCensus p (Carrier .B) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → Chev2Rows.CTypeOK p T) :
    Chev2Rows.CRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact crow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem crow_B_of_cardCensus {p N : ℕ} (hC : PCardCensus p (Carrier .B) N)
    (hT : ∀ (T : Type) [Group T], Nat.card T ∣ N → Chev2Rows.CTypeOK p T) :
    Chev2Rows.CRow .B p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_B
  exact crow_of_cardCensus sporadicOuterLeTwo_holds b hnc hC hT

theorem crow_M_of_census {p : ℕ} {P : TauCeti.CFSGIndex → Prop}
    (hC : PCompCensus p (Carrier .M) P)
    (hT : ∀ (T : Type) [Group T], catalogIs T P → Chev2Rows.CTypeOK p T) :
    Chev2Rows.CRow .M p := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact crow_of_census sporadicOuterLeTwo_holds b hnc hC hT

theorem crows_B_all (h3 : Chev2Rows.CRow .B 3) (h5 : Chev2Rows.CRow .B 5)
    (h7 : Chev2Rows.CRow .B 7) : ∀ p, Chev2Rows.CRow .B p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_B hp hp2 with rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact crow_B_of_eleven_le hp h S he hp hp2

theorem crows_M_all (h3 : Chev2Rows.CRow .M 3) (h5 : Chev2Rows.CRow .M 5)
    (h7 : Chev2Rows.CRow .M 7) (h11 : Chev2Rows.CRow .M 11)
    (h13 : Chev2Rows.CRow .M 13) : ∀ p, Chev2Rows.CRow .M p := by
  intro p S _ _ he hp hp2
  rcases prime_cases_M hp hp2 with rfl | rfl | rfl | rfl | rfl | h
  · exact h3 S he hp hp2
  · exact h5 S he hp hp2
  · exact h7 S he hp hp2
  · exact h11 S he hp hp2
  · exact h13 S he hp hp2
  · exact crow_M_of_seventeen_le hp h S he hp hp2

section B3NoComp

section KGroup

theorem crow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : Chev2Rows.CRow .B 3 :=
  crow_B_of_census (census_B_three hK) (ctypeOK_B3 sporadicOrdersTable_holds lieOrderBridge_holds)

end KGroup

end B3NoComp

section B5NoComp

section KGroup

theorem crow_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .B)) : Chev2Rows.CRow .B 5 :=
  crow_B_of_census (census_B_five hK) (ctypeOK_B5 sporadicOrdersTable_holds lieOrderBridge_holds)

end KGroup

end B5NoComp

section M3NoComp

section KGroup

theorem crow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (Carrier .M)) : Chev2Rows.CRow .M 3 :=
  crow_M_of_census (census_M_three hK) (ctypeOK_M3 sporadicOrdersTable_holds lieOrderBridge_holds)

end KGroup

end M3NoComp

section M5NoComp

section KGroup

theorem crow_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (Carrier .M)) : Chev2Rows.CRow .M 5 :=
  crow_M_of_census (census_M_five hK) (ctypeOK_M5 sporadicOrdersTable_holds lieOrderBridge_holds)

end KGroup

end M5NoComp

section B7

theorem crow_B_seven
    : Chev2Rows.CRow .B 7 :=
  crow_B_of_cardCensus (census_B_seven : PCardCensus 7 (Carrier .B) 80640)
    (ctypeOK_B7 lieOrderBridge_holds)

end B7

section M7

theorem crow_M_seven
    : Chev2Rows.CRow .M 7 :=
  crow_M_of_census census_M_seven (ctypeOK_M7 sporadicOrdersTable_holds lieOrderBridge_holds)

end M7

end Rows

end CFSG.HardMathSupport.Dickson.BMRows
