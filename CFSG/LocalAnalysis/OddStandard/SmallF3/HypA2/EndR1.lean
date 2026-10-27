module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.EndDataDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PslBound
public import CFSG.Yardstones.M0362f3a873a3.Definitions
public import CFSG.GH74.NoComponent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSetup

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem false_of_psl_two_three
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree) {G : Type} [Group G]
    [Finite G] {x : G} {Y : Subgroup G} (hY : EndData G x Y) (hZ : center ↥Y = ⊥) {e : ℕ}
    (he : LieModel (↥Y ⧸ center ↥Y) .PSL 2 3 e)
    (hbig : classSBound ≤ Nat.card (↥Y ⧸ center ↥Y)) (hpow : ∃ j : ℕ, e = 2 ^ j)
    (S : Sylow 2 ↥(Subgroup.centralizer (Y : Set G)))
    (hS : IsCyclic ↥(S : Subgroup ↥(Subgroup.centralizer (Y : Set G)))) : False := by
  haveI := hY.setting.simple
  have h8e : 8 ≤ e := eight_le_of_lieModel_psl_two_three he hbig
  obtain ⟨j, hj⟩ := hpow
  have hj3 : 3 ≤ j := by
    by_contra h
    have hjle : j ≤ 2 := by omega
    have h8 : 8 ≤ 2 ^ j := by rw [← hj]; exact h8e
    interval_cases j <;> norm_num at h8
  have h8dvd : 8 ∣ e := by
    have h : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [hj, h]
    exact pow_dvd_pow 2 hj3
  have h32 : 32 ∣ Nat.card (↥Y ⧸ center ↥Y) :=
    thirtyTwo_dvd_card_of_lieModel_psl_two_three he h8dvd
  have hppc : CFSG.pPrimeCore 2 ↥Y = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two ↥Y]
    exact oddCore_eq_bot_of_isComponentIn (hY.setting.balanced x hY.ox) hY.comp
  have hcardQ : Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y) = Nat.card (↥Y ⧸ center ↥Y) := by
    rw [hppc, hZ]
  have hbal : (∃ z : G, orderOf z = 2 ∧
      CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) →
      CFSG.ComponentClassification.OutcomeLocal.UOutcome G :=
    fun ⟨z, hz, hne⟩ => absurd (hY.setting.balanced z hz) hne
  have hoddlie : OddLieType (↥Y ⧸ center ↥Y) :=
    ⟨.PSL, 2, 3, e, Nat.prime_three, by norm_num, he.admissible, he⟩
  have hl2r : CFSG.Yardstones.M0362f3a873a3.L2OrReeLieQuotient (↥Y ⧸ center ↥Y) :=
    Or.inl ⟨3, e, he⟩
  have h5 : ¬ Nonempty (↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e5⟩
    have hcard : Nat.card (↥Y ⧸ center ↥Y) = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      norm_num [Nat.factorial]
    have hle : classSBound ≤ 60 := by rw [← hcard]; exact hbig
    norm_num [classSBound] at hle
  have h6 : ¬ Nonempty (↥Y ⧸ center ↥Y ≃* alternatingGroup (Fin 6)) := by
    rintro ⟨e6⟩
    have hcard : Nat.card (↥Y ⧸ center ↥Y) = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
      norm_num [Nat.factorial]
    have hle : classSBound ≤ 360 := by rw [← hcard]; exact hbig
    norm_num [classSBound] at hle
  have hsc : ¬ CFSG.OddStandard.HarrisSolomonFritzScope Y := by
    intro hh
    obtain ⟨P, hP⟩ := hh.2.2
    have hne : Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y) ≠ 0 := by
      rw [hcardQ]
      intro h0
      have hpos : 0 < classSBound := by norm_num [classSBound]
      omega
    have h32Q : 32 ∣ Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y) := by
      rw [hcardQ]; exact h32
    have h32Q' : 2 ^ 5 ∣ Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y) := by
      have h : (2 : ℕ) ^ 5 = 32 := by norm_num
      rw [h]
      exact h32Q
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hk : 5 ≤ (Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y)).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp h32Q'
    have hPcard : Nat.card (P : Subgroup (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y)) =
        2 ^ (Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y)).factorization 2 :=
      Sylow.card_eq_multiplicity P
    have hle : 2 ^ 5 ≤ 2 ^ (Nat.card (↥Y ⧸ CFSG.pPrimeCore 2 ↥Y)).factorization 2 :=
      Nat.pow_le_pow_right (by norm_num) hk
    rw [← hPcard, hP] at hle
    norm_num at hle
  have hoddZ : Odd (Nat.card (center ↥Y)) := by
    rw [hZ, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have hmain := hL2 G Y
    ⟨hY.setting.simple, hY.setting.nonab, hY.setting.kProper, hY.standard⟩
    hbal hoddlie hl2r h5 h6 hsc (Or.inl hoddZ) S hS
  rcases hmain with halt | hodd | hspor
  · obtain ⟨m, hm, ⟨hmiso⟩⟩ := halt
    exact hY.setting.notCat (Or.inr (Or.inl ⟨m, by omega, ⟨hmiso⟩⟩))
  · exact hY.setting.notCat
      (CFSG.ComponentClassification.HarrisLit.catalog_of_oddLieType hodd)
  · rcases hspor with h | h | h | h
    · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
    · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
    · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)
    · exact hY.setting.notCat (CFSG.GH74.catalog_of_isSporadic h)

end CFSG.OddStandard.SmallF3.HypA2
