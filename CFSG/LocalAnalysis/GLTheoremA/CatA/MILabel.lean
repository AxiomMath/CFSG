module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches
public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.StandardType
open CFSG.Timmesfeld.Orders CFSG.SeitzReduction.F4Pilot.EvenExc

theorem tits_odd : Odd (3 ^ 3 * 5 ^ 2 * 13) := by decide

theorem ordTits_eq : ordTits = 2 ^ 11 * (3 ^ 3 * 5 ^ 2 * 13) := by
  unfold ordTits; ring

theorem evenLieOrder_ne_ordTits {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (ht : t ≠ .Tits) :
    CFSG.SeitzReduction.F4Pilot.evenLieOrder t n f ≠ ordTits := by
  have hf : 1 ≤ f := hadm.2.1
  rw [ordTits_eq]
  cases t with
  | PSL =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
    have hm : 1 ≤ m := by have := hadm.2.2.1; omega
    show CFSG.Open.ordA (m + 1 - 1) (2 ^ f) ≠ _
    rw [Nat.add_sub_cancel]
    by_cases h111 : m = 1 ∧ f = 11
    · obtain ⟨rfl, rfl⟩ := h111
      decide
    · refine (profile_ordA hm hf).ne_of_ne tits_odd fun hN => h111 ?_
      have h1 : f ∣ 11 := ⟨m * (m + 1) / 2, hN.symm⟩
      have h2 : f = 1 ∨ f = 11 := (Nat.dvd_prime (by norm_num)).1 h1
      rcases h2 with rfl | rfl
      · exfalso
        have h3 : m * (m + 1) / 2 = 11 := by omega
        have h4 : m ≤ 5 := by
          by_contra hh
          have : 6 ≤ m := by omega
          have : 6 * 7 ≤ m * (m + 1) := Nat.mul_le_mul this (by omega)
          omega
        interval_cases m <;> omega
      · refine ⟨?_, rfl⟩
        have h3 : m * (m + 1) / 2 = 1 := by omega
        have h4 : m ≤ 2 := by
          by_contra hh
          have : 3 ≤ m := by omega
          have : 3 * 4 ≤ m * (m + 1) := Nat.mul_le_mul this (by omega)
          omega
        interval_cases m <;> omega
  | PSU =>
    obtain ⟨-, -, hn, hn32⟩ := hadm
    show CFSG.Open.ordTwistedA (n - 1) (2 ^ f) ≠ _
    refine (profile_ordTwistedA (by omega) hf).ne_of_ne tits_odd fun hN => ?_
    have h1 : f ∣ 11 := ⟨(n - 1) * (n - 1 + 1) / 2, hN.symm⟩
    have h2 : f = 1 ∨ f = 11 := (Nat.dvd_prime (by norm_num)).1 h1
    have h5 : 3 ≤ (n - 1) * (n - 1 + 1) / 2 := by
      have : 2 * 3 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    rcases h2 with rfl | rfl
    · have h3 : (n - 1) * (n - 1 + 1) / 2 = 11 := by omega
      have h4 : n ≤ 6 := by
        by_contra hh
        have : 6 ≤ n - 1 := by omega
        have : 6 * 7 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul this (by omega)
        omega
      interval_cases n <;> omega
    · omega
  | PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    show CFSG.Open.ordBC n (2 ^ f) ≠ _
    refine (profile_ordBC hf).ne_of_ne tits_odd fun hN => ?_
    have h4 : 4 ≤ n * n := by nlinarith
    have h1 : f ∣ 11 := ⟨n * n, hN.symm⟩
    have h2 : f = 1 ∨ f = 11 := (Nat.dvd_prime (by norm_num)).1 h1
    rcases h2 with rfl | rfl
    · have h3 : n * n = 11 := by omega
      have h5 : n ≤ 3 := by nlinarith
      interval_cases n <;> omega
    · omega
  | POmegaOdd => exact absurd rfl hadm.2.2.2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordD n (2 ^ f) ≠ _
    refine (profile_ordD (by omega) hf).ne_of_ne tits_odd fun hN => ?_
    have h4 : 12 ≤ n * (n - 1) := by
      have : 3 ≤ n - 1 := by omega
      nlinarith
    have hle := Nat.le_mul_of_pos_left (n * (n - 1)) (show 0 < f by omega)
    omega
  | POmegaMinus =>
    have hn : 4 ≤ n := hadm.2.2
    show CFSG.Open.ordTwistedD n (2 ^ f) ≠ _
    refine (profile_ordTwistedD (by omega) hf).ne_of_ne tits_odd fun hN => ?_
    have h4 : 12 ≤ n * (n - 1) := by
      have : 3 ≤ n - 1 := by omega
      nlinarith
    have hle := Nat.le_mul_of_pos_left (n * (n - 1)) (show 0 < f by omega)
    omega
  | F4 => exact (profile_ordF4' hf).ne_of_ne tits_odd (by omega)
  | E6 => exact (profile_ordE6' hf).ne_of_ne tits_odd (by omega)
  | E7 => exact (profile_ordE7' hf).ne_of_ne tits_odd (by omega)
  | E8 => exact (profile_ordE8' hf).ne_of_ne tits_odd (by omega)
  | twistedE6 => exact (profile_ordTwistedE6' hf).ne_of_ne tits_odd (by omega)
  | G2 => exact (profile_ordG2' hf).ne_of_ne tits_odd (by omega)
  | trialityD4 => exact (profile_ordTrialityD4' hf).ne_of_ne tits_odd (by omega)
  | twistedB2 => exact (profile_ordSuzuki' hf).ne_of_ne tits_odd (by omega)
  | twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  | twistedF4 => exact (profile_ordTwistedF4' hf).ne_of_ne tits_odd (by omega)
  | Tits => exact absurd rfl ht


theorem card_markedModel_g2der {lab : LargeEvenLabel} (hg : lab.tag = .G2der) {R : Type}
    [Group R] (h : MarkedModel lab R) : Nat.card R = 6048 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hg
  subst hg
  dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
        (by norm_num)]
    decide
  all_goals exact absurd hn (by norm_num)

theorem card_markedModel_twF4der {lab : LargeEvenLabel} (hg : lab.tag = .twF4der) {R : Type}
    [Group R] (h : MarkedModel lab R) : Nat.card R = ordTits := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hg
  subst hg
  exact CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder h

theorem markTag_ne_Tits {lab : LargeEvenLabel} (h : lab.tag ≠ .twF4der) :
    markTag lab ≠ .Tits := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case twF4der => exact absurd rfl h
  all_goals first
    | (simp only [markTag]; done)
    | (simp only [markTag]; split_ifs <;> decide)
    | (simp only [markTag]; decide)

theorem derived_labelUniq {lab lab' : LargeEvenLabel} (hd : DerivedLab lab)
    (hne : lab.tag ≠ lab'.tag) {R R' : Type} [Group R] [Group R'] (hM : MarkedModel lab R)
    (hM' : MarkedModel lab' R') : IsEmpty (R ≃* R') := by
  refine ⟨fun σ => ?_⟩
  have hcard : Nat.card R = Nat.card R' := Nat.card_congr σ.toEquiv
  rcases hd with hd | hd
  · have h6048 : Nat.card R = 6048 := card_markedModel_g2der hd hM
    by_cases hb : lab'.tag = .B2der
    · have := ggMarkedModel_card_b2der hb hM'
      omega
    by_cases ht : lab'.tag = .twF4der
    · have := card_markedModel_twF4der ht hM'
      have h2 : ordTits = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := rfl
      omega
    have hg : lab'.tag ≠ .G2der := fun h => hne (hd.trans h.symm)
    have hY := lieModel_of_markedModel (markChar_eq_two_of_ne hb hg) hM'
    have hcardR' := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hY
    have hT : markTag lab' ≠ .Tits := markTag_ne_Tits ht
    have hMod : LieModel R .PSU 3 3 1 := by
      obtain ⟨t, l, n⟩ := lab
      dsimp only at hd
      subst hd
      exact hM
    have hodd : OddLieType R' :=
      ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, ⟨Nat.prime_three, le_rfl, by norm_num,
        by norm_num⟩, lieModel_of_mulEquiv' σ hMod⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hY hT hodd with
      ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · rw [h1, h2, h3] at hcardR'
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSL 2 2 = 60 := by decide
      omega
    · rw [h1, h2, h3] at hcardR'
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSL 3 1 = 168 := by decide
      omega
    · rw [h1, h2, h3] at hcardR'
      have : CFSG.SeitzReduction.F4Pilot.evenLieOrder .PSU 4 1 = 25920 := by decide
      omega
  · have hTits : Nat.card R = ordTits := card_markedModel_twF4der hd hM
    by_cases hb : lab'.tag = .B2der
    · have := ggMarkedModel_card_b2der hb hM'
      have h2 : ordTits = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := rfl
      omega
    by_cases hg : lab'.tag = .G2der
    · have := card_markedModel_g2der hg hM'
      have h2 : ordTits = 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := rfl
      omega
    have ht : lab'.tag ≠ .twF4der := fun h => hne (hd.trans h.symm)
    have hY := lieModel_of_markedModel (markChar_eq_two_of_ne hb hg) hM'
    have hcardR' := CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hY
    have hT : markTag lab' ≠ .Tits := markTag_ne_Tits ht
    exact evenLieOrder_ne_ordTits (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hY) hT
      (by omega)

end MI

end CFSG.LocalAnalysis.GLTheoremA
