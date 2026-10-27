module

public import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerDefs
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.LayerExcl
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Table
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Alt9
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.U54
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.McL
import CFSG.LocalAnalysis.SectionRank.QTK.CentreFact.Sporadic
import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.Sporadic.J3
import CFSG.Sporadic.J4
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalogBase
public import CFSG.LocalAnalysis.SectionRank.SporadicCover

public section

namespace CFSG.SectionRank.QTK.CentreFact

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Cases

variable {H : Type} [Group H] [Finite H] {L₁ L₂ : Subgroup H} {r : ℕ}

private structure Pair (L₁ L₂ : Subgroup H) (r : ℕ) : Prop where
  he : CFSG.Open.evenRank H ≤ 2
  hK : CFSG.SectionRank.IsKGroupCat H
  h₁ : CFSG.IsComponent L₁
  h₂ : CFSG.IsComponent L₂
  hne : L₁ ≠ L₂
  hφ : Nonempty (↥L₁ ≃* ↥L₂)
  hr : r.Prime
  hr2 : r ≠ 2
  hrZ : r ∣ Nat.card (center ↥L₁)

private abbrev Concl (L₁ L₂ : Subgroup H) (r : ℕ) : Prop :=
  r = 3 ∧ CFSG.Quasithin.IsSU3 8 ↥L₁ ∧ CFSG.Open.pRank 3 (L₁ ⊔ L₂) = 3

private theorem pair_short (hP : LayerPairFact) (P : Pair L₁ L₂ 3)
    (hl : LayerPairList (↥L₁ ⧸ center ↥L₁)) : Concl L₁ L₂ 3 :=
  ⟨rfl, hP H P.he P.hK L₁ L₂ P.h₁ P.h₂ P.hne P.hφ hl P.hrZ⟩

private theorem pair_alt (hP : LayerPairFact) (P : Pair L₁ L₂ r) {n : ℕ} (hn5 : 5 ≤ n)
    (hn9 : n ≤ 9) (e : ↥L₁ ⧸ center ↥L₁ ≃* alternatingGroup (Fin n)) : Concl L₁ L₂ r := by
  haveI : Group.IsPerfect ↥L₁ := P.h₁.1.1
  obtain ⟨φ⟩ := P.hφ
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hcard : Nat.card (↥L₁ ⧸ center ↥L₁) = Nat.factorial n / 2 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
  have hr3 : r = 3 := by
    by_contra hr3
    refine layer_not_dvd_card_center_of_not_sq_dvd P.hr ?_ P.hrZ
    rw [hcard]
    intro hd
    have h5 : ¬ r ^ 2 ∣ 5 :=
      CFSG.SectionRank.not_sq_dvd_of_bound (B := 6) (by norm_num) (by norm_num) (by decide)
        P.hr P.hr2 hr3
    have h35 : ¬ r ^ 2 ∣ 35 :=
      CFSG.SectionRank.not_sq_dvd_of_bound (B := 6) (by norm_num) (by norm_num) (by decide)
        P.hr P.hr2 hr3
    interval_cases n
    · rw [show Nat.factorial 5 / 2 = 2 ^ 2 * 3 ^ 1 * 5 by decide] at hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3 h5 hd
    · rw [show Nat.factorial 6 / 2 = 2 ^ 3 * 3 ^ 2 * 5 by decide] at hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3 h5 hd
    · rw [show Nat.factorial 7 / 2 = 2 ^ 3 * 3 ^ 2 * 35 by decide] at hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3 h35 hd
    · rw [show Nat.factorial 8 / 2 = 2 ^ 6 * 3 ^ 2 * 35 by decide] at hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3 h35 hd
    · rw [show Nat.factorial 9 / 2 = 2 ^ 6 * 3 ^ 4 * 35 by decide] at hd
      exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3 h35 hd
  subst hr3
  interval_cases n
  · exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (by rw [hcard]; decide) P.hrZ).elim
  · exact pair_short hP P (Or.inl ⟨e⟩)
  · exact pair_short hP P (Or.inr (Or.inl ⟨e⟩))
  · exact (layer_false_of_realLocalElement_three P.he P.h₁ P.h₂ P.hne φ e
      layer_realLocalElement_alt_eight P.hrZ).elim
  · exact (not_three_dvd_card_center_of_alt_nine P.he e P.hrZ).elim

private theorem pair_odd
    (hP : LayerPairFact) (P : Pair L₁ L₂ r) (hT : TableRestricted (↥L₁ ⧸ center ↥L₁) r)
    {p : ℕ} (hp : p.Prime)
    (h : (∃ f : ℕ, 1 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL 2 p f) ∨
      (∃ f : ℕ, (f = 1 ∨ f = 2) ∧
        (StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL 3 p f ∨
          StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 3 p f)) ∨
      StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSp 2 p 1 ∨
      ChevalleyExceptionalModel (↥L₁ ⧸ center ↥L₁) .G2 p 1 ∨
      ((∃ a : ℕ, p = 2 ^ a + 1) ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL 4 p 1) ∨
      ((∃ b : ℕ, p + 1 = 2 ^ b) ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 4 p 1)) :
    Concl L₁ L₂ r := by
  rcases h with ⟨f, -, hm⟩ | ⟨f, hf, hm | hm⟩ | hm | hm | ⟨-, hm⟩ | ⟨-, hm⟩
  · obtain ⟨rfl, rfl, rfl⟩ := tablePrime_psl_two P.hr P.hr2 (hT.classical hm)
    obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_psl_two_nine hm
    exact pair_short hP P (Or.inl ⟨e⟩)
  · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
    obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq P.hr Nat.prime_three).1 hr3
    exact pair_short hP P (Or.inr (Or.inr (Or.inr ⟨p, f, hp, by omega, Or.inl ⟨hm, hrq⟩⟩)))
  · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
    obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq P.hr Nat.prime_three).1 hr3
    exact pair_short hP P (Or.inr (Or.inr (Or.inr ⟨p, f, hp, by omega, Or.inr ⟨hm, hrq⟩⟩)))
  · exact absurd (hT.classical hm) not_tablePrime_psp
  · obtain ⟨rfl, rfl, -⟩ := tablePrime_g2 (hT.chevalley (by decide) hm)
    exact (layer_false_of_g2_three P.he P.h₁ P.h₂ P.hne hm).elim
  · exact absurd (hT.classical hm) (not_tablePrime_psl_four P.hr P.hr2)
  · obtain ⟨rfl, rfl, -⟩ := tablePrime_psu_four P.hr P.hr2 (hT.classical hm)
    exact (layer_false_of_u4_three P.he P.h₁ P.h₂ P.hne hm P.hrZ).elim

private theorem pair_even (hP : LayerPairFact) (P : Pair L₁ L₂ r)
    (hT : TableRestricted (↥L₁ ⧸ center ↥L₁) r)
    (h : ((∃ f : ℕ,
      (2 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 3 2 f) ∨
      (2 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSp 2 2 f) ∨
      (1 ≤ f ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 4 2 f) ∨
      (2 ≤ f ∧ ChevalleyExceptionalModel (↥L₁ ⧸ center ↥L₁) .G2 2 f) ∨
      (1 ≤ f ∧ ChevalleyExceptionalModel (↥L₁ ⧸ center ↥L₁) .trialityD4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ ReeTitsModel (↥L₁ ⧸ center ↥L₁) .twistedF4 2 f) ∨
      (Odd f ∧ 3 ≤ f ∧ SuzukiModel (↥L₁ ⧸ center ↥L₁) 2 f)) ∨
      StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 5 2 2 ∨
      ReeTitsModel (↥L₁ ⧸ center ↥L₁) .Tits 2 1)) : Concl L₁ L₂ r := by
  rcases h with ⟨f, ⟨-, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ | ⟨-, hm⟩ |
    ⟨-, -, hm⟩ | ⟨-, -, hm⟩⟩ | hm | hm
  · exact absurd (tablePrime_psl_two P.hr P.hr2 (hT.classical hm)).2.1 (by norm_num)
  · obtain ⟨hr3, hrq⟩ := tablePrime_psl_three (hT.classical hm)
    obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq P.hr Nat.prime_three).1 hr3
    exact pair_short hP P (Or.inr (Or.inr (Or.inr ⟨2, f, Nat.prime_two, hf, Or.inl ⟨hm, hrq⟩⟩)))
  · obtain ⟨hr3, hrq⟩ := tablePrime_psu_three (hT.classical hm)
    obtain rfl : r = 3 := (Nat.prime_dvd_prime_iff_eq P.hr Nat.prime_three).1 hr3
    exact pair_short hP P
      (Or.inr (Or.inr (Or.inr ⟨2, f, Nat.prime_two, by omega, Or.inr ⟨hm, hrq⟩⟩)))
  · exact absurd (hT.classical hm) not_tablePrime_psp
  · exact absurd (tablePrime_psu_four P.hr P.hr2 (hT.classical hm)).2.1 (by norm_num)
  · exact absurd (tablePrime_g2 (hT.chevalley (by decide) hm)).2.1 (by norm_num)
  · exact absurd (hT.chevalley (by decide) hm) not_tablePrime_trialityD4
  · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_twistedF4
  · exact absurd (hT.suzuki hm) not_tablePrime_twistedB2
  · obtain rfl : r = 5 := tablePrime_psu_five_two_two P.hr (hT.classical hm)
    exact (not_five_dvd_card_center_of_U54 P.he hm P.hrZ).elim
  · exact absurd (hT.reeTits (by decide) hm) not_tablePrime_tits

private theorem pair_four (P : Pair L₁ L₂ r) (hT : TableRestricted (↥L₁ ⧸ center ↥L₁) r)
    (h : (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSL n 2 1) ∨
      StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSp 3 2 1) : Concl L₁ L₂ r := by
  rcases h with ⟨n, -, hm⟩ | hm
  · exact absurd (hT.classical hm) (not_tablePrime_psl_two_one P.hr)
  · exact absurd (hT.classical hm) not_tablePrime_psp

private theorem pair_sporadic
    (hP : LayerPairFact) (hJ : LayerPairJ3) (P : Pair L₁ L₂ r) {s : TauCeti.SporadicName}
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J3 ∨
      s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .McL)
    (e : ↥L₁ ⧸ center ↥L₁ ≃* NativeSporadic.Carrier s) : Concl L₁ L₂ r := by
  haveI : Group.IsPerfect ↥L₁ := P.h₁.1.1
  obtain ⟨φ⟩ := P.hφ
  have hJ4 : J4OrderHyp := dvd_of_eq CFSG.Sporadic.J4.card_J4
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have hn : Nat.card (↥L₁ ⧸ center ↥L₁) = 7920 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 443520 ∨
        Nat.card (↥L₁ ⧸ center ↥L₁) = 10200960 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.SectionRank.card_small_sporadic (s := .M11) (Or.inl rfl)
    obtain ⟨-, hrc⟩ := CFSG.SectionRank.small_sporadic_order_conditions hn
    by_cases hr3 : r = 3
    · subst hr3
      exact (layer_false_of_realLocalElement_three P.he P.h₁ P.h₂ P.hne φ e
        layer_realLocalElement_M11 P.hrZ).elim
    · exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (hrc r P.hr P.hr2 hr3) P.hrZ).elim
  · exact (not_dvd_card_center_of_M12 P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  ·
    have hn : Nat.card (↥L₁ ⧸ center ↥L₁) = 7920 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 443520 ∨
        Nat.card (↥L₁ ⧸ center ↥L₁) = 10200960 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.SectionRank.card_small_sporadic (s := .M22) (Or.inr (Or.inl rfl))
    obtain ⟨-, hrc⟩ := CFSG.SectionRank.small_sporadic_order_conditions hn
    by_cases hr3 : r = 3
    · subst hr3
      exact pair_short hP P (Or.inr (Or.inr (Or.inl ⟨e⟩)))
    · exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (hrc r P.hr P.hr2 hr3) P.hrZ).elim
  ·
    have hn : Nat.card (↥L₁ ⧸ center ↥L₁) = 7920 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 443520 ∨
        Nat.card (↥L₁ ⧸ center ↥L₁) = 10200960 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.SectionRank.card_small_sporadic (s := .M23) (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨-, hrc⟩ := CFSG.SectionRank.small_sporadic_order_conditions hn
    by_cases hr3 : r = 3
    · subst hr3
      exact (layer_false_of_realLocalElement_three P.he P.h₁ P.h₂ P.hne φ e
        layer_realLocalElement_M23 P.hrZ).elim
    · exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (hrc r P.hr P.hr2 hr3) P.hrZ).elim
  · exact (not_dvd_card_center_of_M24 P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  ·
    have hcard : Nat.card (↥L₁ ⧸ center ↥L₁) = 175560 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J1.card_J1
    obtain ⟨-, hrc⟩ := CFSG.SectionRank.small_sporadic_order_conditions
      (Or.inr (Or.inr (Or.inr hcard)) : Nat.card (↥L₁ ⧸ center ↥L₁) = 7920 ∨
        Nat.card (↥L₁ ⧸ center ↥L₁) = 443520 ∨ Nat.card (↥L₁ ⧸ center ↥L₁) = 10200960 ∨
        Nat.card (↥L₁ ⧸ center ↥L₁) = 175560)
    by_cases hr3 : r = 3
    · subst hr3
      exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (by rw [hcard]; decide) P.hrZ).elim
    · exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr (hrc r P.hr P.hr2 hr3) P.hrZ).elim
  · exact (not_dvd_card_center_of_J2 P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  ·
    by_cases hr3 : r = 3
    · subst hr3
      exact (hJ H P.he P.hK L₁ L₂ P.h₁ P.h₂ P.hne P.hφ ⟨e⟩ P.hrZ).elim
    · have hsq : ¬ r ^ 2 ∣ Nat.card (↥L₁ ⧸ center ↥L₁) := by
        rw [Nat.card_congr e.toEquiv, show Nat.card (NativeSporadic.Carrier .J3) = 50232960 from
          CFSG.Sporadic.J3.card_J3]
        intro hd
        have h2 : r ^ 2 ∣ 2 ^ 7 * 3 ^ 5 * 1615 := by
          rw [show 2 ^ 7 * 3 ^ 5 * 1615 = 50232960 by norm_num]
          exact hd
        exact CFSG.SectionRank.not_sq_dvd_of_not_sq_dvd_cofactor P.hr P.hr2 hr3
          (CFSG.SectionRank.not_sq_dvd_of_bound (B := 41) (by norm_num) (by norm_num) (by decide)
            P.hr P.hr2 hr3) h2
      exact (layer_not_dvd_card_center_of_not_sq_dvd P.hr hsq P.hrZ).elim
  · exact (not_dvd_card_center_of_J4 hJ4 P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  · exact (not_dvd_card_center_of_HS P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  · exact (not_dvd_card_center_of_He P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  · exact (not_dvd_card_center_of_Ru P.h₁.1 e P.hr P.hr2 P.hrZ).elim
  · by_cases hr3 : r = 3
    · subst hr3
      exact (not_three_dvd_card_center_of_McL P.he e P.hrZ).elim
    · exact (not_dvd_card_center_of_McL_ne_three P.h₁.1 e P.hr hr3 P.hrZ).elim

end Cases

theorem layerPairFull_of_short
    (hP : LayerPairFact) (hJ : LayerPairJ3) : LayerPairFull := by
  intro H _ _ he hK L₁ L₂ h₁ h₂ hne hφ r hr hr2 hrZ
  have P : Pair L₁ L₂ r := ⟨he, hK, h₁, h₂, hne, hφ, hr, hr2, hrZ⟩
  have hq : CFSG.IsQuasisimple ↥L₁ := h₁.1
  have hT : TableRestricted (↥L₁ ⧸ center ↥L₁) r := fun _ _ _ _ hm =>
    CoverB.tablePrime_of_dvd hq hm hr hr2 hrZ
  rcases CoverB.qtkSimpleList_of_cover he hq (hK.subgroup L₁) with
    ⟨n, hn5, hn9, ⟨e⟩⟩ | ⟨p, hp, -, h⟩ | h | h | ⟨s, hs, ⟨e⟩⟩
  · exact pair_alt hP P hn5 hn9 e
  · exact pair_odd hP P hT hp h
  · exact pair_even hP P hT h
  · exact pair_four P hT h
  · exact pair_sporadic hP hJ P hs e

end CFSG.SectionRank.QTK.CentreFact
