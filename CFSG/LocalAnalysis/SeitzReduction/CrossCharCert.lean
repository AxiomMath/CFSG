module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatOdd
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2Odd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatInputs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatOdd

public section

namespace CFSG.SeitzReduction.CrossChar

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Open CFSG.ComponentClassification.CatLeaf

section NoTits

theorem card_eq_lieOrder_of_ne_Tits {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (h : LieModel X t n p f) (hT : t ≠ .Tits) :
    Nat.card X = lieOrderNumerator t n (p ^ f) / lieOrderDivisor t n (p ^ f) := by
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    rw [GH74.card_of_lieModel_PSL (by omega) h, ordA, Nat.sub_add_cancel (by omega : 1 ≤ n),
      mul_comm (n - 1) n]
    rfl
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hc : Nat.card X = ordTwistedA (n - 1) (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two
          (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.1 rfl
      · exact GH74.card_of_lieModel_PSU (by omega) hp2 h
    rw [hc, ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm (n - 1) n,
      Finset.prod_congr rfl fun i _ =>
        ComponentClassification.CatLeafProof.toNat_pow_sub_neg_one_pow
          (Nat.one_le_pow _ _ hp.pos) i]
    rfl
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have hc : Nat.card X = ordBC n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two
          (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.1 rfl
      · exact GH74.card_of_lieModel_PSp (by omega) hp2 h
    rw [hc, ordBC, ← sq]
    rfl
  case POmegaOdd =>
    obtain ⟨-, -, hn, hp2⟩ := hadm
    have hc := (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.2.1 rfl
    have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
    rw [hc, ordBC, ClassicalInvolution.gcd_two_sub_one_of_odd hodd, ← sq]
    rfl
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hsc := GH74.statedClassicalModel_of_lieModel (by omega) h
    have hc : Nat.card X = ordD n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.1 rfl
      · exact (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.1 rfl
    rw [hc, ordD]
    rfl
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    have hsc := GH74.statedClassicalModel_of_lieModel (by omega) h
    have hc : Nat.card X = ordTwistedD n (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact (Timmesfeld.card_statedClassicalModel_two hsc).2.2.2.2 rfl
      · exact (ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hsc).2.2.2.2.2 rfl
    rw [hc, ordTwistedD]
    rfl
  case G2 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).1 rfl, ordG2]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case F4 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.1 rfl, ordF4]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case E6 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.1 rfl, ordE6]
    rfl
  case E7 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.2.1 rfl, ordE7]
    rfl
  case E8 =>
    rw [(Timmesfeld.card_chevalleyExceptionalModel_untwisted
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2.2.2.2 rfl, ordE8]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedE6 =>
    rw [ClassicalInvolution.card_of_twistedChevalleyModel_E6 hp hf
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h).2, ordTwistedE6]
    rfl
  case trialityD4 =>
    have hce := GH74.chevalleyExceptionalModel_of_lieModel (by decide) h
    have hc : Nat.card X = ordTrialityD4 (p ^ f) := by
      by_cases hp2 : p = 2
      · subst hp2
        exact Timmesfeld.card_chevalleyExceptionalModel_two hce
      · exact ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 hce
    rw [hc, ordTrialityD4]
    simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedB2 =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact absurd hrt (by decide)
    · obtain ⟨rfl, -, -, -, hc⟩ := GH74.card_of_suzukiModel hsz
      rw [hc, ordSuzuki]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
  case twistedG2 =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · obtain ⟨rfl, -, -, -, hc⟩ := ClassicalInvolution.card_of_reeTitsModel_twistedG2 hrt
      rw [hc, ordRee]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
    · exact absurd hsz (by decide)
  case twistedF4 =>
    obtain ⟨-, -, -, rfl, -, -⟩ := hadm
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · rw [ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 hrt, ordTwistedF4]
      simp only [lieOrderNumerator, lieOrderDivisor, Nat.div_one]
    · exact absurd hsz (by decide)
  case Tits => exact absurd rfl hT

theorem card_mul_lieOrderDivisor_of_ne_Tits {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) (h : LieModel X t n p f) (hT : t ≠ .Tits) :
    Nat.card X * lieOrderDivisor t n (p ^ f) = lieOrderNumerator t n (p ^ f) := by
  rw [card_eq_lieOrder_of_ne_Tits hadm h hT,
    Nat.div_mul_cancel (ComponentClassification.CatLeafProof.lieOrderDivisor_dvd_numerator hadm)]

theorem eq_of_lieModel_two_of_oddLieType_of_ne_Tits {X : Type} [Group X] {t : StatedLieTag}
    {n f : ℕ} (hX : LieModel X t n 2 f) (hT : t ≠ .Tits) (hodd : OddLieType X) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) := by
  have hadm := statedLieAdmissible_of_lieModel hX
  obtain ⟨t', n', p, g, -, hp2, hadm', hY⟩ := hodd
  have hT' : t' ≠ .Tits := by
    rintro rfl
    exact hp2 hadm'.2.2.2.1
  exact eq_of_crossChar_arith (crossChar_arith hadm hadm' hp2
    (card_mul_lieOrderDivisor_of_ne_Tits hadm hX hT)
    (card_mul_lieOrderDivisor_of_ne_Tits hadm' hY hT'))

theorem not_oddLieType_of_lieModel_two_of_ne_Tits {X : Type} [Group X] {t : StatedLieTag}
    {n f : ℕ} (hX : LieModel X t n 2 f) (hT : t ≠ .Tits) (h1 : ¬ (t = .PSL ∧ n = 2 ∧ f = 2))
    (h2 : ¬ (t = .PSL ∧ n = 3 ∧ f = 1)) (h3 : ¬ (t = .PSU ∧ n = 4 ∧ f = 1)) : ¬ OddLieType X :=
  fun hodd => by
    rcases eq_of_lieModel_two_of_oddLieType_of_ne_Tits hX hT hodd with h | h | h
    exacts [h1 h, h2 h, h3 h]

theorem sLmNotOddLieInputAt {m : ℕ} (hm : m ≠ 2) : LinearPilot.SLmNotOddLieInputAt m := by
  intro X _ f hmf hX
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide) (fun h => hm h.2.1)
    (fun h => hmf (by rw [h.2.1, h.2.2])) (fun h => absurd h.1 (by decide))

theorem sLmNotOddLieInput : LinearPilot.SLmNotOddLieInput :=
  fun _ hm => sLmNotOddLieInputAt (by omega)

theorem sUmNotOddLieInputAt (m : ℕ) : UnitaryPilot.SUmNotOddLieInputAt m := by
  intro X _ f hmf hX
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide)
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
    (fun h => hmf (by rw [h.2.1, h.2.2]))

theorem sp2mNotOddLieInput (m : ℕ) : SymplecticPilot.Sp2mNotOddLieInput m := by
  intro X _ f hX
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide)
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide))

theorem sp6NotOddLieInput : F4Pilot.Sp6NotOddLieInput :=
  sp2mNotOddLieInput 3

theorem omegaNotOddLieInputAt (m : ℕ) : OmegaPilot.OmegaNotOddLieInputAt m := by
  intro X _ t f ht hX
  have hPSL : t ≠ .PSL := by rcases ht with rfl | rfl <;> decide
  have hPSU : t ≠ .PSU := by rcases ht with rfl | rfl <;> decide
  have hTits : t ≠ .Tits := by rcases ht with rfl | rfl <;> decide
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX hTits (fun h => hPSL h.1)
    (fun h => hPSL h.1) (fun h => hPSU h.1)

theorem e7NotOddLieInput : E8Pilot.E7NotOddLieInput := by
  intro X _ f hX
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide)
    (fun h => absurd h.1 (by decide)) (fun h => absurd h.1 (by decide))
    (fun h => absurd h.1 (by decide))

theorem sL2NotOddLieInputAt {n : ℕ} (hn : n ≠ 2) : RankOne.SL2NotOddLieInputAt n := by
  intro X _ hX
  exact not_oddLieType_of_lieModel_two_of_ne_Tits hX (by decide) (fun h => hn h.2.2)
    (fun h => by omega) (fun h => absurd h.1 (by decide))

end NoTits

section AllTags

theorem eq_of_lieModel_two_of_oddLieType' {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hX : LieModel X t n 2 f) (hodd : OddLieType X) :
    (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) :=
  eq_of_lieModel_two_of_oddLieType ComponentClassification.CatLeafProof.lieOrderFormulasInput hX
    hodd

end AllTags

end CFSG.SeitzReduction.CrossChar
