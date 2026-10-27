module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExcOrders

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem ordG2_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordG2 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordG2' hg) (w := g * 6) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordTrialityD4_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordTrialityD4' hg) (w := g * 12)
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordF4_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordF4 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordF4' hg) (w := g * 12) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordE6_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordE6 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordE6' hg) (w := g * 12) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordTwistedE6_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordTwistedE6' hg) (w := 2 * (g * 9))
    (Or.inr (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordE7_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordE7 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordE7' hg) (w := g * 18) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordE8_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordE8 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordE8' hg) (w := g * 30) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordSuzuki_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordSuzuki' hg) (w := 2 * (g * 2))
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h <;> exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordTwistedF4_ne_ordA_five {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ g) ≠ ordA 5 (2 ^ f) :=
  ne_ordA_five_of_profile (EvenExc.profile_ordTwistedF4' hg) (w := 2 * (g * 6))
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h <;>
        exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (by omega) (fun e _ h1 h2 => by omega)

theorem ordTits_ne_ordA_five {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordA 5 (2 ^ f) := by
  rw [ordTits_eq]
  exact fun h => (profile_l6 hf).ne_of_ne (by decide) (by omega) h.symm

@[expose] def evenLieOrder : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, f => ordA (n - 1) (2 ^ f)
  | .PSU, n, f => ordTwistedA (n - 1) (2 ^ f)
  | .PSp, n, f => ordBC n (2 ^ f)
  | .POmegaOdd, n, f => ordBC n (2 ^ f)
  | .POmegaPlus, n, f => ordD n (2 ^ f)
  | .POmegaMinus, n, f => ordTwistedD n (2 ^ f)
  | .G2, _, f => ordG2 (2 ^ f)
  | .F4, _, f => ordF4 (2 ^ f)
  | .E6, _, f => ordE6 (2 ^ f)
  | .E7, _, f => ordE7 (2 ^ f)
  | .E8, _, f => ordE8 (2 ^ f)
  | .twistedE6, _, f => ordTwistedE6 (2 ^ f)
  | .trialityD4, _, f => ordTrialityD4 (2 ^ f)
  | .twistedB2, _, f => ordSuzuki (2 ^ f)
  | .twistedG2, _, f => ordRee (2 ^ f)
  | .twistedF4, _, f => ordTwistedF4 (2 ^ f)
  | .Tits, _, _ => ordTits

theorem two_le_of_admissible_G2 {n g : ℕ} (hadm : StatedLieAdmissible .G2 n 2 g) : 2 ≤ g := by
  obtain ⟨-, hg, -, hq⟩ := hadm
  rcases Nat.lt_or_ge g 2 with h | h
  · obtain rfl : g = 1 := by omega
    norm_num at hq
  · exact h

theorem evenLieOrder_eq_ordBC_three {t : StatedLieTag} {n g f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hf : 1 ≤ f)
    (h : evenLieOrder t n g = ordBC 3 (2 ^ f)) : t = .PSp ∧ n = 3 ∧ g = f := by
  have hG2 : t = .G2 → 2 ≤ g := fun ht => two_le_of_admissible_G2 (ht ▸ hadm)
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL => exact absurd h (ordA_ne_ordBC_three (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case PSU => exact absurd h (ordTwistedA_ne_ordBC_three (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case PSp =>
    obtain ⟨rfl, rfl⟩ := ordBC_eq_ordBC_three ht.1 hg hf h
    exact ⟨rfl, rfl, rfl⟩
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordBC_three ht hg hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordBC_three ht hg hf)
  case G2 => exact absurd h (EvenExc.ordG2_ne_ordBC_three (hG2 rfl) hf)
  case F4 => exact absurd h (EvenExc.ordF4_ne_ordBC_three hg hf)
  case E6 => exact absurd h (EvenExc.ordE6_ne_ordBC_three hg hf)
  case E7 => exact absurd h (EvenExc.ordE7_ne_ordBC_three hg hf)
  case E8 => exact absurd h (EvenExc.ordE8_ne_ordBC_three hg hf)
  case twistedE6 => exact absurd h (EvenExc.ordTwistedE6_ne_ordBC_three hg hf)
  case trialityD4 => exact absurd h (EvenExc.ordTrialityD4_ne_ordBC_three hg hf)
  case twistedB2 => exact absurd h (EvenExc.ordSuzuki_ne_ordBC_three hg hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (EvenExc.ordTwistedF4_ne_ordBC_three hg hf)
  case Tits => exact absurd h (EvenExc.ordTits_ne_ordBC_three hf)

theorem evenLieOrder_eq_ordA_five {t : StatedLieTag} {n g f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hf : 1 ≤ f)
    (h : evenLieOrder t n g = ordA 5 (2 ^ f)) : t = .PSL ∧ n = 6 ∧ g = f := by
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := ht
    obtain ⟨h1, rfl⟩ := ordA_eq_ordA_five (by omega) hg hf h
    exact ⟨rfl, by omega, rfl⟩
  case PSU => exact absurd h (ordTwistedA_ne_ordA_five (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case PSp => exact absurd h (ordBC_ne_ordA_five ht.1 hg hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordA_five ht hg hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordA_five ht hg hf)
  case G2 => exact absurd h (ordG2_ne_ordA_five hg hf)
  case F4 => exact absurd h (ordF4_ne_ordA_five hg hf)
  case E6 => exact absurd h (ordE6_ne_ordA_five hg hf)
  case E7 => exact absurd h (ordE7_ne_ordA_five hg hf)
  case E8 => exact absurd h (ordE8_ne_ordA_five hg hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordA_five hg hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordA_five hg hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordA_five hg hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordA_five hg hf)
  case Tits => exact absurd h (ordTits_ne_ordA_five hf)

theorem statedLieAdmissible_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : LieModel X t n p f) : StatedLieAdmissible t n p f :=
  CFSG.Blueprint.LieModel.admissible h

theorem not_lieModel_POmegaOdd_two {X : Type} [Group X] {n f : ℕ} :
    ¬ LieModel X .POmegaOdd n 2 f :=
  fun h => (statedLieAdmissible_of_lieModel h).2.2.2 rfl

theorem not_lieModel_twistedG2_two {X : Type} [Group X] {n f : ℕ} :
    ¬ LieModel X .twistedG2 n 2 f :=
  fun h => absurd (statedLieAdmissible_of_lieModel h).2.2.2.1 (by norm_num)

theorem card_eq_evenLieOrder_of_mem_classicalTags {X : Type} [Group X] {t : StatedLieTag}
    {n f : ℕ} (ht : t ∈ classicalTags) (h : LieModel X t n 2 f) :
    Nat.card X = evenLieOrder t n f := by
  have hadm := statedLieAdmissible_of_lieModel h
  cases t
  case PSL => exact GH74.card_of_lieModel_PSL (by obtain ⟨-, -, hn, -⟩ := hadm; omega) h
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact (Timmesfeld.card_statedClassicalModel_two
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.1 rfl
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    exact (Timmesfeld.card_statedClassicalModel_two
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.1 rfl
  case POmegaOdd => exact absurd rfl hadm.2.2.2
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact (Timmesfeld.card_statedClassicalModel_two
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.2.1 rfl
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact (Timmesfeld.card_statedClassicalModel_two
      (GH74.statedClassicalModel_of_lieModel (by omega) h)).2.2.2.2 rfl
  all_goals exact absurd ht (by decide)

theorem card_eq_evenLieOrder_of_classicalOrSuzuki {X : Type}
    [Group X] {t : StatedLieTag} {n f : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2)
    (h : LieModel X t n 2 f) : Nat.card X = evenLieOrder t n f := by
  rcases ht with ht | rfl
  · exact card_eq_evenLieOrder_of_mem_classicalTags ht h
  · rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, hrt, -⟩ | ⟨-, -, hsz⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact absurd hrt (by decide)
    · obtain ⟨-, -, -, -, hc⟩ := GH74.card_of_suzukiModel hsz
      exact hc

theorem lieModel_PSp_three_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {f : ℕ} (h6 : LieModel X .PSp 3 2 f) {t : StatedLieTag}
    {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSp ∧ n = 3 ∧ f' = f := by
  refine evenLieOrder_eq_ordBC_three (statedLieAdmissible_of_lieModel h)
    (statedLieAdmissible_of_lieModel h6).2.1 ?_
  rw [← card_eq_evenLieOrder_of_classicalOrSuzuki ht h, hcard,
    card_eq_evenLieOrder_of_mem_classicalTags (by decide) h6]
  rfl

theorem lieModel_PSp_three_two_unique_classicalOrSuzuki
    (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ)
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h6 : LieModel X .PSp 3 2 f)
    (_hadm : StatedLieAdmissible t n 2 f') (h : LieModel X t n 2 f') :
    t = .PSp ∧ n = 3 ∧ f' = f :=
  lieModel_PSp_three_two_unique_classicalOrSuzuki_of_card_eq h6 ht h rfl

theorem lieModel_PSL_six_two_unique_classicalOrSuzuki_of_card_eq
    {X Y : Type} [Group X] [Group Y] {f : ℕ} (h6 : LieModel X .PSL 6 2 f) {t : StatedLieTag}
    {n f' : ℕ} (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSL ∧ n = 6 ∧ f' = f := by
  refine evenLieOrder_eq_ordA_five (statedLieAdmissible_of_lieModel h)
    (statedLieAdmissible_of_lieModel h6).2.1 ?_
  rw [← card_eq_evenLieOrder_of_classicalOrSuzuki ht h, hcard,
    card_eq_evenLieOrder_of_mem_classicalTags (by decide) h6]
  rfl

theorem lieModel_PSL_six_two_unique_classicalOrSuzuki
    (X : Type) [Group X] (f : ℕ) (t : StatedLieTag) (n f' : ℕ)
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h6 : LieModel X .PSL 6 2 f)
    (_hadm : StatedLieAdmissible t n 2 f') (h : LieModel X t n 2 f') :
    t = .PSL ∧ n = 6 ∧ f' = f :=
  lieModel_PSL_six_two_unique_classicalOrSuzuki_of_card_eq h6 ht h rfl

section Orders


theorem card_eq_evenLieOrder {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) : Nat.card X = evenLieOrder t n f := by
  have hadm := statedLieAdmissible_of_lieModel h
  cases t
  case G2 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case F4 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case E6 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case E7 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case E8 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case twistedE6 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case trialityD4 =>
    exact Timmesfeld.card_chevalleyExceptionalModel_two
      (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)
  case twistedB2 => exact card_eq_evenLieOrder_of_classicalOrSuzuki (Or.inr rfl) h
  case twistedG2 => exact absurd hadm.2.2.2.1 (by norm_num)
  case twistedF4 =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact EvenExc.card_of_reeTitsModel_twistedF4' hrt
    · exact absurd hsz (by decide)
  case Tits =>
    rcases h with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, hrt⟩ | ⟨-, hsz, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact EvenExc.card_of_reeTitsModel_tits hrt
    · exact absurd hsz (by decide)
  all_goals exact card_eq_evenLieOrder_of_mem_classicalTags (by decide) h

theorem lieModel_PSp_three_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h6 : LieModel X .PSp 3 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSp ∧ n = 3 ∧ f' = f := by
  refine evenLieOrder_eq_ordBC_three (statedLieAdmissible_of_lieModel h)
    (statedLieAdmissible_of_lieModel h6).2.1 ?_
  rw [← card_eq_evenLieOrder h, hcard, card_eq_evenLieOrder h6]
  rfl

theorem lieModel_PSp_three_two_unique {X : Type} [Group X] {f : ℕ}
    (h6 : LieModel X .PSp 3 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel X t n 2 f') :
    t = .PSp ∧ n = 3 ∧ f' = f :=
  lieModel_PSp_three_two_unique_of_card_eq h6 h rfl

theorem lieModel_PSL_six_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h6 : LieModel X .PSL 6 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .PSL ∧ n = 6 ∧ f' = f := by
  refine evenLieOrder_eq_ordA_five (statedLieAdmissible_of_lieModel h)
    (statedLieAdmissible_of_lieModel h6).2.1 ?_
  rw [← card_eq_evenLieOrder h, hcard, card_eq_evenLieOrder h6]
  rfl

theorem lieModel_PSL_six_two_unique {X : Type} [Group X] {f : ℕ}
    (h6 : LieModel X .PSL 6 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel X t n 2 f') :
    t = .PSL ∧ n = 6 ∧ f' = f :=
  lieModel_PSL_six_two_unique_of_card_eq h6 h rfl

end Orders

end CFSG.SeitzReduction.F4Pilot
