module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.SeitzReduction.E8Pilot

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SeitzReduction.F4Pilot (idxA idxBC idxD idx2D profile_idxA profile_idxBC profile_idxD
  profile_idx2D idxA_le idxBC_le idxD_le idx2D_le profile_top_eq evenLieOrder
  mul_succ_eq_two_mul_div_two)
open CFSG.SeitzReduction.F4Pilot.EvenExc (le_mul_of_dvd_mul not_two_mul_dvd_self)

@[expose] def idxOrdE7 (f k : ℕ) : Prop :=
  k ∣ f * 18 ∨ k ∣ f * 14 ∨ k ∣ f * 12 ∨ k ∣ f * 10 ∨ k ∣ f * 8 ∨ k ∣ f * 6 ∨ k ∣ f * 2

theorem profile_e7 {f : ℕ} (hf : 1 ≤ f) : Profile (ordE7 (2 ^ f)) (f * 63) (idxOrdE7 f) :=
  F4Pilot.EvenExc.profile_ordE7' hf

theorem idxOrdE7_le {f k : ℕ} (hf : 1 ≤ f) (hk : idxOrdE7 f k) : k ≤ f * 18 := by
  rcases hk with h | h | h | h | h | h | h <;>
    exact le_mul_of_dvd_mul hf (by norm_num) (by norm_num) h

theorem e7_top {m N w f : ℕ} {Z : ℕ → Prop} (hf : 1 ≤ f) (h : Profile m N Z) (hw : Z w)
    (hle : ∀ k, Z k → k ≤ w) (hm : m = ordE7 (2 ^ f)) :
    N = f * 63 ∧ w = f * 18 ∧ ∀ k, 2 ≤ k → k ≠ 6 → (Z k ↔ idxOrdE7 f k) := by
  have hS := profile_e7 hf
  rw [← hm] at hS
  obtain ⟨hN, hw'⟩ := profile_top_eq hS h (w := f * 18) (Or.inl dvd_rfl) (by omega)
    (fun k hk => idxOrdE7_le hf hk) hw hle
  exact ⟨hN.symm, hw'.symm, fun k hk h6 => ((hS.transfer h).2 k hk h6).symm⟩

theorem ne_ordE7_of_profile {m N w f : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hw : Z w)
    (hle : ∀ k, Z k → k ≤ w) (hf : 1 ≤ f) (htop : N = f * 63 → w = f * 18 → False) :
    m ≠ ordE7 (2 ^ f) := fun hm => by
  obtain ⟨hN, hw', -⟩ := e7_top hf h hw hle hm
  exact htop hN hw'

theorem ordA_ne_ordE7 {m g f : ℕ} (hm : 1 ≤ m) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordA m (2 ^ g) ≠ ordE7 (2 ^ f) := by
  intro he
  have hX := profile_idxA hm hg
  have hT := mul_succ_eq_two_mul_div_two m
  obtain ⟨hN, hw, hZ⟩ := e7_top hf hX ⟨m + 1, by simp; omega, dvd_rfl⟩
    (fun k hk => idxA_le (by omega) hk) he
  generalize m * (m + 1) / 2 = T at hT hN
  have e1 : g * (m + 1) * m = g * (m + 1) * 7 := by
    calc g * (m + 1) * m = g * (m * (m + 1)) := by ring
      _ = 2 * (g * T) := by rw [hT]; ring
      _ = g * (m + 1) * 7 := by rw [hN, hw]; ring
  obtain rfl : m = 7 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
  have hrel : 9 * f = 4 * g := by omega
  have hk : idxA 7 g (g * 3) := ⟨3, by simp, dvd_rfl⟩
  rcases (hZ _ (by omega) (by omega)).mp hk with hd | hd | hd | hd | hd | hd | hd <;>
    · have := dvd_of_rel (by omega) hrel hd
      omega

theorem ordBC_ne_ordE7 {n g f : ℕ} (hn : 1 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordBC n (2 ^ g) ≠ ordE7 (2 ^ f) := by
  intro he
  have hX := profile_idxBC (n := n) hg
  obtain ⟨hN, hw, hZ⟩ := e7_top hf hX ⟨n, by simp; omega, dvd_rfl⟩
    (fun k hk => idxBC_le (by omega) hk) he
  have h1 : g * n = f * 9 := by
    have : g * (2 * n) = 2 * (g * n) := by ring
    omega
  have e1 : g * n * n = g * n * 7 := by
    calc g * n * n = g * (n * n) := by ring
      _ = g * n * 7 := by rw [hN, h1]; ring
  obtain rfl : n = 7 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
  have hrel : 9 * f = 7 * g := by omega
  have hk : idxBC 7 g (g * (2 * 6)) := ⟨6, by simp, dvd_rfl⟩
  rcases (hZ _ (by omega) (by omega)).mp hk with hd | hd | hd | hd | hd | hd | hd <;>
    · have := dvd_of_rel (by omega) hrel hd
      omega

theorem ordD_ne_ordE7 {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordD n (2 ^ g) ≠ ordE7 (2 ^ f) := by
  intro he
  have hX := profile_idxD (by omega : 1 ≤ n) hg
  obtain ⟨hN, hw, hZ⟩ := e7_top hf hX (Or.inr ⟨n - 1, by simp; omega, dvd_rfl⟩)
    (fun k hk => idxD_le (by omega) (by omega) hk) he
  have h1 : g * (n - 1) = f * 9 := by
    have : g * (2 * (n - 1)) = 2 * (g * (n - 1)) := by ring
    omega
  have e1 : g * (n - 1) * n = g * (n - 1) * 7 := by
    calc g * (n - 1) * n = g * (n * (n - 1)) := by ring
      _ = g * (n - 1) * 7 := by rw [hN, h1]; ring
  obtain rfl : n = 7 := Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hg (by omega)) e1
  have hrel : 3 * f = 2 * g := by omega
  have hk : idxD 7 g (g * 7) := Or.inl dvd_rfl
  rcases (hZ _ (by omega) (by omega)).mp hk with hd | hd | hd | hd | hd | hd | hd <;>
    · have := dvd_of_rel (by omega) hrel hd
      omega

theorem ordTwistedD_ne_ordE7 {n g f : ℕ} (hn : 4 ≤ n) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedD n (2 ^ g) ≠ ordE7 (2 ^ f) := by
  intro he
  have hX := profile_idx2D (by omega : 1 ≤ n) hg
  have hgn : 0 < g * n := Nat.mul_pos (by omega) (by omega)
  obtain ⟨hN, hw, hZ⟩ := e7_top hf hX
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd hgn h; omega⟩)
    (fun k hk => idx2D_le (by omega) (by omega) hk) he
  have h1 : g * n = f * 9 := by omega
  have e1 : g * n * (n - 1) = g * n * 7 := by
    calc g * n * (n - 1) = g * (n * (n - 1)) := by ring
      _ = g * n * 7 := by rw [hN, h1]; ring
  have hn8 : n - 1 = 7 := Nat.eq_of_mul_eq_mul_left hgn e1
  obtain rfl : n = 8 := by omega
  have hrel : 9 * f = 8 * g := by omega
  have hk : idx2D 8 g (g * (2 * 3)) := Or.inr ⟨3, by simp, dvd_rfl⟩
  rcases (hZ _ (by omega) (by omega)).mp hk with hd | hd | hd | hd | hd | hd | hd <;>
    · have := dvd_of_rel (by omega) hrel hd
      omega

theorem ordTwistedA_ne_ordE7 {u g f : ℕ} (hu : 2 ≤ u) (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedA u (2 ^ g) ≠ ordE7 (2 ^ f) :=
  fun h => ordE7_ne_ordTwistedA hf hu hg h.symm

theorem ordG2_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordG2 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordG2' hg) (w := g * 6) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h <;> exact le_mul_of_dvd_mul hg (by norm_num) (by norm_num) h)
    hf (fun h1 h2 => by omega)

theorem ordF4_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordF4 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordF4' hg) (w := g * 12) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h <;> exact le_mul_of_dvd_mul hg (by norm_num) (by norm_num) h)
    hf (fun h1 h2 => by omega)

theorem ordE6_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordE6 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordE6' hg) (w := g * 12) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h <;>
        exact le_mul_of_dvd_mul hg (by norm_num) (by norm_num) h)
    hf (fun h1 h2 => by omega)

theorem ordTwistedE6_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedE6 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordTwistedE6' hg) (w := 2 * (g * 9))
    (Or.inr (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩))
    (fun k hk => by
      rcases hk with h | ⟨h, -⟩ | h | h | ⟨h, -⟩ | h
      · exact (le_mul_of_dvd_mul hg (by norm_num) (le_refl 12) h).trans (by omega)
      · exact Nat.le_of_dvd (by omega) h
      · exact (le_mul_of_dvd_mul hg (by norm_num) (le_refl 8) h).trans (by omega)
      · exact (le_mul_of_dvd_mul hg (by norm_num) (le_refl 6) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact (le_mul_of_dvd_mul hg (by norm_num) (le_refl 2) h).trans (by omega))
    hf (fun h1 h2 => by omega)

theorem ordE8_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) : ordE8 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordE8' hg) (w := g * 30) (Or.inl dvd_rfl)
    (fun k hk => by
      rcases hk with h | h | h | h | h | h | h | h <;>
        exact le_mul_of_dvd_mul hg (by norm_num) (by norm_num) h)
    hf (fun h1 h2 => by omega)

theorem ordTrialityD4_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTrialityD4 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordTrialityD4' hg) (w := g * 12)
    (Or.inl ⟨dvd_rfl, fun h => by have := Nat.le_of_dvd (by omega) h; omega⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | h <;> exact le_mul_of_dvd_mul hg (by norm_num) (by norm_num) h)
    hf (fun h1 h2 => by omega)

theorem ordSuzuki_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordSuzuki (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordSuzuki' hg) (w := 2 * (g * 2))
    (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (fun h1 h2 => by omega)

theorem ordTwistedF4_ne_ordE7 {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) :
    ordTwistedF4 (2 ^ g) ≠ ordE7 (2 ^ f) :=
  ne_ordE7_of_profile (F4Pilot.EvenExc.profile_ordTwistedF4' hg) (w := 2 * (g * 6))
    (Or.inl ⟨dvd_rfl, not_two_mul_dvd_self (by omega)⟩)
    (fun k hk => by
      rcases hk with ⟨h, -⟩ | h | ⟨h, -⟩ | h
      · exact Nat.le_of_dvd (by omega) h
      · exact (le_mul_of_dvd_mul hg (by norm_num) (le_refl 4) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega)
      · exact (Nat.le_of_dvd (by omega) h).trans (by omega))
    hf (fun h1 h2 => by omega)

theorem ordTits_ne_ordE7 {f : ℕ} (hf : 1 ≤ f) : ordTits ≠ ordE7 (2 ^ f) := by
  rw [ordTits_eq]
  exact fun h => (profile_e7 hf).ne_of_ne (by decide) (by omega) h.symm

theorem eq_of_ordE7_eq {g f : ℕ} (hg : 1 ≤ g) (hf : 1 ≤ f) (h : ordE7 (2 ^ g) = ordE7 (2 ^ f)) :
    g = f := by
  have h1 := profile_e7 hg
  rw [h] at h1
  have := ((profile_e7 hf).transfer h1).1
  omega

theorem evenLieOrder_eq_ordE7 {t : StatedLieTag} {n g f : ℕ}
    (hadm : StatedLieAdmissible t n 2 g) (hf : 1 ≤ f)
    (h : evenLieOrder t n g = ordE7 (2 ^ f)) : t = .E7 ∧ n = 0 ∧ g = f := by
  obtain ⟨-, hg, ht⟩ := hadm
  cases t
  case PSL => exact absurd h (ordA_ne_ordE7 (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case PSU => exact absurd h (ordTwistedA_ne_ordE7 (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case PSp => exact absurd h (ordBC_ne_ordE7 (by obtain ⟨hn, -⟩ := ht; omega) hg hf)
  case POmegaOdd => exact absurd rfl ht.2
  case POmegaPlus => exact absurd h (ordD_ne_ordE7 ht hg hf)
  case POmegaMinus => exact absurd h (ordTwistedD_ne_ordE7 ht hg hf)
  case G2 => exact absurd h (ordG2_ne_ordE7 hg hf)
  case F4 => exact absurd h (ordF4_ne_ordE7 hg hf)
  case E6 => exact absurd h (ordE6_ne_ordE7 hg hf)
  case E7 => exact ⟨rfl, ht, eq_of_ordE7_eq hg hf h⟩
  case E8 => exact absurd h (ordE8_ne_ordE7 hg hf)
  case twistedE6 => exact absurd h (ordTwistedE6_ne_ordE7 hg hf)
  case trialityD4 => exact absurd h (ordTrialityD4_ne_ordE7 hg hf)
  case twistedB2 => exact absurd h (ordSuzuki_ne_ordE7 hg hf)
  case twistedG2 => exact absurd ht.2.1 (by norm_num)
  case twistedF4 => exact absurd h (ordTwistedF4_ne_ordE7 hg hf)
  case Tits => exact absurd h (ordTits_ne_ordE7 hf)

theorem eq_zero_one_le_of_lieModel_E7 {X : Type} [Group X] {n f : ℕ} (h : LieModel X .E7 n 2 f) :
    n = 0 ∧ 1 ≤ f := by
  have hadm := F4Pilot.statedLieAdmissible_of_lieModel h
  exact ⟨hadm.2.2, hadm.2.1⟩

theorem isSimpleGroup_of_lieModel_E7
    {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .E7 n p f) : IsSimpleGroup X :=
  (LieType.Simplicity.fam_e7_simplicity X p f
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)).2

section Orders


theorem card_of_lieModel_E7_two {X : Type} [Group X] {n f : ℕ} (h : LieModel X .E7 n 2 f) :
    Nat.card X = ordE7 (2 ^ f) :=
  Timmesfeld.card_chevalleyExceptionalModel_two
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) h)

theorem lieModel_E7_two_unique_classicalOrSuzuki_of_card_eq {X Y : Type} [Group X] [Group Y]
    {f : ℕ} (h7 : LieModel X .E7 0 2 f) {t : StatedLieTag} {n f' : ℕ}
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .E7 ∧ n = 0 ∧ f' = f := by
  refine evenLieOrder_eq_ordE7 (F4Pilot.statedLieAdmissible_of_lieModel h)
    (eq_zero_one_le_of_lieModel_E7 h7).2 ?_
  rw [← F4Pilot.card_eq_evenLieOrder_of_classicalOrSuzuki ht h, hcard,
    card_of_lieModel_E7_two h7]

theorem not_lieModel_classicalOrSuzuki_of_card_eq_E7 {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h7 : LieModel X .E7 0 2 f) {t : StatedLieTag} {n f' : ℕ}
    (ht : t ∈ classicalTags ∨ t = .twistedB2) (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : False := by
  obtain ⟨rfl, -, -⟩ := lieModel_E7_two_unique_classicalOrSuzuki_of_card_eq h7 ht h hcard
  rcases ht with ht | ht
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)


theorem lieModel_E7_two_unique_of_card_eq {X Y : Type} [Group X] [Group Y] {f : ℕ}
    (h7 : LieModel X .E7 0 2 f) {t : StatedLieTag} {n f' : ℕ} (h : LieModel Y t n 2 f')
    (hcard : Nat.card Y = Nat.card X) : t = .E7 ∧ n = 0 ∧ f' = f := by
  refine evenLieOrder_eq_ordE7 (F4Pilot.statedLieAdmissible_of_lieModel h)
    (eq_zero_one_le_of_lieModel_E7 h7).2 ?_
  rw [← F4Pilot.card_eq_evenLieOrder h, hcard, card_of_lieModel_E7_two h7]

theorem lieModel_E7_two_unique {X : Type} [Group X] {f : ℕ} (h7 : LieModel X .E7 0 2 f)
    {t : StatedLieTag} {n f' : ℕ} (h : LieModel X t n 2 f') : t = .E7 ∧ n = 0 ∧ f' = f :=
  lieModel_E7_two_unique_of_card_eq h7 h rfl

end Orders

end CFSG.SeitzReduction.E8Pilot
