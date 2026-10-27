module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

set_option linter.unusedSectionVars false



private theorem i167COrth_label_isOmPA_aux1 {X : Type} [Group X] {P : GLALabel → Prop}
    (h : HasLabel X P) : ∃ lab : GLALabel, P lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem i167COrth_label_isOmPA_aux2 {lab : GLALabel} {n k : ℕ} (hn : 4 ≤ n)
    (hP : CFSG.StandardType.markTag lab = .POmegaPlus ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :
    canonLabel lab = ⟨.D, n, k⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem i167COrth_label_isOmPA_aux3 {lab : GLALabel} {k : ℕ}
    (hP : CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 4 ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :
    canonLabel lab = ⟨.A, 3, k⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem i167COrth_label_isOmPA_aux4 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    {n k : ℕ} (hk : 1 ≤ k) {i : TauCeti.CFSGIndex} (hi : isOmP n (2 ^ k) i)
    (e : X ⧸ Subgroup.center X ≃* i.Group) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      canonLabel lab = (if n = 3 then (⟨.A, 3, k⟩ : GLALabel) else ⟨.D, n, k⟩) := by
  unfold isOmP at hi
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating d hd => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | D r q =>
      simp only [onLie] at hi
      obtain ⟨hr, hqc⟩ := hi
      have hr4 : 4 ≤ r := by
        have hv' := (TauCeti.LieTypeIndex.valid_iff _).mp hv
        simpa using hv'.1
      obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk (hqc.trans (by norm_num))
      have hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 2 k := by
        simpa [h1, h2, hr] using CFSG.Models.lieModel_D r q hv e
      have hmB : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 2 k :=
        CFSG.Models.LieModel.toBlueprint (by decide) hm
      have hmark : HasLabel X (fun lab : GLALabel =>
          CFSG.StandardType.markTag lab = .POmegaPlus ∧ CFSG.StandardType.markRank lab = n ∧
            CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :=
        CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hmB
      obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isOmPA_aux1 hmark
      have hn3 : n ≠ 3 := by omega
      exact ⟨lab, hLab, by rw [if_neg hn3]; exact i167COrth_label_isOmPA_aux2 (by omega) hP⟩
    | _ => simp [onLie] at hi

private theorem i167COrth_label_isOmPA_aux5 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    {k : ℕ} (hk2 : 2 ≤ k) {i : TauCeti.CFSGIndex} (hi : isLnA 4 (2 ^ k) i)
    (e : X ⧸ Subgroup.center X ≃* i.Group) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ canonLabel lab = ⟨.A, 3, k⟩ := by
  unfold isLnA at hi
  rcases hi with hi | hs | hs | hs | hs
  · cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating d hd => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | A r q =>
        simp only [onLie, isLnEps] at hi
        obtain ⟨hr, hqc⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) (by omega) (hqc.trans (by norm_num))
        have hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .PSL 4 2 k := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        have hmB : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 4 2 k :=
          CFSG.Models.LieModel.toBlueprint (by decide) hm
        have hmark : HasLabel X (fun lab : GLALabel =>
            CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 4 ∧
              CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :=
          CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hmB
        obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isOmPA_aux1 hmark
        exact ⟨lab, hLab, i167COrth_label_isOmPA_aux3 hP⟩
      | _ => simp [onLie, isLnEps] at hi
  · omega
  · omega
  · omega
  · obtain ⟨-, hq, -⟩ := hs
    have hk1 : k = 1 := Nat.pow_right_injective (le_refl 2) (hq.trans (by norm_num : (2 : ℕ) = 2 ^ 1))
    omega

theorem i167COrth_label_isOmPA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n k : ℕ} (hn : 3 ≤ n)
    (hk : 1 ≤ k) (hk3 : n = 3 → 2 ≤ k) (h : catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k))) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      canonLabel lab = (if n = 3 then (⟨.A, 3, k⟩ : GLALabel) else ⟨.D, n, k⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmPA at hi
  rcases hi with hi | ⟨rfl, hi⟩
  · exact i167COrth_label_isOmPA_aux4 hq hk hi e
  · obtain ⟨lab, hLab, hcanon⟩ := i167COrth_label_isOmPA_aux5 hq (hk3 rfl) hi e
    exact ⟨lab, hLab, by simpa using hcanon⟩

private theorem i167COrth_label_isOmMA_aux1 {lab : GLALabel} {n k : ℕ} (hn : 4 ≤ n)
    (hP : CFSG.StandardType.markTag lab = .POmegaMinus ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :
    canonLabel lab = ⟨.twD, n, k⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
      CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem i167COrth_label_isOmMA_aux2 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    {n k : ℕ} (hn : 4 ≤ n) (hk : 1 ≤ k) {i : TauCeti.CFSGIndex} (hi : isOmM n (2 ^ k) i)
    (e : X ⧸ Subgroup.center X ≃* i.Group) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ canonLabel lab = ⟨.twD, n, k⟩ := by
  unfold isOmM at hi
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating d hd => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedD r q =>
      simp only [onLie] at hi
      obtain ⟨hr, hqc⟩ := hi
      obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk (hqc.trans (by norm_num))
      have hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .POmegaMinus n 2 k := by
        simpa [h1, h2, hr] using CFSG.Models.lieModel_twistedD r q hv e
      have hmB : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaMinus n 2 k :=
        CFSG.Models.LieModel.toBlueprint (by decide) hm
      have hmark : HasLabel X (fun lab : GLALabel =>
          CFSG.StandardType.markTag lab = .POmegaMinus ∧ CFSG.StandardType.markRank lab = n ∧
            CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :=
        CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hmB
      obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isOmPA_aux1 hmark
      exact ⟨lab, hLab, i167COrth_label_isOmMA_aux1 hn hP⟩
    | _ => simp [onLie] at hi

theorem i167COrth_label_isOmMA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n k : ℕ} (hn : 4 ≤ n)
    (hk : 1 ≤ k) (h : catalogIs (X ⧸ Subgroup.center X) (isOmMA n (2 ^ k))) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ canonLabel lab = (⟨.twD, n, k⟩ : GLALabel) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmMA at hi
  rcases hi with hi | ⟨hn3, hi⟩
  · exact i167COrth_label_isOmMA_aux2 hq hn hk hi e
  · omega

end CFSG.LocalAnalysis.GLTheoremA.I167

end
