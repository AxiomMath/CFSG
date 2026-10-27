module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

set_option linter.unusedSectionVars false



private theorem i167COrth_label_isLnA_aux1 {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    (h : catalogIs S (isLnA n 2)) : CFSG.Blueprint.LieModel S .PSL n 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
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
        obtain ⟨hr, hq⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
          (hq.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .PSL n 2 1 := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        exact CFSG.Models.LieModel.toBlueprint (by decide) hm
      | _ => simp [onLie, isLnEps] at hi
  · omega
  · omega
  · omega
  · omega

private theorem i167COrth_label_isLnA_aux2 {lab : GLALabel} {n : ℕ} (hn : 5 ≤ n)
    (hP : CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :
    canonLabel lab = (⟨.A, n - 1, 1⟩ : GLALabel) := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem i167COrth_label_isLnA_aux3 {X : Type} [Group X] {P : GLALabel → Prop}
    (h : HasLabel X P) : ∃ lab : GLALabel, P lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

theorem i167COrth_label_isLnA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hn : 5 ≤ n)
    (h : catalogIs (X ⧸ Subgroup.center X) (isLnA n 2)) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ canonLabel lab = (⟨.A, n - 1, 1⟩ : GLALabel) := by
  have hm := i167COrth_label_isLnA_aux1 hn h
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = n ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
  obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isLnA_aux3 hmark
  exact ⟨lab, hLab, i167COrth_label_isLnA_aux2 hn hP⟩

private theorem i167COrth_label_isUnA_aux1 {S : Type} [Group S] {m f : ℕ} (hf : 1 ≤ f)
    {i : TauCeti.CFSGIndex} (hi : onLie (isLnEps m (2 ^ f) false) i) (e : S ≃* i.Group) :
    CFSG.Blueprint.LieModel S .PSU m 2 f := by
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating d hd => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedA r q =>
      simp only [onLie, isLnEps] at hi
      obtain ⟨hr, hq⟩ := hi
      obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := f) hf hq
      have hm : CFSG.Models.LieModel S .PSU m 2 f := by
        simpa [h1, h2, hr] using lieModel_twistedA' r q hv e
      exact CFSG.Models.LieModel.toBlueprint (by decide) hm
    | _ => simp [onLie, isLnEps] at hi

private theorem i167COrth_label_isUnA_aux2 {lab : GLALabel} {m f : ℕ} (hm : 3 ≤ m) (hf : 1 ≤ f)
    (hP : CFSG.StandardType.markTag lab = .PSU ∧ CFSG.StandardType.markRank lab = m ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f) :
    canonLabel lab = (⟨.twA, m - 1, f⟩ : GLALabel) := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem i167COrth_label_isUnA_aux3 {S : Type} [Group S] {f : ℕ} (hf : 1 ≤ f)
    (h : catalogIs S (isLnA 2 (2 ^ f))) : CFSG.Blueprint.LieModel S .PSL 2 2 f := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isLnA at hi
  rcases hi with hi | ⟨-, hq, hi⟩ | ⟨-, hq, hi⟩ | ⟨h3, -⟩ | ⟨h4, -⟩
  · cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating d hd => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | A r q =>
        simp only [onLie, isLnEps] at hi
        obtain ⟨hr, hq⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := f) hf hq
        have hm : CFSG.Models.LieModel S .PSL 2 2 f := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        exact CFSG.Models.LieModel.toBlueprint (by decide) hm
      | _ => simp [onLie, isLnEps] at hi
  · rcases hq with hq | hq
    · have hf2 : f = 2 := Nat.pow_right_injective (le_refl 2) (hq.trans (by norm_num))
      subst hf2
      cases i with
      | cyclic p hp => simp [isAltN] at hi
      | alternating d hd =>
        have hd5 : d = 5 := hi
        subst hd5
        exact CFSG.StandardType.ChevTwo.lieModel_psl_two_four_of_alternating_five e
      | sporadic s => simp [isAltN] at hi
      | lie idx => simp [isAltN] at hi
    · have hf2 : f ≤ 2 := by
        by_contra h
        have h3 : 3 ≤ f := by omega
        have h8 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
        omega
      interval_cases f <;> norm_num at hq
  · have hf3 : f ≤ 3 := by
      by_contra h
      have h4 : 4 ≤ f := by omega
      have h16 : 2 ^ 4 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h4
      omega
    interval_cases f <;> norm_num at hq
  · omega
  · omega

private theorem i167COrth_label_isUnA_aux4 {f : ℕ} {i : TauCeti.CFSGIndex}
    (hi : onLie (isLnEps 2 (2 ^ f) false) i) : False := by
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating d hd => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨t, hv⟩ := d
    cases t with
    | twistedA r q =>
      simp only [onLie, isLnEps] at hi
      obtain ⟨hr, -⟩ := hi
      have hr2 : 2 ≤ r := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
        ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
      omega
    | _ => simp [onLie, isLnEps] at hi

private theorem i167COrth_label_isUnA_aux5 {lab : GLALabel} {f : ℕ} (hf : 1 ≤ f)
    (hP : CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 2 ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f) :
    canonLabel lab = (⟨.A, 1, f⟩ : GLALabel) := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

theorem i167COrth_label_isUnA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {m f : ℕ} (hm : 2 ≤ m)
    (hf : 1 ≤ f) (h : catalogIs (X ⧸ Subgroup.center X) (isUnA m (2 ^ f))) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      canonLabel lab = (if m = 2 then (⟨.A, 1, f⟩ : GLALabel) else ⟨.twA, m - 1, f⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isUnA at hi
  by_cases hm2 : m = 2
  · subst hm2
    rcases hi with hi | ⟨-, hi⟩
    · exact (i167COrth_label_isUnA_aux4 hi).elim
    · have hm := i167COrth_label_isUnA_aux3 hf ⟨i, hi, ⟨e⟩⟩
      have hmark : HasLabel X (fun lab : GLALabel =>
          CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 2 ∧
            CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f) :=
        CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
      obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isLnA_aux3 hmark
      refine ⟨lab, hLab, ?_⟩
      rw [if_pos rfl]
      exact i167COrth_label_isUnA_aux5 hf hP
  · have hm3 : 3 ≤ m := by omega
    rcases hi with hi | ⟨hm2', -⟩
    · have hm := i167COrth_label_isUnA_aux1 hf hi e
      have hmark : HasLabel X (fun lab : GLALabel =>
          CFSG.StandardType.markTag lab = .PSU ∧ CFSG.StandardType.markRank lab = m ∧
            CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = f) :=
        CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
      obtain ⟨lab, hP, hLab⟩ := i167COrth_label_isLnA_aux3 hmark
      refine ⟨lab, hLab, ?_⟩
      rw [if_neg hm2]
      exact i167COrth_label_isUnA_aux2 hm3 hf hP
    · exact absurd hm2' hm2

end CFSG.LocalAnalysis.GLTheoremA.I167

end
