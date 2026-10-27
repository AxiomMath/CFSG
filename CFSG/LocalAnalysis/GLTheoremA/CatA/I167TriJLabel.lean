module

import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

set_option linter.unusedSectionVars false




private theorem exists_label_isLnA_aux1 {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
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

private theorem exists_label_isLnA_aux2 {lab : GLALabel} {n : ℕ} (hn : 5 ≤ n)
    (hP : CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :
    (canonLabel lab).tag = .A ∧ (canonLabel lab).rank = n - 1 := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem exists_label_isLnA_aux3 {X : Type} [Group X] {P : GLALabel → Prop}
    (h : HasLabel X P) : ∃ lab : GLALabel, P lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem exists_label_isOmMA_aux1 {S : Type} [Group S] {n : ℕ} (hn : 6 ≤ n)
    (h : catalogIs S (isOmMA n 2)) : CFSG.Blueprint.LieModel S .POmegaMinus n 2 1 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmMA isOmM at hi
  rcases hi with hi | ⟨h3, _⟩
  · cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating d hd => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | twistedD r q =>
        simp only [onLie] at hi
        obtain ⟨hr, hq⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
          (hq.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .POmegaMinus n 2 1 := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_twistedD r q hv e
        exact CFSG.Models.LieModel.toBlueprint (by decide) hm
      | _ => simp [onLie] at hi
  · omega

private theorem exists_label_isOmMA_aux2 {lab : GLALabel} {n : ℕ} (hn : 6 ≤ n)
    (hP : CFSG.StandardType.markTag lab = .POmegaMinus ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :
    (canonLabel lab).tag = .twD ∧ (canonLabel lab).rank = n := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem exists_label_isOmPA_aux1 {lab : GLALabel} {n k : ℕ} (hn : 5 ≤ n) (hk : 1 ≤ k)
    (hP : CFSG.StandardType.markTag lab = .POmegaPlus ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :
    ((canonLabel lab).tag = .A ∧ 3 ≤ (canonLabel lab).rank) ∨
      ((canonLabel lab).tag = .D ∧ 5 ≤ (canonLabel lab).rank) := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem exists_label_isOmPA_aux2 {lab : GLALabel} {k : ℕ} (hk : 1 ≤ k)
    (hP : CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 4 ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :
    ((canonLabel lab).tag = .A ∧ 3 ≤ (canonLabel lab).rank) ∨
      ((canonLabel lab).tag = .D ∧ 5 ≤ (canonLabel lab).rank) := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
    (try split_ifs at hP ⊢) <;> simp_all <;> omega

private theorem exists_label_isOmPA_aux3 {S : Type} [Group S] {k : ℕ} (hk : 1 ≤ k) (hk1 : k ≠ 1)
    (h : catalogIs S (isLnA 4 (2 ^ k))) : CFSG.Blueprint.LieModel S .PSL 4 2 k := by
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
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk
          (hq.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .PSL 4 2 k := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        exact CFSG.Models.LieModel.toBlueprint (by decide) hm
      | _ => simp [onLie, isLnEps] at hi
  · omega
  · omega
  · omega
  · obtain ⟨-, hq, -⟩ := hs
    exact absurd (Nat.pow_right_injective (le_refl 2) (hq.trans (by norm_num))) hk1


theorem exists_label_isLnA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hn : 5 ≤ n)
    (h : catalogIs (X ⧸ Subgroup.center X) (isLnA n 2)) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ (canonLabel lab).tag = .A ∧
      (canonLabel lab).rank = n - 1 := by
  have hm := exists_label_isLnA_aux1 hn h
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = n ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
  obtain ⟨lab, hP, hLab⟩ := exists_label_isLnA_aux3 hmark
  exact ⟨lab, hLab, exists_label_isLnA_aux2 hn hP⟩

theorem exists_label_isOmMA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n : ℕ} (hn : 6 ≤ n)
    (h : catalogIs (X ⧸ Subgroup.center X) (isOmMA n 2)) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ (canonLabel lab).tag = .twD ∧
      (canonLabel lab).rank = n := by
  have hm := exists_label_isOmMA_aux1 hn h
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = .POmegaMinus ∧ CFSG.StandardType.markRank lab = n ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
  obtain ⟨lab, hP, hLab⟩ := exists_label_isLnA_aux3 hmark
  exact ⟨lab, hLab, exists_label_isOmMA_aux2 hn hP⟩


private theorem exists_label_isOmPA_aux4 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    {n k : ℕ} (hodd : Odd n) (hk : 1 ≤ k) {i : TauCeti.CFSGIndex}
    (hi : isOmP n (2 ^ k) i) (e : X ⧸ Subgroup.center X ≃* i.Group) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      (((canonLabel lab).tag = .A ∧ 3 ≤ (canonLabel lab).rank) ∨
        ((canonLabel lab).tag = .D ∧ 5 ≤ (canonLabel lab).rank)) := by
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
      obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk
        (hqc.trans (by norm_num))
      have hm : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 2 k := by
        simpa [h1, h2, hr] using CFSG.Models.lieModel_D r q hv e
      have hmB : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .POmegaPlus n 2 k :=
        CFSG.Models.LieModel.toBlueprint (by decide) hm
      have hn5 : 5 ≤ n := by
        rcases hodd with ⟨m, hm⟩
        omega
      have hmark : HasLabel X (fun lab : GLALabel =>
          CFSG.StandardType.markTag lab = .POmegaPlus ∧ CFSG.StandardType.markRank lab = n ∧
            CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :=
        CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hmB
      obtain ⟨lab, hP, hLab⟩ := exists_label_isLnA_aux3 hmark
      exact ⟨lab, hLab, exists_label_isOmPA_aux1 hn5 hk hP⟩
    | _ => simp [onLie] at hi

private theorem exists_label_isOmPA_aux5 {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    {k : ℕ} (hk : 1 ≤ k) (hk1 : k ≠ 1) {i : TauCeti.CFSGIndex}
    (hi : isLnA 4 (2 ^ k) i) (e : X ⧸ Subgroup.center X ≃* i.Group) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      (((canonLabel lab).tag = .A ∧ 3 ≤ (canonLabel lab).rank) ∨
        ((canonLabel lab).tag = .D ∧ 5 ≤ (canonLabel lab).rank)) := by
  have hm := exists_label_isOmPA_aux3 hk hk1 ⟨i, hi, ⟨e⟩⟩
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = .PSL ∧ CFSG.StandardType.markRank lab = 4 ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = k) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
  obtain ⟨lab, hP, hLab⟩ := exists_label_isLnA_aux3 hmark
  exact ⟨lab, hLab, exists_label_isOmPA_aux2 hk hP⟩


theorem exists_label_isOmPA {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X) {n k : ℕ} (hodd : Odd n)
    (hn : 3 ≤ n) (hk : 1 ≤ k) (hk1 : k = 1 → 5 ≤ n)
    (h : catalogIs (X ⧸ Subgroup.center X) (isOmPA n (2 ^ k))) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧
      (((canonLabel lab).tag = .A ∧ 3 ≤ (canonLabel lab).rank) ∨
        ((canonLabel lab).tag = .D ∧ 5 ≤ (canonLabel lab).rank)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmPA at hi
  rcases hi with hi | ⟨hn3, hi⟩
  · exact exists_label_isOmPA_aux4 hq hodd hk hi e
  · have hk' : k ≠ 1 := fun hk1' => by have := hk1 hk1'; omega
    exact exists_label_isOmPA_aux5 hq hk hk' hi e

end CFSG.LocalAnalysis.GLTheoremA.I167

end
