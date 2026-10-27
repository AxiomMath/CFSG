module

public import CFSG.Certificates.Kernel.J4Loc.TrioSound
public import Certificates.Data.J4Loc.TrioOct

public section

namespace CFSG.KS.J4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem letters_idx {l : ℕ} (hl : l < 6) : letters.idxOf (letters.getD l 0) = l := by
  interval_cases l <;> decide

theorem idx_lt {ℓ : ℤ} (hℓ : ℓ ∈ letters) : letters.idxOf ℓ < 6 :=
  List.idxOf_lt_length_of_mem hℓ

theorem getD_idx {ℓ : ℤ} (hℓ : ℓ ∈ letters) : letters.getD (letters.idxOf ℓ) 0 = ℓ := by
  simp only [letters, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem act_eq_actK (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) {l : ℕ} (hl : l < 6) :
    act (letters.getD l 0) = actK (rowL letterRows l) := by
  funext c
  rw [actK_eq, rowL_eq, hLR l hl]
  unfold act letterRow
  rw [letters_idx hl]

theorem wordF_eq (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) :
    ∀ (w : List ℕ), (∀ l ∈ w, l < 6) → ∀ W : Finset ℕ,
      wordF letterRows w W = wordImgF (w.map fun l => letters.getD l 0) W := by
  intro w
  induction w with
  | nil => intro _ W; rfl
  | cons l w ih =>
    intro hw W
    change wordF letterRows w (W.image (actK (rowL letterRows l))) =
      wordImgF (w.map fun l => letters.getD l 0) (W.image (act (letters.getD l 0)))
    rw [act_eq_actK hLR (hw l List.mem_cons_self)]
    exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) _

theorem trioOct_eq {TK TR N I0 : ℕ} (h : OctAll letterRows TK TR N I0)
    (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) (hI0 : I0 < N)
    (hV0 : octF TK I0 = V0F) : TrioOct = octF TK '' {i | i < N} := by
  ext W
  constructor
  · rintro ⟨w, hw, rfl⟩
    suffices H : ∀ (w : List ℤ), (∀ ℓ ∈ w, ℓ ∈ letters) → ∀ i < N,
        wordImgF w (octF TK i) ∈ octF TK '' {i | i < N} by
      rw [← hV0]
      exact H w hw I0 hI0
    intro w
    induction w with
    | nil => intro _ i hi; exact ⟨i, hi, rfl⟩
    | cons ℓ w ih =>
      intro hw i hi
      have hℓ := hw ℓ List.mem_cons_self
      obtain ⟨j, hj, he⟩ := octF_step h hi (idx_lt hℓ)
      change wordImgF w ((octF TK i).image (act ℓ)) ∈ _
      rw [← getD_idx hℓ, act_eq_actK hLR (idx_lt hℓ), he]
      exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) j hj
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨w, hw, he⟩ := octF_word h hi
    refine ⟨w.map fun l => letters.getD l 0, fun ℓ hℓ => ?_, ?_⟩
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hℓ
      have h6 := hw l hl
      interval_cases l <;> decide
    · rw [he, hV0, wordF_eq hLR w hw]

theorem trioOct_ncard {TK TR N I0 : ℕ} (h : OctAll letterRows TK TR N I0)
    (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) (hI0 : I0 < N)
    (hV0 : octF TK I0 = V0F) : TrioOct.ncard = N := by
  have e : octF TK '' {i | i < N} = (((Finset.range N).image (octF TK) : Finset (Finset ℕ)) :
      Set (Finset ℕ)) := by
    ext
    simp
  rw [trioOct_eq h hLR hI0 hV0, e, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (fun i hi j hj he => octF_inj h (by simpa using hi)
      (by simpa using hj) he), Finset.card_range]

theorem trioOct_props {TK TR N I0 : ℕ} (h : OctAll letterRows TK TR N I0)
    (hLR : ∀ l < 6, (letterRows.getD l []).length = 11) (hI0 : I0 < N)
    (hV0 : octF TK I0 = V0F) {W : Finset ℕ} (hW : W ∈ TrioOct) :
    W.card = 8 ∧ 0 ∈ W ∧ (∀ x ∈ W, x < 2048) ∧ ∀ x ∈ W, ∀ y ∈ W, x ^^^ y ∈ W := by
  rw [trioOct_eq h hLR hI0 hV0] at hW
  obtain ⟨i, hi, rfl⟩ := hW
  exact octF_props h hi

end CFSG.KS.J4Loc

end
