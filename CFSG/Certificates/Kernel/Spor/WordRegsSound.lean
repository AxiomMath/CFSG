module

public import Certificates.Data.Kernel.Spor.WordRegs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Tactic.Attr.Core

public section

namespace CFSG.KS.WordRegs

variable {G : Type*} [Group G] (ρ : ℕ → G)

@[expose] def codeEl (c : ℕ) : G := if c % 2 = 1 then ρ (c / 2) else (ρ (c / 2))⁻¹

@[expose] def wordEl (w : List ℕ) : G := (w.map (codeEl ρ)).prod

@[expose] def RootsEq (RW : List (List ℕ)) : Prop := ∀ g, 2 ≤ g → ρ g = wordEl ρ (RW.getD (g - 2) [])

variable {ρ}

theorem wordEl_nil : wordEl ρ [] = 1 := rfl

theorem wordEl_cons (c : ℕ) (w : List ℕ) : wordEl ρ (c :: w) = codeEl ρ c * wordEl ρ w := by
  simp [wordEl]

theorem wordEl_append (u v : List ℕ) : wordEl ρ (u ++ v) = wordEl ρ u * wordEl ρ v := by
  simp [wordEl]

theorem wordEl_single (c : ℕ) : wordEl ρ [c] = codeEl ρ c := by simp [wordEl]

theorem codeEl_odd (g : ℕ) : codeEl ρ (2 * g + 1) = ρ g := by
  unfold codeEl
  rw [if_pos (by omega)]
  congr 1
  omega

theorem codeEl_flipC (c : ℕ) : codeEl ρ (flipC c) = (codeEl ρ c)⁻¹ := by
  unfold codeEl flipC
  by_cases h : c % 2 = 1
  · rw [if_pos h, if_neg (by omega), if_pos h]
    congr 2
    omega
  · rw [if_neg h, if_pos (by omega), if_neg h, inv_inv]
    congr 1
    omega

theorem wordEl_invW (w : List ℕ) : wordEl ρ (invW w) = (wordEl ρ w)⁻¹ := by
  induction w with
  | nil => simp [invW, wordEl]
  | cons c w ih =>
    have e : invW (c :: w) = invW w ++ [flipC c] := by simp [invW]
    rw [e, wordEl_append, ih, wordEl_single, codeEl_flipC, wordEl_cons, mul_inv_rev]

theorem tieW_sound {RW : List (List ℕ)} (hρ : RootsEq ρ RW) {w : List ℕ} {c : ℕ}
    (h : tieW RW w c = true) : wordEl ρ w = codeEl ρ c := by
  unfold tieW at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with rfl | ⟨⟨hc, h2⟩, hw⟩
  · exact wordEl_single c
  · have e : c = 2 * (c / 2) + 1 := by omega
    rw [e, codeEl_odd, hρ _ h2, ← hw]

theorem sgnC_pos {K : List ℕ} {l : ℤ} (hl : 0 < l) : sgnC K l = K.getD (l.natAbs - 1) 0 := by
  unfold sgnC
  rw [if_pos hl]

theorem sgnC_neg {K : List ℕ} {l : ℤ} (hl : ¬ 0 < l) :
    sgnC K l = flipC (K.getD (l.natAbs - 1) 0) := by
  unfold sgnC
  rw [if_neg hl]

theorem wordEl_sgnC {f : ℕ → G} {K : List ℕ} (w : List ℤ)
    (hw : ∀ l ∈ w, codeEl ρ (K.getD (l.natAbs - 1) 0) = f (l.natAbs - 1)) :
    wordEl ρ (w.map (sgnC K)) =
      (w.map fun l => if 0 < l then f (l.natAbs - 1) else (f (l.natAbs - 1))⁻¹).prod := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, wordEl_cons, List.map_cons, List.prod_cons,
      ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')]
    have hl := hw l List.mem_cons_self
    congr 1
    by_cases hp : 0 < l
    · rw [sgnC_pos hp, if_pos hp, hl]
    · rw [sgnC_neg hp, if_neg hp, codeEl_flipC, hl]

theorem codeEl_even (g : ℕ) : codeEl ρ (2 * g) = (ρ g)⁻¹ := by
  unfold codeEl
  rw [if_neg (by omega)]
  congr 2
  omega

theorem rootsOK_spec {RW : List (List ℕ)} (h : rootsOK RW = true) {k : ℕ} {c : ℕ}
    (hc : c ∈ RW.getD k []) : c / 2 < k + 2 := by
  unfold rootsOK at h
  rw [List.all_eq_true] at h
  by_cases hk : k < RW.length
  · have := h k (List.mem_range.2 hk)
    rw [List.all_eq_true] at this
    exact of_decide_eq_true (this c hc)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : RW.length ≤ k)] at hc

end CFSG.KS.WordRegs

end
