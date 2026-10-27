module

public import Certificates.Data.Kernel.Spor.MulHAbs
public import CFSG.Certificates.Kernel.Spor.MulHSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem sorted_absent {cnt p v : Nat} {F S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → F (S i) < F (S (i + 1))))
    (hp : p ≤ cnt) (hlo : p ≠ 0 → F (S (p - 1)) < v) (hhi : p < cnt → v < F (S p)) :
    ∀ a < cnt, F a ≠ v := by
  have hmono : ∀ i j, i < j → j < cnt → F (S i) < F (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  by_cases hip : i < p
  · have hlt := hlo (by omega)
    rcases Nat.lt_or_ge i (p - 1) with h | h
    · have := hmono i (p - 1) h (by omega)
      omega
    · have hi' : i = p - 1 := by omega
      rw [hi'] at e
      omega
  · have hpc : p < cnt := by omega
    have hgt := hhi hpc
    rcases Nat.lt_or_ge p i with h | h
    · have := hmono p i h hi
      omega
    · have hi' : i = p := by omega
      rw [hi'] at e
      omega

theorem absK_sound {n w cnt q p : Nat} {T HS HSI : Nat → Nat}
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (h : absK n w (mask w) cnt T HS q p = true) :
    ∀ a < cnt, hkeyK n w (mask w) (T a) ≠ hkeyK n w (mask w) q := by
  unfold absK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h2 h3
  refine sorted_absent (F := fun i => hkeyK n w (mask w) (T i)) (S := r32 HS) (SI := r32 HSI)
    (fun i hi => ?_) (Nat.le_of_ble_eq_true h1) (fun hp0 => ?_) (fun hpc => ?_)
  · have h' := hs i hi
    unfold hsortPtK at h'
    rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
    simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h'
    obtain ⟨a1, a2, a3⟩ := h'
    rw [CFSG.KS.Raw.Orb.bIf_eq] at a3
    refine ⟨Nat.blt_eq.mp a1, Nat.eq_of_beq_eq_true a2, fun hc => ?_⟩
    simp only [Nat.blt_eq.mpr hc, ↓reduceIte] at a3
    exact Nat.blt_eq.mp a3
  · have hb : Nat.beq p 0 = false := by
      cases e : Nat.beq p 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hp0
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h2
    exact Nat.blt_eq.mp h2
  · simp only [Nat.blt_eq.mpr hpc, ↓reduceIte] at h3
    exact Nat.blt_eq.mp h3

theorem memT_absK {n w cnt q p : Nat} {T PL HS HSI : Nat → Nat}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hq : canonK n w (mask w) (n * w) q = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (h : absK n w (mask w) cnt T HS q p = true) :
    memT n (hRec n w cnt T PL).1 (tabT (unpack n w q)) = false := by
  have ha := absK_sound hs h
  unfold memT
  rw [Bool.eq_false_iff]
  intro hm
  rw [Array.any_eq_true] at hm
  obtain ⟨i, hi, he⟩ := hm
  have hi' : i < cnt := by simpa [hRec] using hi
  have hx : (hRec n w cnt T PL).1[i] = tabT (unpack n w (T i)) := by simp [hRec]
  rw [hx, tblEq_unpack hq (hT i hi')] at he
  exact ha i hi' (by rw [Nat.eq_of_beq_eq_true he])

theorem memT_memK {n w cnt q pos br : Nat} {T PL HS HSI : Nat → Nat}
    (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hq : canonK n w (mask w) (n * w) q = true)
    (hs : ∀ i < cnt, hsortPtK n w (mask w) cnt T HS HSI i = true)
    (h : memK n w (mask w) cnt T HS q pos br = true) :
    memT n (hRec n w cnt T PL).1 (tabT (unpack n w q)) = Nat.blt pos cnt := by
  unfold memK at h
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h
  by_cases hp : Nat.blt pos cnt = true
  · simp only [hp, ↓reduceIte] at h
    rw [hp]
    refine memT_of (Nat.blt_eq.mp hp) ?_
    rw [← Nat.eq_of_beq_eq_true h]
    exact tblEqH_self n _
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
    rw [memT_absK hT hq hs h]
    cases e : Nat.blt pos cnt
    · rfl
    · exact absurd e hp

end CFSG.KS.MulH

end
