module

public import Certificates.Data.Kernel.SmithEKV
public import CFSG.Certificates.Kernel.SmithEK.GSound
public import CFSG.Certificates.Kernel.SmithEK.TSound
public import CFSG.Certificates.Kernel.SmithEK.ISound

public section

namespace CFSG.SmithE.K

open CFSG.SmithE CFSG.F4.Native

theorem fixRowK_sound (w : Nat) : ∀ (L : List Nat) (V M : Nat), fixRowK w L V M = true →
    ∀ a < L.length, (fld a V = w ↔ M.testBit a = true)
  | [], _, _, _, a, ha => absurd ha (by simp)
  | _ :: L, V, M, h, a, ha => by
    have h' : (((V % 1048576 == w) == (M % 2 == 1)) &&
        fixRowK w L (V / 1048576) (M / 2)) = true := h
    rw [Bool.and_eq_true, beq_iff_eq] at h'
    rcases a with _ | a
    · have e := congrArg (· = true) h'.1
      simp only [beq_iff_eq] at e
      rw [fld_zero_k, Nat.testBit_zero, decide_eq_true_iff]
      exact Iff.of_eq e
    · rw [fld_succ, Nat.testBit_succ]
      exact fixRowK_sound w L _ _ h'.2 a (by simpa using ha)

theorem fixChunkK_sound {C W P L : List Nat} {s n : Nat} (h : fixChunkK C W P L s n = true)
    {i : Nat} (h1 : s ≤ i) (h2 : i < s + n) :
    W.getD i 0 < 2 ^ 20 ∧ fixRowK (W.getD i 0) L (c8ap C (W.getD i 0)) (P.getD i 0) = true := by
  unfold fixChunkK at h
  rw [List.all_eq_true] at h
  have e := h i (List.mem_range'_1.mpr ⟨h1, h2⟩)
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using e

theorem conj_of_cols {A B Cc : List Nat} (hA : A.length = 20) (hC : Cc.length = 20)
    (h : ∀ m < 20, applyL A (applyL B (A.getD m 0)) = Cc.getD m 0) (x : Nat) :
    applyL Cc x = applyL A (applyL B (applyL A x)) := by
  rw [applyL_comp B A, applyL_comp A]
  congr 1
  apply List.ext_getElem (by simp [hA, hC])
  intro n h1 h2
  have hn : n < 20 := by rw [hC] at h1; exact h1
  have e := h n hn
  rw [List.getD_eq_getElem A 0 (by rw [hA]; exact hn),
    List.getD_eq_getElem Cc 0 (by rw [hC]; exact hn)] at e
  simp only [List.getElem_map]
  exact e.symm

theorem invol_of_cols {A : List Nat} (hA : A.length = 20)
    (h : ∀ m < 20, applyL A (A.getD m 0) = 2 ^ m) {x : Nat} (hx : x < 2 ^ 20) :
    applyL A (applyL A x) = x := by
  rw [applyL_comp A A]
  have e : A.map (applyL A) = (List.range 20).map (2 ^ ·) := by
    apply List.ext_getElem (by simp [hA])
    intro n h1 h2
    have hn : n < 20 := by simpa [hA] using h1
    have e := h n hn
    rw [List.getD_eq_getElem A 0 (by rw [hA]; exact hn)] at e
    simp only [List.getElem_map, List.getElem_range]
    exact e
  rw [e, applyL_pow 20 x hx]

theorem ptTab_get {k a : Nat} (hk : k < 693) (ha : a < 693) : (ptTab[k]!)[a]! = ptImg k a := by
  unfold ptTab
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hk]
  exact CFSG.SmithL6.Kernel.ofFn_get! _ ha

theorem chkTW_of (hT : chkT = true)
    (hfix : ∀ a < 693, ∀ i < 891,
      (applyCols tvArr[a]! wtArr[i]! = wtArr[i]! ↔ inPlane i a = true))
    (hwt : ∀ i < 891, wtArr[i]! < 2 ^ 20)
    (hpt : ∀ k < 693, ∀ a < 693, ptImg k a < 693 ∧ ∀ x,
      applyCols tvArr[ptImg k a]! x = applyCols tvArr[k]! (applyCols tvArr[a]! (applyCols tvArr[k]! x)))
    (hinv : ∀ k < 693, ∀ x < 2 ^ 20, applyCols tvArr[k]! (applyCols tvArr[k]! x) = x) :
    chkTW = true := by
  have hA : ∀ k < 693, ∀ i < 891, planeImg k i < 891 ∧
      wtArr[planeImg k i]! = applyCols tvArr[k]! wtArr[i]! := by
    intro k hk i hi
    unfold chkT at hT
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hT
    obtain ⟨⟨h1, h2⟩, -⟩ := hT k hk i hi
    exact ⟨h1, h2⟩
  unfold chkTW
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Array.all_eq_true_iff_forall_mem]
  intro k hk i hi
  obtain ⟨hj, hwj⟩ := hA k hk i hi
  refine ⟨⟨hj, hwj⟩, fun a ha => ?_⟩
  rw [planePtsArr_get hi] at ha
  obtain ⟨ha1, ha2⟩ := mem_planePts.mp (Array.mem_toList_iff.mpr ha)
  rw [ptTab_get hk ha1]
  obtain ⟨hb, hc⟩ := hpt k hk a ha1
  rw [← hfix _ hb _ hj, hc, hwj, hinv k hk _ (hwt i hi), (hfix a ha1 i hi).mpr ha2]

end CFSG.SmithE.K
