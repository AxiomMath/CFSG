module

public import CFSG.LieType.RootSystem.Basic
public import Mathlib.GroupTheory.Coxeter.Length
public import TauCeti.GroupTheory.Coxeter.Parabolic
import TauCeti.GroupTheory.Coxeter.Dihedral

public section

namespace CFSG.LieType.RootSystem

open CoxeterSystem

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

private def altCoord (a b : ℤ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 =>
    if n % 2 = 0 then ((altCoord a b n).1, -(altCoord a b n).2 - b * (altCoord a b n).1)
    else (-(altCoord a b n).1 - a * (altCoord a b n).2, (altCoord a b n).2)

omit [DecidableEq I] in
include hA in
private theorem altCoord_nonneg {i j : I} (hij : i ≠ j) {n : ℕ}
    (hn : n < TauCeti.coxeterOrder (A j i * A i j)) :
    0 ≤ (altCoord (A i j) (A j i) n).1 ∧ 0 ≤ (altCoord (A i j) (A j i) n).2 := by
  rcases cartan_pair_cases hA hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ <;>
  · rw [h1, h2] at hn ⊢
    norm_num at hn
    revert n
    decide

private theorem weylAction_alternatingWord (i j : I) (n : ℕ) :
    weylAction hA ((coxeterMatrix hA).toCoxeterSystem.wordProd (alternatingWord i j n))
      (Pi.single i 1) = pair i j (altCoord (A i j) (A j i) n) := by
  induction n with
  | zero => simp [alternatingWord, altCoord, pair_apply]
  | succ n ih =>
    rw [alternatingWord_succ', wordProd_cons, weylAction_mul_apply, ih, weylAction_simple]
    by_cases hn : Even n
    · rw [ite_eq_left hn, reflection_pair_right i (hA.apply_self j), altCoord,
        ite_eq_left (Nat.even_iff.mp hn)]
    · rw [ite_eq_right hn, reflection_pair_left j (hA.apply_self i), altCoord,
        ite_eq_right (fun h => hn (Nat.even_iff.mpr h))]

theorem exists_nonneg_of_mem_parabolic_pair {i j : I} (hij : i ≠ j)
    {x : (coxeterMatrix hA).Group} (hx : x ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {i, j})
    (hxi : ¬ (coxeterMatrix hA).toCoxeterSystem.IsRightDescent x i) :
    ∃ p q : ℤ, 0 ≤ p ∧ 0 ≤ q ∧
      weylAction hA x (Pi.single i 1) = p • Pi.single i 1 + q • Pi.single j 1 := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  have hlen := cs.not_isRightDescent_iff.mp hxi
  rcases cs.wordProd_alternatingWord_eq_of_mem_parabolic_pair hx with h | h
  ·
    have hred : cs.IsReduced (alternatingWord j i (cs.length x + 1)) := by
      change cs.length (cs.wordProd _) = _
      rw [alternatingWord_succ, wordProd_concat, h, List.length_concat, length_alternatingWord,
        hlen]
    have hM : (coxeterMatrix hA) j i ≠ 0 := by
      simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
      have := TauCeti.two_le_coxeterOrder (hA.apply_mul_apply_mem_of_ne hij.symm)
      omega
    have hlt : cs.length x < (coxeterMatrix hA) j i := by
      by_contra hc
      exact cs.not_isReduced_alternatingWord j i hM (by omega) hred
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply] at hlt
    obtain ⟨hp, hq⟩ := altCoord_nonneg hA hij hlt
    exact ⟨_, _, hp, hq, by rw [← pair_apply, ← weylAction_alternatingWord, h]⟩
  ·
    obtain ⟨n, hn⟩ | h0 : (∃ n, cs.length x = n + 1) ∨ cs.length x = 0 := by
      rcases Nat.eq_zero_or_pos (cs.length x) with h0 | h0
      · exact Or.inr h0
      · exact Or.inl ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
    · exfalso
      rw [hn, alternatingWord_succ, wordProd_concat] at h
      have h' : x * cs.simple i = cs.wordProd (alternatingWord i j n) := by
        rw [← h, simple_mul_simple_cancel_right]
      have := cs.length_wordProd_le (alternatingWord i j n)
      rw [← h', length_alternatingWord] at this
      omega
    · rw [cs.length_eq_zero_iff.mp h0]
      exact ⟨1, 0, zero_le_one, le_rfl, by simp⟩

theorem nonneg_of_not_isRightDescent (w : (coxeterMatrix hA).Group) (i : I)
    (hw : ¬ (coxeterMatrix hA).toCoxeterSystem.IsRightDescent w i) :
    0 ≤ weylAction hA w (Pi.single i 1) := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  obtain ⟨n, hn⟩ : ∃ n, cs.length w = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing w i with
  | _ n ih =>
    by_cases h1 : w = 1
    · subst h1
      simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one h1
    have hij : i ≠ j := by
      rintro rfl
      exact hw hj
    obtain ⟨⟨u, x⟩, ⟨hu, hx, hux⟩, -⟩ := cs.existsUnique_isMinimalCosetRep_mul {i, j} w
    dsimp only at hu hx hux
    subst hux
    have hlen := cs.length_mul_of_isMinimalCosetRep hu hx
    have hu' := cs.isMinimalCosetRep_iff.mp hu
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hu' j (by simp) (by simpa using hj)
    have hxpos : 0 < cs.length x := by
      rcases Nat.eq_zero_or_pos (cs.length x) with h | h
      · exact absurd (cs.length_eq_zero_iff.mp h) hx1
      · exact h
    have hui := ih (cs.length u) (by omega) u i (hu' i (by simp)) rfl
    have huj := ih (cs.length u) (by omega) u j (hu' j (by simp)) rfl
    have hxi : ¬ cs.IsRightDescent x i := by
      rw [cs.not_isRightDescent_iff] at hw ⊢
      have h2 := cs.length_mul_of_isMinimalCosetRep hu
        (mul_mem hx (cs.simple_mem_parabolic (by simp : i ∈ ({i, j} : Set I))))
      rw [mul_assoc] at hw
      omega
    obtain ⟨p, q, hp, hq, hpq⟩ := exists_nonneg_of_mem_parabolic_pair hA hij hx hxi
    rw [weylAction_mul_apply, hpq, map_add, map_zsmul, map_zsmul]
    exact add_nonneg (smul_nonneg hp hui) (smul_nonneg hq huj)

theorem nonpos_of_isRightDescent {w : (coxeterMatrix hA).Group} {i : I}
    (hw : (coxeterMatrix hA).toCoxeterSystem.IsRightDescent w i) :
    weylAction hA w (Pi.single i 1) ≤ 0 := by
  have h := nonneg_of_not_isRightDescent hA _ i
    ((coxeterMatrix hA).toCoxeterSystem.isRightDescent_iff_not_isRightDescent_mul.mp hw)
  rw [weylAction_mul_apply, weylAction_simple_single, map_neg] at h
  exact neg_nonneg.mp h

theorem isRightDescent_iff (w : (coxeterMatrix hA).Group) (i : I) :
    (coxeterMatrix hA).toCoxeterSystem.IsRightDescent w i ↔
      weylAction hA w (Pi.single i 1) ≤ 0 := by
  refine ⟨nonpos_of_isRightDescent hA, fun h => by_contra fun hw => ?_⟩
  exact weylAction_single_ne_zero hA w i
    (le_antisymm h (nonneg_of_not_isRightDescent hA w i hw))

theorem nonneg_iff_not_isRightDescent (w : (coxeterMatrix hA).Group) (i : I) :
    0 ≤ weylAction hA w (Pi.single i 1) ↔
      ¬ (coxeterMatrix hA).toCoxeterSystem.IsRightDescent w i := by
  refine ⟨fun h hw => weylAction_single_ne_zero hA w i
    (le_antisymm ((isRightDescent_iff hA w i).mp hw) h), nonneg_of_not_isRightDescent hA w i⟩

theorem weylAction_single_nonneg_or_nonpos (w : (coxeterMatrix hA).Group) (i : I) :
    0 ≤ weylAction hA w (Pi.single i 1) ∨ weylAction hA w (Pi.single i 1) ≤ 0 := by
  by_cases hw : (coxeterMatrix hA).toCoxeterSystem.IsRightDescent w i
  · exact Or.inr (nonpos_of_isRightDescent hA hw)
  · exact Or.inl (nonneg_of_not_isRightDescent hA w i hw)

theorem nonneg_or_nonpos (D : Set I) {γ : I → ℤ} (hγ : γ ∈ roots hA D) : 0 ≤ γ ∨ γ ≤ 0 := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
  · exact weylAction_single_nonneg_or_nonpos hA w i
  · rcases weylAction_single_nonneg_or_nonpos hA w i with h | h
    · exact Or.inl (nsmul_nonneg h 2)
    · exact Or.inr (nsmul_nonpos h 2)

theorem weylAction_injective : Function.Injective (weylAction hA) := by
  refine (injective_iff_map_eq_one (weylAction hA)).mpr fun w hw => by_contra fun h1 => ?_
  obtain ⟨i, hi⟩ := (coxeterMatrix hA).toCoxeterSystem.exists_rightDescent_of_ne_one h1
  have h := (isRightDescent_iff hA w i).mp hi
  rw [hw, Module.End.one_apply] at h
  simpa using h i

end CFSG.LieType.RootSystem
