module

public import Certificates.Data.Kernel.SmithEKM
public import CFSG.LargeExtraspecial.S14SMKDivCheck
public import CFSG.Certificates.Kernel.SmithEK.WSound
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.SmithE.K

open CFSG.SmithE CFSG.F4.Native

theorem ptBits_cons (m p : Nat) (L : List Nat) :
    ptBits m (p :: L) = (bif m.testBit p then 1 else 0) + 2 * ptBits m L := rfl

theorem testBit_ptBits (m : Nat) : ∀ (L : List Nat) (a : Nat),
    (ptBits m L).testBit a = (decide (a < L.length) && m.testBit (L.getD a 0))
  | [], a => by simp [ptBits]
  | p :: L, 0 => by
    rw [ptBits_cons, Nat.testBit_zero]
    cases h : m.testBit p <;> simp [h, Nat.add_mul_mod_self_left]
  | p :: L, a + 1 => by
    rw [ptBits_cons]
    have e : ((bif m.testBit p then 1 else 0) + 2 * ptBits m L) / 2 = ptBits m L := by
      cases m.testBit p <;> simp <;> omega
    rw [Nat.testBit_succ, e, testBit_ptBits m L a]
    simp

theorem ptBits_lt (m : Nat) (L : List Nat) : ptBits m L < 2 ^ L.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_ptBits]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  exact Or.inl hi

theorem cntK_zero (x : Nat) : cntK 0 x = 0 := rfl

theorem cntK_succ (f x : Nat) :
    cntK (f + 1) x = bif x == 0 then 0 else cntK f (x &&& (x - 1)) + 1 := rfl

private theorem land_pred_two_mul (y : Nat) (hy : y ≠ 0) :
    (2 * y) &&& (2 * y - 1) = 2 * (y &&& (y - 1)) := by
  have e : 2 * y - 1 = 2 * (y - 1) + 1 := by omega
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases i with
  | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
  | succ i =>
    have h1 : 2 * y / 2 = y := by omega
    have h2 : (2 * (y - 1) + 1) / 2 = y - 1 := by omega
    have h3 : 2 * (y &&& (y - 1)) / 2 = (y &&& (y - 1)) := by omega
    simp only [Nat.testBit_succ, h1, h2, h3, Nat.testBit_and]

theorem testBit_land_pred : ∀ x : Nat, x ≠ 0 →
    ∃ i₀, x.testBit i₀ = true ∧ ∀ i, (x &&& (x - 1)).testBit i = (x.testBit i && i != i₀) := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    rcases Nat.even_or_odd x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have hy : y ≠ 0 := by omega
      obtain ⟨j, hj, hjb⟩ := ih y (by omega) hy
      refine ⟨j + 1, ?_, fun i => ?_⟩
      · rw [show y + y = 2 * y by omega, Nat.testBit_succ]
        simpa using hj
      · rw [show y + y = 2 * y by omega, land_pred_two_mul y hy]
        cases i with
        | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
        | succ i =>
          have h1 : 2 * y / 2 = y := by omega
          have h3 : 2 * (y &&& (y - 1)) / 2 = (y &&& (y - 1)) := by omega
          simp only [Nat.testBit_succ, h1, h3, hjb i]
          simp
    · refine ⟨0, by simp [Nat.testBit_zero], fun i => ?_⟩
      have e : (2 * y + 1) &&& (2 * y + 1 - 1) = 2 * y := by
        rw [show 2 * y + 1 - 1 = 2 * y by omega]
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and]
        cases i with
        | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
        | succ i =>
          have h1 : (2 * y + 1) / 2 = y := by omega
          have h2 : 2 * y / 2 = y := by omega
          simp only [Nat.testBit_succ, h1, h2, Bool.and_self]
      rw [e]
      cases i with
      | zero => simp [Nat.testBit_zero, Nat.mul_mod_right]
      | succ i =>
        have h1 : (2 * y + 1) / 2 = y := by omega
        have h2 : 2 * y / 2 = y := by omega
        simp only [Nat.testBit_succ, h1, h2]
        simp

theorem countP_range_split (p q : Nat → Bool) (i₀ : Nat) (hp : ∀ a, p a = (q a || a == i₀))
    (hq : q i₀ = false) : ∀ m, (List.range m).countP p =
      (List.range m).countP q + (if i₀ < m then 1 else 0)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.countP_append, List.countP_append, countP_range_split p q i₀ hp hq m]
    by_cases h : m = i₀
    · subst h
      simp [hp, hq]
    · have hm : p m = q m := by simp [hp, h]
      simp only [List.countP_singleton, hm]
      by_cases h1 : i₀ < m
      · have h2 : i₀ < m + 1 := by omega
        simp only [h1, h2, if_true]
        omega
      · have h2 : ¬ i₀ < m + 1 := by omega
        simp only [h1, h2, if_false]
        omega

@[expose] def cntB (n x : Nat) : Nat := (List.range n).countP fun a => x.testBit a

theorem cntB_land_pred {n x : Nat} (hx : x ≠ 0) (hn : x < 2 ^ n) :
    cntB n x = cntB n (x &&& (x - 1)) + 1 := by
  obtain ⟨i₀, h0, hb⟩ := testBit_land_pred x hx
  have hi : i₀ < n := by
    by_contra hc
    have : x < 2 ^ i₀ := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow this] at h0
    exact absurd h0 (by simp)
  unfold cntB
  rw [countP_range_split (fun a => x.testBit a) (fun a => (x &&& (x - 1)).testBit a) i₀
    (fun a => ?_) (by rw [hb]; simp), if_pos hi]
  rw [hb]
  by_cases h : a = i₀
  · subst h
    simp [h0]
  · have e1 : (a == i₀) = false := beq_false_of_ne h
    have e2 : (a != i₀) = true := bne_iff_ne.mpr h
    rw [e1, e2, Bool.and_true, Bool.or_false]

theorem cntB_le (n x : Nat) : cntB n x ≤ n := by
  unfold cntB
  exact Nat.le_trans List.countP_le_length (by simp)

theorem cntK_eq {n : Nat} : ∀ (f x : Nat), x < 2 ^ n → cntB n x ≤ f → cntK f x = cntB n x
  | 0, x, _, h => by
    rw [cntK_zero]
    omega
  | f + 1, x, hn, h => by
    rw [cntK_succ]
    by_cases hx : x = 0
    · subst hx
      simp [cntB]
    · have hb := cntB_land_pred hx hn
      have hlt : x &&& (x - 1) < 2 ^ n := lt_of_le_of_lt Nat.and_le_left hn
      rw [cntK_eq f _ hlt (by omega), ← hb]
      simp [hx]

theorem map_getD_range (P : List Nat) : (List.range P.length).map (fun j => P.getD j 0) = P := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem countP_eq_range (P : List Nat) (f : Nat → Bool) :
    P.countP f = (List.range P.length).countP (fun j => f (P.getD j 0)) := by
  conv_lhs => rw [← map_getD_range P]
  rw [List.countP_map]
  rfl

theorem meetCard_eq {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts) {i j : Nat} (hi : i < 891)
    (hj : j < 891) : meetCard i j = cntK 693 (P.getD i 0 &&& P.getD j 0) := by
  have hx : P.getD i 0 &&& P.getD j 0 < 2 ^ 693 := by
    rw [hP i hi, ← hlen]
    exact lt_of_le_of_lt Nat.and_le_left (ptBits_lt _ _)
  rw [cntK_eq 693 _ hx (cntB_le _ _)]
  unfold meetCard planePtsArr
  rw [CFSG.SmithL6.Kernel.ofFn_get! _ hi]
  unfold planePts cntB
  rw [List.filter_toArray, List.size_toArray, List.filter_filter, ← List.countP_eq_length_filter]
  refine List.countP_congr fun a ha => ?_
  have ha' : a < 693 := List.mem_range.mp ha
  have e : ∀ k < 891, inPlane k a = (P.getD k 0).testBit a := fun k hk => by
    rw [hP k hk, testBit_ptBits, hlen]
    simp only [inPlane, maskArr_get hk, hpts, CFSG.SmithL6.Kernel.get0, List.toList_toArray]
    simp [ha']
  rw [Nat.testBit_and, e i hi, e j hj, Bool.and_comm]

theorem ptChunkK_sound {M P L : List Nat} {s n : Nat} (h : ptChunkK M P L s n = true) {i : Nat}
    (h1 : s ≤ i) (h2 : i < s + n) : P.getD i 0 = ptBits (M.getD i 0) L := by
  unfold ptChunkK at h
  rw [List.all_eq_true] at h
  exact beq_iff_eq.mp (h i (List.mem_range'_1.mpr ⟨h1, h2⟩))

theorem d2ChunkK_sound {P : List Nat} {s n : Nat} (h : d2ChunkK P s n = true) {i : Nat}
    (h1 : s ≤ i) (h2 : i < s + n) : d2RowK P (P.getD i 0) = true := by
  unfold d2ChunkK at h
  rw [List.all_eq_true] at h
  exact h i (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem chkDist2_of {pts P : List Nat} (hpts : uPts () = pts.toArray) (hlen : pts.length = 693)
    (hPl : P.length = 891) (hP : ∀ i < 891, P.getD i 0 = ptBits (wMask i) pts)
    (hrow : ∀ i < 891, d2RowK P (P.getD i 0) = true) : chkDist2 = true := by
  unfold chkDist2
  rw [List.all_eq_true]
  intro i hi
  have hi' : i < 891 := List.mem_range.mp hi
  have h := hrow i hi'
  unfold d2RowK at h
  rw [← List.countP_eq_length_filter]
  have e : (List.range 891).countP (fun j => meetCard i j == 1) =
      P.countP (fun b => cntK 693 (P.getD i 0 &&& b) == 1) := by
    rw [countP_eq_range P, hPl]
    refine List.countP_congr fun j hj => ?_
    rw [meetCard_eq hpts hlen hP hi' (List.mem_range.mp hj)]
  rw [e]
  exact h

end CFSG.SmithE.K
