module

public import Certificates.Data.Kernel.Spor.RowWord
public import CFSG.Certificates.Kernel.Spor.RowSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.Row

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem rpermK_range {n w o o' : Nat} {F G : Nat → Nat}
    (h : rpermK n w (mask w) F o G o' = true) : ∀ i < n, rg w (mask w) F o i < n := by
  intro i hi
  have h1 := allN_spec h i hi
  rw [CFSG.KC.Enum.strictB] at h1
  have e : ∀ y : Nat, Nat.rec (motive := fun _ => Bool)
      ((fun v => Bool.rec (motive := fun _ => Bool) false
        (Nat.beq (rg w (mask w) G o' v) i) (Nat.blt v n)) 0)
      (fun m _ => (fun v => Bool.rec (motive := fun _ => Bool) false
        (Nat.beq (rg w (mask w) G o' v) i) (Nat.blt v n)) (Nat.succ m)) y =
      Bool.rec (motive := fun _ => Bool) false (Nat.beq (rg w (mask w) G o' y) i) (Nat.blt y n) :=
    fun y => by cases y <;> rfl
  rw [e] at h1
  exact Eq.mp Nat.blt_eq ((bAnd_iff _ _).1 h1).1

theorem rwordPt_eq {n w kS : Nat} {S Sinv : Array (Array Nat)} {F G O : Nat → Nat}
    (hS : ∀ j < kS, S[j]! = rowArr n w F (O j)) (hSi : ∀ j < kS, Sinv[j]! = rowArr n w G (O j))
    (hrF : ∀ j < kS, ∀ i < n, rg w (mask w) F (O j) i < n)
    (hrG : ∀ j < kS, ∀ i < n, rg w (mask w) G (O j) i < n) :
    ∀ (wd : List Int), lettersOK kS wd = true → ∀ x < n,
      (wordA n S Sinv wd)[x]! = rwordPt w (mask w) F G O wd x ∧
        rwordPt w (mask w) F G O wd x < n
  | [], _, x, hx => by
    refine ⟨?_, hx⟩
    rw [wordA, idA, getElem!_pos _ x (by simp [hx])]
    simp [rwordPt]
  | z :: rest, hl, x, hx => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hl
    obtain ⟨⟨hz0, hzk⟩, hrest⟩ := hl
    obtain ⟨ih1, ih2⟩ := rwordPt_eq hS hSi hrF hrG rest
      (by simpa [lettersOK] using hrest) x hx
    have ev : rwordPt w (mask w) F G O (z :: rest) x =
        rletter w (mask w) F G O z (rwordPt w (mask w) F G O rest x) := by
      change strictN (rwordPt w (mask w) F G O rest x) (fun y => rletter w (mask w) F G O z y) = _
      rw [strictN_app]
    rw [ev]
    have hw : (wordA n S Sinv (z :: rest))[x]! =
        (letterA S Sinv z)[(wordA n S Sinv rest)[x]!]! := by
      rw [wordA, compA, getElem!_pos _ x (by simp [hx])]
      simp
    rw [hw, ih1]
    cases z with
    | ofNat k =>
      have hk1 : 1 ≤ k := by
        rcases k with _ | k
        · exact absurd rfl hz0
        · omega
      have hnat : (Int.ofNat k).natAbs = k := rfl
      have hkS : k - 1 < kS := by omega
      have hpos : (0 : Int) < Int.ofNat k := Int.ofNat_lt.mpr hk1
      have hlet : letterA S Sinv (Int.ofNat k) = S[k - 1]! := by
        unfold letterA
        simp only [hpos, ↓reduceIte]
        rfl
      rw [hlet, hS _ hkS, rowArr_get ih2]
      exact ⟨rfl, hrF _ hkS _ ih2⟩
    | negSucc k =>
      have hkS : k < kS := by simp at hzk; omega
      have hlet : letterA S Sinv (Int.negSucc k) = Sinv[k]! := by
        simp [letterA]
      rw [hlet, hSi _ hkS, rowArr_get ih2]
      exact ⟨rfl, hrG _ hkS _ ih2⟩

end CFSG.KS.Row

end
