module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL42Data

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L42Insp

set_option maxRecDepth 100000

@[expose] def p0L : List Nat := p0W.map pw

@[expose] def ptau0 : Nat := pw [0, 2, 4, 6]

@[expose] def evenW (w : List Nat) : Bool := w.all (· < 7) && w.length % 2 == 0

@[expose] def hasFix (a : Nat) : Bool := (List.range 8).any fun i => pd a i == i

theorem p0_check :
    (p0W.all evenW) = true ∧ pone ∈ p0L ∧
      (∀ w₁ ∈ p0W, ∀ w₂ ∈ p0W, pm (pw w₁) (pw w₂) ∈ p0L) ∧ (∀ w ∈ p0W, pw w.reverse ∈ p0L) ∧
      p0L.Nodup ∧ p0L.length = 64 ∧ (∀ p ∈ p0L, pm ptau0 p = pm p ptau0) ∧
      (∀ g ∈ p0genW, pw g ∈ p0L) := by
  decide +kernel

@[expose] def s8test (σ : Nat) : Bool :=
  (!(p0genW.all fun g => pm σ (pw g) == pm (pw g) σ) || σ == pone || σ == ptau0) &&
    (!(pm σ σ == pone) || hasFix σ || σ == ptau0 || keyTbl.any fun e => e.1 == σ)

private def enumS8eFrom (f : Nat → Bool) (j0 : Nat) : Bool :=
  (List.range' 1 7).all fun j1 => (List.range' 2 6).all fun j2 =>
  (List.range' 3 5).all fun j3 => (List.range' 4 4).all fun j4 => (List.range' 5 3).all fun j5 =>
  (List.range' 6 2).all fun j6 =>
    ((if j0 = 0 then 0 else 1) + (if j1 = 1 then 0 else 1) + (if j2 = 2 then 0 else 1) +
      (if j3 = 3 then 0 else 1) + (if j4 = 4 then 0 else 1) + (if j5 = 5 then 0 else 1) +
      (if j6 = 6 then 0 else 1)) % 2 != 0 ||
    f (pm (pm (pm (pm (pm (pm (pswap 0 j0) (pswap 1 j1)) (pswap 2 j2)) (pswap 3 j3)) (pswap 4 j4))
      (pswap 5 j5)) (pswap 6 j6))

private theorem s8_check_0 : enumS8eFrom s8test 0 = true := by decide +kernel
private theorem s8_check_1 : enumS8eFrom s8test 1 = true := by decide +kernel
private theorem s8_check_2 : enumS8eFrom s8test 2 = true := by decide +kernel
private theorem s8_check_3 : enumS8eFrom s8test 3 = true := by decide +kernel
private theorem s8_check_4 : enumS8eFrom s8test 4 = true := by decide +kernel
private theorem s8_check_5 : enumS8eFrom s8test 5 = true := by decide +kernel
private theorem s8_check_6 : enumS8eFrom s8test 6 = true := by decide +kernel
private theorem s8_check_7 : enumS8eFrom s8test 7 = true := by decide +kernel

theorem s8_check : enumS8e s8test = true := by
  change (List.range' 0 8).all (enumS8eFrom s8test) = true
  rw [List.all_eq_true]
  intro j hj
  rw [List.mem_range'_1] at hj
  match j, hj with
  | 0, _ => exact s8_check_0
  | 1, _ => exact s8_check_1
  | 2, _ => exact s8_check_2
  | 3, _ => exact s8_check_3
  | 4, _ => exact s8_check_4
  | 5, _ => exact s8_check_5
  | 6, _ => exact s8_check_6
  | 7, _ => exact s8_check_7
  | _ + 8, h => exact absurd h.2 (by omega)

@[expose] def yw (i : Nat) : List Nat := repY.getD i []

theorem entry_check : ∀ e ∈ keyTbl, e.2.1 < 6 ∧ evenW e.2.2 = true ∧
    pm (pw e.2.2) ptau0 = pm ptau0 (pw e.2.2) ∧
    pm (pm (pw e.2.2) (pm e.1 (pw e.2.2.reverse))) (pw (yw e.2.1)) = pm (pw (yw e.2.1)) ptau0 := by
  decide +kernel

@[expose] def blocks (i : Nat) : List (List Nat) := c0genW ++ [yw i, [0] ++ yw i ++ [0]]

@[expose] def pwb (B : List (List Nat)) (w : List Nat) : Nat :=
  (w.map fun n => if n % 2 = 0 then pw (B.getD (n / 2) []) else pw (B.getD (n / 2) []).reverse).foldr
    pm pone

theorem gens_check : (∀ g ∈ c0genW, evenW g = true ∧ pm (pw g) ptau0 = pm ptau0 (pw g)) ∧
    (∀ i < 6, evenW (yw i) = true) := by
  decide +kernel

theorem cert_check : ∀ i < 6, ∀ j < 6,
    pwb (blocks i) ((repCert.getD i []).getD j []) = pm (pswap 0 1) (pswap 1 (j + 2)) := by
  decide +kernel

@[expose] def pgam (n : Nat) : Nat :=
  if n % 2 = 0 then pm (pswap 0 1) (pswap 1 (n / 2 + 2)) else pm (pswap 1 (n / 2 + 2)) (pswap 0 1)

@[expose] def pwg (w : List Nat) : Nat := (w.map pgam).foldr pm pone

theorem tri_check :
    ((List.range 8).all fun a => (List.range 8).all fun b => (List.range 8).all fun c =>
      a == b || b == c || a == c ||
        (pwg (triTbl.getD (64 * a + 8 * b + c) []) == pm (pswap a b) (pswap b c) &&
          (triTbl.getD (64 * a + 8 * b + c) []).all (· < 12))) = true := by
  decide +kernel

end CFSG.QuasithinUnique.Vol2Native.L239.L42Insp
