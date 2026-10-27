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

theorem s8_check : enumS8e s8test = true := by
  decide +kernel

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
