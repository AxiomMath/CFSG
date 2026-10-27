module

public import CFSG.Certificates.Kernel.E7Orbit.Sound
public import Certificates.Data.OmegaSevenMax.Defs
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.E7Orbit

open Certificates.OmegaSevenMax CFSG.KC.Enum CFSG.KC.Benes

theorem ndiv_eq (a b : Nat) : Nat.div a b = a / b := rfl

theorem nmod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

def eD (u c m d : Nat) : Nat := (c / d % 3 + m * (u / d % 3)) % 3

theorem rxM_eq (u c m : Nat) : rxM u c m = eD u c m 1 + 3 * eD u c m 3 + 9 * eD u c m 9 +
    27 * eD u c m 27 + 81 * eD u c m 81 + 243 * eD u c m 243 + 729 * eD u c m 729 := by
  simp only [rxM, rxD, dg, eD, nadd, nmul, ndiv_eq, nmod_eq]
  ring

theorem eD_lt (u c m d : Nat) : eD u c m d < 3 := Nat.mod_lt _ (by decide)

theorem decV_digits (a b c d e f g : Nat) (ha : a < 3) (hb : b < 3) (hc : c < 3) (hd : d < 3)
    (he : e < 3) (hf : f < 3) (hg : g < 3) :
    decV (a + 3 * b + 9 * c + 27 * d + 81 * e + 243 * f + 729 * g) =
      ![(a : ZMod 3), b, c, d, e, f, g] := by
  have key : ∀ k : Fin 7, (a + 3 * b + 9 * c + 27 * d + 81 * e + 243 * f + 729 * g) / 3 ^ (k : ℕ) % 3 =
      ![a, b, c, d, e, f, g] k := by
    intro k
    fin_cases k <;> norm_num <;> omega
  funext i
  simp only [decV]
  rw [key i]
  fin_cases i <;> rfl

theorem natCast_eD (u c m d : Nat) :
    ((eD u c m d : Nat) : ZMod 3) = ((c / d % 3 : Nat) : ZMod 3) + (m : ZMod 3) * ((u / d % 3 : Nat) : ZMod 3) := by
  simp only [eD, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul]

theorem polarV_decV (u c : Nat) : polarV (decV u) (decV c) = ((2 * polS u c : Nat) : ZMod 3) := by
  simp only [polarV, decV, polS, pr, dg, nadd, nmul, ndiv_eq, nmod_eq]
  norm_num
  ring

theorem decV_rxN (u c : Nat) : decV (rxN u c) = rxV (decV u) (decV c) := by
  unfold rxN
  rw [strictN_eq, rxM_eq, decV_digits _ _ _ _ _ _ _ (eD_lt ..) (eD_lt ..) (eD_lt ..) (eD_lt ..)
    (eD_lt ..) (eD_lt ..) (eD_lt ..)]
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hm : ∀ m : Nat, m = Nat.mul 2 (Nat.mod (Nat.mul 2 (polS u c)) 3) →
      (m : ZMod 3) = -polarV (decV u) (decV c) := by
    intro m e
    rw [e, polarV_decV, nmul, nmul, nmod_eq, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul]
    push_cast
    linear_combination (2 * ((polS u c : Nat) : ZMod 3)) * h3
  generalize em : Nat.mul (nat_lit 2) (Nat.mod (Nat.mul (nat_lit 2) (polS u c)) (nat_lit 3)) = m
  have hm' := hm m em.symm
  funext i
  simp only [rxV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, natCast_eD, hm']
  fin_cases i <;> simp only [decV] <;> norm_num <;> ring

theorem rxM_lt (u c m : Nat) : rxM u c m < 2187 := by
  rw [rxM_eq]
  have h1 := eD_lt u c m 1
  have h3 := eD_lt u c m 3
  have h9 := eD_lt u c m 9
  have h27 := eD_lt u c m 27
  have h81 := eD_lt u c m 81
  have h243 := eD_lt u c m 243
  have h729 := eD_lt u c m 729
  omega

theorem rxN_lt (u c : Nat) : rxN u c < 2187 := by
  unfold rxN
  rw [strictN_eq]
  exact rxM_lt _ _ _

theorem decV_gF (k p : Nat) :
    decV (gF k p) = rxV (decV (pg 12 4095 uP k)) (rxV (decV (pg 12 4095 wP k)) (decV p)) := by
  unfold gF
  rw [decV_rxN, decV_rxN]

theorem decV_hN (j p : Nat) :
    decV (hN j p) = rxV (decV 1) (rxV (decV (3 ^ (j + 1))) (decV p)) := by
  unfold hN
  rw [decV_rxN, decV_rxN]
  rfl

end CFSG.KC.E7Orbit

end
