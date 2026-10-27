module

public import Certificates.Data.Kernel.PermCent.L33RepTwin
public import CFSG.Certificates.Kernel.PermCent.CVSound
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallCheckN
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Prop27.OddCoreCheck
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Certificates.Kernel.PkCV.L33R

open CFSG.GH74.GLS.Prop27 CFSG.ClassicalInvolution.Q3.TA3.Check

variable {n : Nat} [Small n]

theorem oddCoreAt_C (m : Nat) (CA CP : List (CV n)) :
    oddCoreAt m (CA.map ev) (CP.map ev) = oddCoreAtC m CA CP := by
  unfold oddCoreAt oddCoreAtC
  simp only [List.all_map, List.any_map, Function.comp_def, ev_pow', ev_mul', ev_inv', one_eq_ev,
    decide_ev_eq, pow_fast, ne_eq, decide_not]

theorem oddCoreRep_C (m : Nat) (LA LP : List (CV n)) (τ : CV n) :
    oddCoreAt m ((LA.map ev).filter fun g => decide (g * ev τ = ev τ * g))
      ((LP.map ev).filter fun c => decide (c * ev τ = ev τ * c)) = oddCoreRepC m LA LP τ := by
  unfold oddCoreRepC
  simp only [List.filter_map, Function.comp_def, ev_mul', decide_ev_eq, comm_fast]
  exact oddCoreAt_C m _ _

theorem ordAux_C (o : CV n) : ∀ (fuel k : Nat) (acc : CV n), acc = o ^ k →
    ordAux (ev o) fuel k = ordRunC o fuel acc k
  | 0, _, _, _ => rfl
  | fuel + 1, k, acc, h => by
    have e : ev o ^ k = 1 ↔ acc = 1 := by rw [ev_pow', one_eq_ev, ev_eq_iff, h]
    have ih := ordAux_C o fuel (k + 1) (acc * o) (by rw [h, pow_succ])
    rw [ordAux, ordRunC]
    by_cases ha : acc = 1
    · rw [if_pos (e.2 ha), if_pos ha]
    · rw [if_neg (mt e.1 ha), if_neg ha, ih]

theorem ordB_C (B : Nat) (o : CV n) : ordB B (ev o) = ordBC B o :=
  ordAux_C o B 1 o (pow_one o).symm

theorem noOddB_C (B : Nat) (C : List (CV n)) : noOddB B (C.map ev) = noOddBC B C := by
  unfold noOddB noOddBC
  simp only [List.all_map, List.any_map, Function.comp_def, ev_mul', ev_inv', one_eq_ev,
    decide_ev_eq, ordB_C]

theorem memB_C (L : List (CV n)) (x : CV n) : memB (L.map ev) (ev x) = memC L x := by
  unfold memB memC
  simp only [List.any_map, Function.comp_def, decide_ev_eq]

theorem q8B_C (t a b : CV n) : q8B (ev t) (ev a) (ev b) = (q8C t a b).map ev := by
  unfold q8B q8C
  simp only [List.map_cons, List.map_nil, ev_mul, ev_one]

theorem pow3_C (a : CV n) : decide (ev a ^ 3 = 1) = powOneC a 3 := by
  rw [ev_pow', one_eq_ev, decide_ev_eq, pow_fast]

theorem pairsN_C (LN : List (CV n)) (t : CV n) (C : List (CV n)) :
    pairsN (LN.map ev) (ev t) (C.map ev) = pairsNC LN t C := by
  unfold pairsN pairsNC
  simp only [List.filter_map, List.all_map, List.any_map, Function.comp_def, q8B_C, pow3_C]
  simp only [ev_mul', ev_inv', one_eq_ev, memB_C, decide_ev_eq, Bool.decide_and, comm_fast]

theorem goodAt_C (B : Nat) (LN L : List (CV n)) (t : CV n) :
    (noOddB B (centB (L.map ev) (ev t)) && pairsN (LN.map ev) (ev t) (centB (L.map ev) (ev t))) =
      goodAtC B LN L t := by
  have e : centB (L.map ev) (ev t) = (L.filter fun c => eq22C c t t c).map ev := by
    unfold centB
    simp only [List.filter_map, Function.comp_def, ev_mul', decide_ev_eq, comm_fast]
  rw [e, noOddB_C, pairsN_C]
  rfl

end CFSG.Certificates.Kernel.PkCV.L33R

end
