module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3Sound
public import Certificates.Data.Kernel.G2Three.Sec1F
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.G2Three.Sec1T3

open CFSG.KD.G2Three.Sec1T3 CFSG.KD.G2Three.Sec1 CFSG.KC.Loop

abbrev parA (PA j : ℕ) : ℕ := fld(PA, Nat.mul 7 j, 127)

theorem tabK_spec {P RT PA PB lo m : ℕ} (h : tabK P RT PA PB lo m = true) (hm : m ≤ 128)
    (i : ℕ) (h1 : lo ≤ i) (h2 : i < lo + m) : atR (rowT P i) 0 = i ∧
      ∀ j < 127, atR (rowT P i) (j + 1) = rtA RT (atR (rowT P i) (parA PA j)) (parA PB j) := by
  have := allBelow_spec h (by omega) (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  dsimp only at this
  rw [e, bAnd_eq, Bool.and_eq_true, recAnd_iff] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, fun j hj => Nat.eq_of_beq_eq_true (this.2 j hj)⟩

theorem colK_spec {P C lo m : ℕ} (h : colK P C lo m = true) (hm : m ≤ 128)
    (i : ℕ) (h1 : lo ≤ i) (h2 : i < lo + m) : ∀ j < 128, atR (rowT C j) i = atR (rowT P i) j := by
  have := allBelow_spec h (by omega) (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  dsimp only at this
  rw [e, recAnd_iff] at this
  exact fun j hj => Nat.eq_of_beq_eq_true (this j hj)

theorem invK_spec {P V : ℕ} (h : invK P V = true) : ∀ i < 128, atR (rowT P i) (atR V i) = 0 :=
  fun i hi => Nat.eq_of_beq_eq_true (allBelow_spec h (by decide) i hi)

theorem sqK_spec {P Q : ℕ} (h : sqK P Q = true) : ∀ i < 128, atR Q i = atR (rowT P i) i :=
  fun i hi => Nat.eq_of_beq_eq_true (allBelow_spec h (by decide) i hi)

theorem parR_spec {RT PA PB m hi : ℕ} (h : parR RT PA PB m hi = true) (hm : m ≤ 64 * hi) :
    ∀ j < m, parA PA j ≤ j ∧ parA PB j < 6 ∧ rtA RT (parA PA j) (parA PB j) = j + 1 := by
  intro j hj
  have := allBelow_spec h hm j hj
  dsimp only at this
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at this
  exact ⟨Nat.le_of_ble_eq_true this.1, by have := this.2.1; rwa [Nat.blt_eq] at this,
    Nat.eq_of_beq_eq_true this.2.2⟩

variable {G : Type} [Group G]

theorem realT_of {elt g : ℕ → G} {P C V Q RT PA PB : ℕ} (h1 : elt 0 = 1)
    (hrt : ∀ i < 128, ∀ s < 6, rtA RT i s < 128 ∧ elt (rtA RT i s) = elt i * g s)
    (hinj : ∀ i < 128, ∀ j < 128, elt i = elt j → i = j)
    (hpar : ∀ j < 127, parA PA j ≤ j ∧ parA PB j < 6 ∧ rtA RT (parA PA j) (parA PB j) = j + 1)
    (htab : ∀ i < 128, atR (rowT P i) 0 = i ∧
      ∀ j < 127, atR (rowT P i) (j + 1) = rtA RT (atR (rowT P i) (parA PA j)) (parA PB j))
    (hcol : ∀ i < 128, ∀ j < 128, atR (rowT C j) i = atR (rowT P i) j)
    (hinv : ∀ i < 128, atR (rowT P i) (atR V i) = 0)
    (hsq : ∀ i < 128, atR Q i = atR (rowT P i) i) : RealT elt P C V Q := by
  have hmul : ∀ i < 128, ∀ j < 128, elt (atR (rowT P i) j) = elt i * elt j := by
    intro i hi j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases j with _ | j
      · rw [(htab i hi).1, h1, mul_one]
      · obtain ⟨hpa, hpb, hp⟩ := hpar j (by omega)
        rw [(htab i hi).2 j (by omega), (hrt _ (atR_lt _ _) _ hpb).2, ih _ (by omega) (by omega),
          mul_assoc, ← (hrt _ (by omega) _ hpb).2, hp]
  refine ⟨h1, fun i hi j hj => ⟨atR_lt _ _, hmul i hi j hj⟩, hcol, fun i hi => ⟨atR_lt _ _, ?_⟩,
    hsq, hinj⟩
  have := hmul i hi _ (atR_lt V i)
  rw [hinv i hi, h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm

end CFSG.KC.G2Three.Sec1T3
