module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.GLTheoremA.YS05NonIso

theorem sf2 {p e A B : ℕ} (hp : p.Prime) (hAB : ¬ p ∣ Nat.gcd A B) (h : p ^ e ∣ A * B) :
    p ^ e ∣ A ∨ p ^ e ∣ B := by
  by_cases hA : p ∣ A
  · have hB : ¬ p ∣ B := fun hB => hAB (Nat.dvd_gcd hA hB)
    exact Or.inl ((Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hB)).dvd_of_dvd_mul_right h)
  · exact Or.inr ((Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hA)).dvd_of_dvd_mul_left h)

theorem sf3 {p e A B C : ℕ} (hp : p.Prime) (hAB : ¬ p ∣ Nat.gcd A B) (hAC : ¬ p ∣ Nat.gcd A C)
    (hBC : ¬ p ∣ Nat.gcd B C) (h : p ^ e ∣ A * B * C) : p ^ e ∣ A ∨ p ^ e ∣ B ∨ p ^ e ∣ C := by
  have hA : ¬ p ∣ Nat.gcd A (B * C) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · exact hAB (Nat.dvd_gcd h1 h3)
    · exact hAC (Nat.dvd_gcd h1 h3)
  rcases sf2 hp hA (by rwa [mul_assoc] at h) with h1 | h1
  · exact Or.inl h1
  · rcases sf2 hp hBC h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h2)

theorem dvd_of_combo {p a b c k m : ℕ} (ha : p ∣ a) (hb : p ∣ b) (h : a * k + c = b * m) :
    p ∣ c := by
  have h1 : p ∣ a * k + c := by rw [h]; exact Dvd.dvd.mul_right hb m
  exact (Nat.dvd_add_right (Dvd.dvd.mul_right ha k)).1 h1

theorem contra_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2) : False :=
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)

theorem contra_three {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (h : p ∣ 3) : False :=
  hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)

theorem contra_one {p : ℕ} (hp : p.Prime) (h : p ∣ 1) : False :=
  hp.one_lt.ne' (Nat.dvd_one.1 h)

theorem pf_u_u2 {p u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ u) (h2 : p ∣ u + 2) : False :=
  contra_two hp hp2 (dvd_of_combo h1 h2 (k := 1) (m := 1) (by ring))

theorem pf_u_q {p u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ u) (h2 : p ∣ u ^ 2 + 2 * u + 2) :
    False :=
  contra_two hp hp2 (dvd_of_combo h1 h2 (k := u + 2) (m := 1) (by ring))

theorem pf_u2_q {p u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h1 : p ∣ u + 2)
    (h2 : p ∣ u ^ 2 + 2 * u + 2) : False :=
  contra_two hp hp2 (dvd_of_combo h1 h2 (k := u) (m := 1) (by ring))

theorem pf_u2_3 {p u : ℕ} (hp : p.Prime) (h1 : p ∣ u + 2) (h2 : p ∣ u ^ 2 + 3 * u + 3) : False :=
  contra_one hp (dvd_of_combo h1 h2 (k := u + 1) (m := 1) (by ring))

theorem pf_q_y {p u : ℕ} (hpy : ¬ p ∣ u + 1) (h1 : p ∣ u ^ 2 + 2 * u + 2)
    (h2 : p ∣ u ^ 2 + 3 * u + 3) : False :=
  hpy (dvd_of_combo h1 h2 (k := 1) (m := 1) (by ring))

theorem pf_u_3 {p u : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (h1 : p ∣ u) (h2 : p ∣ u ^ 2 + 3 * u + 3) :
    False :=
  contra_three hp hp3 (dvd_of_combo h1 h2 (k := u + 3) (m := 1) (by ring))

theorem pf_u_u2u1 {p u : ℕ} (hp : p.Prime) (h1 : p ∣ u) (h2 : p ∣ u ^ 2 + u + 1) : False :=
  contra_one hp (dvd_of_combo h1 h2 (k := u + 1) (m := 1) (by ring))

theorem pf_u2u1_y {p u : ℕ} (hpy : ¬ p ∣ u + 1) (h1 : p ∣ u ^ 2 + u + 1)
    (h2 : p ∣ u ^ 2 + 2 * u + 2) : False :=
  hpy (dvd_of_combo h1 h2 (k := 1) (m := 1) (by ring))

theorem pf_u2_u2u1 {p u : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hu : 1 ≤ u) (h1 : p ∣ u + 2)
    (h2 : p ∣ u ^ 2 + u + 1) : False := by
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
  exact contra_three hp hp3 (dvd_of_combo h1 h2 (k := w) (m := 1) (by ring))

theorem bnd_Sp4 {p e u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hu : 1 ≤ u)
    (h : p ^ e ∣ u ^ 2 * (u + 2) ^ 2 * (u ^ 2 + 2 * u + 2)) : p ^ e ≤ (u + 2) ^ 2 := by
  have hpu : ∀ {d : ℕ}, p ∣ d ^ 2 → p ∣ d := fun h2 => hp.dvd_of_dvd_pow h2
  have hAB : ¬ p ∣ Nat.gcd (u ^ 2) ((u + 2) ^ 2) := fun hg =>
    pf_u_u2 hp hp2 (hpu (hg.trans (Nat.gcd_dvd_left _ _))) (hpu (hg.trans (Nat.gcd_dvd_right _ _)))
  have hAC : ¬ p ∣ Nat.gcd (u ^ 2) (u ^ 2 + 2 * u + 2) := fun hg =>
    pf_u_q hp hp2 (hpu (hg.trans (Nat.gcd_dvd_left _ _))) (hg.trans (Nat.gcd_dvd_right _ _))
  have hBC : ¬ p ∣ Nat.gcd ((u + 2) ^ 2) (u ^ 2 + 2 * u + 2) := fun hg =>
    pf_u2_q hp hp2 (hpu (hg.trans (Nat.gcd_dvd_left _ _))) (hg.trans (Nat.gcd_dvd_right _ _))
  rcases sf3 hp hAB hAC hBC h with h1 | h1 | h1
  · calc p ^ e ≤ u ^ 2 := Nat.le_of_dvd (by positivity) h1
      _ ≤ (u + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  · exact Nat.le_of_dvd (by positivity) h1
  · exact (Nat.le_of_dvd (by positivity) h1).trans (by nlinarith)

theorem bnd_L4s {p e u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpy : ¬ p ∣ u + 1) (hu : 1 ≤ u)
    (h : p ^ e ∣ u ^ 3 * (u ^ 2 + 3 * u + 3) * ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2))) :
    p ^ e ≤ (u + 2) ^ 5 := by
  have hA : ¬ p ∣ Nat.gcd (u ^ 3 * (u ^ 2 + 3 * u + 3)) ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2)) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3 <;>
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
    · exact pf_u_u2 hp hp2 (hp.dvd_of_dvd_pow h3) (hp.dvd_of_dvd_pow h4)
    · exact pf_u_q hp hp2 (hp.dvd_of_dvd_pow h3) h4
    · exact pf_u2_3 hp (hp.dvd_of_dvd_pow h4) h3
    · exact pf_q_y hpy h4 h3
  have hA0 : 0 < u ^ 3 * (u ^ 2 + 3 * u + 3) * ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2)) := by
    have : 0 < u := by omega
    positivity
  rcases sf2 hp hA h with h1 | h1
  · exact (Nat.le_of_dvd (by positivity) h1).trans (by nlinarith)
  · refine (Nat.le_of_dvd (by positivity) h1).trans ?_
    calc (u + 2) ^ 2 * (u ^ 2 + 2 * u + 2) ≤ (u + 2) ^ 2 * (u + 2) ^ 3 :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = (u + 2) ^ 5 := by ring

theorem bnd_L4b {p e u : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpy : ¬ p ∣ u + 1) (hu : 1 ≤ u)
    (h : p ^ e ∣ u ^ 3 * (u ^ 2 + 3 * u + 3) * ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2))) :
    p ^ e ≤ (u + 2) ^ 3 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hA : ¬ p ∣ Nat.gcd (u ^ 3 * (u ^ 2 + 3 * u + 3)) ((u + 2) ^ 2 * (u ^ 2 + 2 * u + 2)) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3 <;>
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
    · exact pf_u_u2 hp hp2 (hp.dvd_of_dvd_pow h3) (hp.dvd_of_dvd_pow h4)
    · exact pf_u_q hp hp2 (hp.dvd_of_dvd_pow h3) h4
    · exact pf_u2_3 hp (hp.dvd_of_dvd_pow h4) h3
    · exact pf_q_y hpy h4 h3
  rcases sf2 hp hA h with h1 | h1
  · rcases sf2 hp (A := u ^ 3) (B := u ^ 2 + 3 * u + 3) (fun hg =>
      pf_u_3 hp hp3 (hp.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_left _ _)))
        (hg.trans (Nat.gcd_dvd_right _ _))) h1 with h2 | h2
    · exact (Nat.le_of_dvd (by positivity) h2).trans (Nat.pow_le_pow_left (by omega) 3)
    · exact (Nat.le_of_dvd (by positivity) h2).trans (by nlinarith)
  · rcases sf2 hp (A := (u + 2) ^ 2) (B := u ^ 2 + 2 * u + 2) (fun hg =>
      pf_u2_q hp hp2 (hp.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_left _ _)))
        (hg.trans (Nat.gcd_dvd_right _ _))) h1 with h2 | h2
    · exact (Nat.le_of_dvd (by positivity) h2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact (Nat.le_of_dvd (by positivity) h2).trans (by nlinarith)

theorem bnd_U4s {p e u : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpy : ¬ p ∣ u + 1) (hu : 1 ≤ u)
    (h : p ^ e ∣ (u + 2) ^ 3 * (u ^ 2 + u + 1) * (u ^ 2 * (u ^ 2 + 2 * u + 2))) :
    p ^ e ≤ (u + 2) ^ 5 := by
  have hA : ¬ p ∣ Nat.gcd ((u + 2) ^ 3 * (u ^ 2 + u + 1)) (u ^ 2 * (u ^ 2 + 2 * u + 2)) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3 <;>
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
    · exact pf_u_u2 hp hp2 (hp.dvd_of_dvd_pow h4) (hp.dvd_of_dvd_pow h3)
    · exact pf_u2_q hp hp2 (hp.dvd_of_dvd_pow h3) h4
    · exact pf_u_u2u1 hp (hp.dvd_of_dvd_pow h4) h3
    · exact pf_u2u1_y hpy h3 h4
  rcases sf2 hp hA h with h1 | h1
  · refine (Nat.le_of_dvd (by positivity) h1).trans ?_
    calc (u + 2) ^ 3 * (u ^ 2 + u + 1) ≤ (u + 2) ^ 3 * (u + 2) ^ 2 :=
          Nat.mul_le_mul_left _ (by nlinarith)
      _ = (u + 2) ^ 5 := by ring
  · refine (Nat.le_of_dvd (by positivity) h1).trans ?_
    calc u ^ 2 * (u ^ 2 + 2 * u + 2) ≤ (u + 2) ^ 2 * (u + 2) ^ 3 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 2) (by nlinarith)
      _ = (u + 2) ^ 5 := by ring

theorem bnd_U4b {p e u : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpy : ¬ p ∣ u + 1) (hu : 1 ≤ u)
    (h : p ^ e ∣ (u + 2) ^ 3 * (u ^ 2 + u + 1) * (u ^ 2 * (u ^ 2 + 2 * u + 2))) :
    p ^ e ≤ (u + 2) ^ 3 := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hA : ¬ p ∣ Nat.gcd ((u + 2) ^ 3 * (u ^ 2 + u + 1)) (u ^ 2 * (u ^ 2 + 2 * u + 2)) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3 <;>
      rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h4
    · exact pf_u_u2 hp hp2 (hp.dvd_of_dvd_pow h4) (hp.dvd_of_dvd_pow h3)
    · exact pf_u2_q hp hp2 (hp.dvd_of_dvd_pow h3) h4
    · exact pf_u_u2u1 hp (hp.dvd_of_dvd_pow h4) h3
    · exact pf_u2u1_y hpy h3 h4
  rcases sf2 hp hA h with h1 | h1
  · rcases sf2 hp (A := (u + 2) ^ 3) (B := u ^ 2 + u + 1) (fun hg =>
      pf_u2_u2u1 hp hp3 hu (hp.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_left _ _)))
        (hg.trans (Nat.gcd_dvd_right _ _))) h1 with h2 | h2
    · exact Nat.le_of_dvd (by positivity) h2
    · exact (Nat.le_of_dvd (by positivity) h2).trans (by nlinarith)
  · rcases sf2 hp (A := u ^ 2) (B := u ^ 2 + 2 * u + 2) (fun hg =>
      pf_u_q hp hp2 (hp.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_left _ _)))
        (hg.trans (Nat.gcd_dvd_right _ _))) h1 with h2 | h2
    · exact (Nat.le_of_dvd (by positivity) h2).trans (by nlinarith)
    · exact (Nat.le_of_dvd (by positivity) h2).trans (by nlinarith)

theorem bnd_L3s {s e v : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) (hv : 1 ≤ v)
    (h : s ^ e ∣ v ^ 2 * (v + 2) * (v ^ 2 + 3 * v + 3)) : s ^ e ≤ (v + 2) ^ 2 := by
  have hs2 : s ≠ 2 := by omega
  have hs3 : s ≠ 3 := by omega
  have hpv : ∀ {d : ℕ}, s ∣ d ^ 2 → s ∣ d := fun h2 => hs.dvd_of_dvd_pow h2
  have hAB : ¬ s ∣ Nat.gcd (v ^ 2) (v + 2) := fun hg =>
    pf_u_u2 hs hs2 (hpv (hg.trans (Nat.gcd_dvd_left _ _))) (hg.trans (Nat.gcd_dvd_right _ _))
  have hAC : ¬ s ∣ Nat.gcd (v ^ 2) (v ^ 2 + 3 * v + 3) := fun hg =>
    pf_u_3 hs hs3 (hpv (hg.trans (Nat.gcd_dvd_left _ _))) (hg.trans (Nat.gcd_dvd_right _ _))
  have hBC : ¬ s ∣ Nat.gcd (v + 2) (v ^ 2 + 3 * v + 3) := fun hg =>
    pf_u2_3 hs (hg.trans (Nat.gcd_dvd_left _ _)) (hg.trans (Nat.gcd_dvd_right _ _))
  rcases sf3 hs hAB hAC hBC h with h1 | h1 | h1
  · exact (Nat.le_of_dvd (by positivity) h1).trans (Nat.pow_le_pow_left (by omega) 2)
  · exact (Nat.le_of_dvd (by omega) h1).trans (by nlinarith)
  · exact (Nat.le_of_dvd (by positivity) h1).trans (by nlinarith)

theorem bnd_L33 {e v : ℕ} (hv : 1 ≤ v) (h0 : 3 ^ e ∣ v ^ 2 * (v + 2) * (v ^ 2 + 3 * v + 3)) :
    3 ^ e ≤ (v + 2) ^ 4 := by
  have h : 3 ^ e ∣ v ^ 2 * (v ^ 2 + 3 * v + 3) * (v + 2) := by
    rwa [show v ^ 2 * (v ^ 2 + 3 * v + 3) * (v + 2) = v ^ 2 * (v + 2) * (v ^ 2 + 3 * v + 3) by ring]
  have hA : ¬ 3 ∣ Nat.gcd (v ^ 2 * (v ^ 2 + 3 * v + 3)) (v + 2) := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h3 | h3
    · exact pf_u_u2 Nat.prime_three (by decide) (Nat.prime_three.dvd_of_dvd_pow h3) h2
    · exact pf_u2_3 Nat.prime_three h2 h3
  rcases sf2 Nat.prime_three hA h with h1 | h1
  · refine (Nat.le_of_dvd (by positivity) h1).trans ?_
    nlinarith
  · exact (Nat.le_of_dvd (by omega) h1).trans (le_self_pow (a := v + 2) (n := 4) (by omega) (by norm_num))

theorem bnd_U3s {s e v : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) (hv : 1 ≤ v)
    (h : s ^ e ∣ v * (v + 2) ^ 2 * (v ^ 2 + v + 1)) : s ^ e ≤ (v + 2) ^ 2 := by
  have hs2 : s ≠ 2 := by omega
  have hs3 : s ≠ 3 := by omega
  have hAB : ¬ s ∣ Nat.gcd v ((v + 2) ^ 2) := fun hg =>
    pf_u_u2 hs hs2 (hg.trans (Nat.gcd_dvd_left _ _))
      (hs.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_right _ _)))
  have hAC : ¬ s ∣ Nat.gcd v (v ^ 2 + v + 1) := fun hg =>
    pf_u_u2u1 hs (hg.trans (Nat.gcd_dvd_left _ _)) (hg.trans (Nat.gcd_dvd_right _ _))
  have hBC : ¬ s ∣ Nat.gcd ((v + 2) ^ 2) (v ^ 2 + v + 1) := fun hg =>
    pf_u2_u2u1 hs hs3 hv (hs.dvd_of_dvd_pow (hg.trans (Nat.gcd_dvd_left _ _)))
      (hg.trans (Nat.gcd_dvd_right _ _))
  rcases sf3 hs hAB hAC hBC h with h1 | h1 | h1
  · exact (Nat.le_of_dvd (by omega) h1).trans (by nlinarith)
  · exact (Nat.le_of_dvd (by positivity) h1).trans (by nlinarith)
  · exact (Nat.le_of_dvd (by positivity) h1).trans (by nlinarith)

theorem bnd_U33 {e v : ℕ} (hv : 1 ≤ v) (h0 : 3 ^ e ∣ v * (v + 2) ^ 2 * (v ^ 2 + v + 1)) :
    3 ^ e ≤ (v + 2) ^ 4 := by
  have h : 3 ^ e ∣ (v + 2) ^ 2 * (v ^ 2 + v + 1) * v := by
    rwa [show (v + 2) ^ 2 * (v ^ 2 + v + 1) * v = v * (v + 2) ^ 2 * (v ^ 2 + v + 1) by ring]
  have hA : ¬ 3 ∣ Nat.gcd ((v + 2) ^ 2 * (v ^ 2 + v + 1)) v := by
    intro hg
    have h1 := hg.trans (Nat.gcd_dvd_left _ _)
    have h2 := hg.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h3 | h3
    · exact pf_u_u2 Nat.prime_three (by decide) h2 (Nat.prime_three.dvd_of_dvd_pow h3)
    · exact pf_u_u2u1 Nat.prime_three h2 h3
  rcases sf2 Nat.prime_three hA h with h1 | h1
  · refine (Nat.le_of_dvd (by positivity) h1).trans ?_
    nlinarith
  · exact (Nat.le_of_dvd (by omega) h1).trans ((Nat.le_add_right v 2).trans
      (le_self_pow (a := v + 2) (n := 4) (by omega) (by norm_num)))

theorem fin_a {u v : ℕ} (hu : 1 ≤ u) (h1 : (u + 1) ^ 4 ≤ (v + 2) ^ 2)
    (h2 : (v + 1) ^ 3 ≤ (u + 2) ^ 2) : False := by
  have h1' : ((u + 1) ^ 2) ^ 2 ≤ (v + 2) ^ 2 := by
    calc ((u + 1) ^ 2) ^ 2 = (u + 1) ^ 4 := by ring
      _ ≤ (v + 2) ^ 2 := h1
  have h3 : (u + 1) ^ 2 ≤ v + 2 := (Nat.pow_le_pow_iff_left (by norm_num)).1 h1'
  have h3' : u * (u + 2) + 1 ≤ v + 2 := by
    have e : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    rw [e] at h3
    exact h3
  have h4 : u * (u + 2) ≤ v + 1 := by omega
  have h5 : (u * (u + 2)) ^ 3 ≤ (v + 1) ^ 3 := Nat.pow_le_pow_left h4 3
  have h6a : (u + 2) ^ 3 ≤ (u * (u + 2)) ^ 3 :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (by omega)) 3
  have h6b : (u + 2) ^ 2 < (u + 2) ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  exact lt_irrefl _ (lt_of_lt_of_le (h6b.trans_le h6a) (h5.trans h2))

theorem fin_b {u v : ℕ} (hu : 3 ≤ u) (h1 : (u + 1) ^ 4 ≤ (v + 2) ^ 4)
    (h2 : (v + 1) ^ 3 ≤ (u + 2) ^ 2) : False := by
  have h3 : u + 1 ≤ v + 2 := (Nat.pow_le_pow_iff_left (by norm_num)).1 h1
  have h4 : u ^ 3 ≤ (v + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h5 : (u + 2) ^ 2 < u ^ 3 := by
    obtain ⟨w, rfl⟩ : ∃ w, u = w + 3 := ⟨u - 3, by omega⟩
    have e : (w + 3) ^ 3 = w ^ 3 + 9 * w ^ 2 + 27 * w + 27 := by ring
    have e' : (w + 3 + 2) ^ 2 = w ^ 2 + 10 * w + 25 := by ring
    rw [e, e']
    nlinarith [sq_nonneg w, pow_nonneg (Nat.zero_le w) 3]
  exact lt_irrefl _ (lt_of_lt_of_le h5 (h4.trans h2))

theorem fin_d {u v : ℕ} (hu : 2 ≤ u) (h1 : (u + 1) ^ 6 ≤ (v + 2) ^ 4)
    (h2 : (v + 1) ^ 3 ≤ (u + 2) ^ 3) : False := by
  have h1' : ((u + 1) ^ 3) ^ 2 ≤ ((v + 2) ^ 2) ^ 2 := by
    calc ((u + 1) ^ 3) ^ 2 = (u + 1) ^ 6 := by ring
      _ ≤ (v + 2) ^ 4 := h1
      _ = ((v + 2) ^ 2) ^ 2 := by ring
  have h3 : (u + 1) ^ 3 ≤ (v + 2) ^ 2 := (Nat.pow_le_pow_iff_left (by norm_num)).1 h1'
  have h4 : v + 1 ≤ u + 2 := (Nat.pow_le_pow_iff_left (by norm_num)).1 h2
  have h5 : (v + 2) ^ 2 ≤ (u + 3) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  obtain ⟨w, rfl⟩ : ∃ w, u = w + 2 := ⟨u - 2, by omega⟩
  have h6 : (w + 5) ^ 2 < (w + 3) ^ 3 := by
    have e : (w + 3) ^ 3 = w ^ 3 + 9 * w ^ 2 + 27 * w + 27 := by ring
    have e' : (w + 5) ^ 2 = w ^ 2 + 10 * w + 25 := by ring
    rw [e, e']
    nlinarith [sq_nonneg w, pow_nonneg (Nat.zero_le w) 3]
  have e1 : (w + 2 + 1) ^ 3 = (w + 3) ^ 3 := by ring
  have e2 : (w + 2 + 3) ^ 2 = (w + 5) ^ 2 := by ring
  rw [e1] at h3
  rw [e2] at h5
  exact lt_irrefl _ (lt_of_lt_of_le h6 (le_trans h3 h5))

theorem fin_e {u v : ℕ} (hu : 4 ≤ u) (h1 : (u + 1) ^ 6 ≤ (v + 2) ^ 2)
    (h2 : (v + 1) ^ 3 ≤ (u + 2) ^ 5) : False := by
  have h1' : ((u + 1) ^ 3) ^ 2 ≤ (v + 2) ^ 2 := by
    calc ((u + 1) ^ 3) ^ 2 = (u + 1) ^ 6 := by ring
      _ ≤ (v + 2) ^ 2 := h1
  have h3 : (u + 1) ^ 3 ≤ 2 * (v + 1) := by
    have := (Nat.pow_le_pow_iff_left (by norm_num)).1 h1'
    linarith
  have h4 : ((u + 1) ^ 3) ^ 3 ≤ (2 * (v + 1)) ^ 3 := Nat.pow_le_pow_left h3 3
  have h5 : (2 * (v + 1)) ^ 3 = 8 * (v + 1) ^ 3 := by ring
  have h6 : ((u + 1) ^ 3) ^ 3 ≤ 8 * (u + 2) ^ 5 := by
    rw [h5] at h4
    exact h4.trans (Nat.mul_le_mul_left 8 h2)
  have hA : 8 * (u + 2) ^ 5 ≤ 256 * (u + 1) ^ 5 := by
    have h := Nat.pow_le_pow_left (show u + 2 ≤ 2 * (u + 1) by omega) 5
    have h' : (2 * (u + 1)) ^ 5 = 32 * (u + 1) ^ 5 := by ring
    rw [h'] at h
    linarith
  have h10 : 625 ≤ (u + 1) ^ 4 := by
    have := Nat.pow_le_pow_left (show 5 ≤ u + 1 by omega) 4
    simpa using this
  have hB : 625 * (u + 1) ^ 5 ≤ ((u + 1) ^ 3) ^ 3 := by
    have e : ((u + 1) ^ 3) ^ 3 = (u + 1) ^ 4 * (u + 1) ^ 5 := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ h10
  have hC : 0 < (u + 1) ^ 5 := by positivity
  linarith

theorem cop_all {p s e1 e2 d1 d2 : ℕ} (hp : p.Prime) (hs : s.Prime) (hps : p ≠ s)
    (hd1 : ¬ p ∣ d1) (hd2 : ¬ s ∣ d2) :
    Nat.Coprime (p ^ e1) (s ^ e2) ∧ Nat.Coprime (p ^ e1) d1 ∧ Nat.Coprime (s ^ e2) d2 :=
  ⟨Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hs).2 hps),
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hd1),
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hs).2 hd2)⟩

theorem gen_div {p s e1 e2 M R1 R2 d1 d2 : ℕ} (E1 : M * d1 = p ^ e1 * R1)
    (E2 : M * d2 = s ^ e2 * R2) (c12 : Nat.Coprime (p ^ e1) (s ^ e2))
    (c1 : Nat.Coprime (p ^ e1) d1) (c2 : Nat.Coprime (s ^ e2) d2) :
    p ^ e1 ∣ R2 ∧ s ^ e2 ∣ R1 := by
  have star : p ^ e1 * R1 * d2 = s ^ e2 * R2 * d1 := by rw [← E1, ← E2]; ring
  constructor
  · have h1 : p ^ e1 ∣ s ^ e2 * (R2 * d1) := by
      rw [← mul_assoc, ← star]; exact ⟨R1 * d2, by ring⟩
    exact c1.dvd_of_dvd_mul_right (c12.dvd_of_dvd_mul_left h1)
  · have h1 : s ^ e2 ∣ p ^ e1 * (R1 * d2) := by
      rw [← mul_assoc, star]; exact ⟨R2 * d1, by ring⟩
    exact c2.dvd_of_dvd_mul_right (c12.symm.dvd_of_dvd_mul_left h1)

theorem nd_L {p v d : ℕ} (hp : p.Prime) (hpx : p ∣ v + 1) (hd : d ∣ v) : ¬ p ∣ d :=
  fun h => contra_one hp ((Nat.dvd_add_right (h.trans hd)).1 hpx)

theorem nd_U {p v d : ℕ} (hp : p.Prime) (hpx : p ∣ v + 1) (hd : d ∣ v + 2) : ¬ p ∣ d := fun h => by
  have h1 := Nat.dvd_sub (h.trans hd) hpx
  rw [show v + 2 - (v + 1) = 1 by omega] at h1
  exact contra_one hp h1

end CFSG.LocalAnalysis.GLTheoremA.YS05NonIso
