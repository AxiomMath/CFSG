module

public import CFSG.Certificates.NativeValidSchreier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

variable {n : ℕ}

@[expose] def conjA (n : ℕ) (k u : Array ℕ) : Array ℕ := compA n (compA n k u) (invCand n k)

theorem rep_conjA {k u : Array ℕ} {g h : Equiv.Perm (Fin n)} (hk : Rep n k g)
    (hki : Rep n (invCand n k) g⁻¹) (hu : Rep n u h) : Rep n (conjA n k u) (g * h * g⁻¹) :=
  rep_compA (rep_compA hk hu) hki

@[expose] def commutesA (n : ℕ) (t u : Array ℕ) : Bool := eqA n (compA n t u) (compA n u t)

theorem commutesA_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin n)} (hg : Rep n t g)
    (hh : Rep n u h) : commutesA n t u = true ↔ g * h = h * g :=
  eqA_iff (rep_compA hg hh) (rep_compA hh hg)

theorem getElem!_rawInvs_eq {m : ℕ} {S : Array (Array ℕ)} {j : ℕ} (hj : j < S.size) :
    (rawInvs m S)[j]! = invCand m S[j]! := by
  rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S j hj]

theorem rep_inv_of_chainOK {S : Array (Array ℕ)} {k : ℕ} {base : List (Fin n)}
    {W : Array (List ℤ)} {chunks : ℕ}
    (h : rawChainOK n (S.extract 0 k) S (base.map Fin.val).toArray W chunks = true) {j : ℕ}
    (hj : j < S.size) : Rep n (invCand n S[j]!) (permOfArr n S[j]!)⁻¹ := by
  have h' := (chainCheckFacts h).strong_inv j hj
  rw [getElem!_rawInvs_eq hj] at h'
  exact (rep_permOfArr h').2

theorem exists_rep_wordA {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin n)} {j : ℕ}
    {H : Subgroup (Equiv.Perm (Fin n))} (hS : ∀ h < j, Rep n S[h]! (gs h))
    (hSinv : ∀ h < j, Rep n Sinv[h]! (gs h)⁻¹) (hH : ∀ h < j, gs h ∈ H) :
    ∀ w : List ℤ, lettersOK j w = true → ∃ g ∈ H, Rep n (wordA n S Sinv w) g
  | [], _ => ⟨1, H.one_mem, by simpa [wordA] using rep_idA (n := n)⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨g', hg', hrep'⟩ := exists_rep_wordA hS hSinv hH w hw'
    have hlet := rep_letterA hS hSinv ⟨hl0, hlj⟩
    refine ⟨_, H.mul_mem ?_ hg', by rw [wordA]; exact rep_compA hlet hrep'⟩
    by_cases hpos : 0 < l
    · rw [ite_eq_left (decide_eq_true hpos)]
      exact hH _ (by omega)
    · rw [ite_eq_right (by simpa using hpos)]
      exact H.inv_mem (hH _ (by omega))

end CFSG.ClassicalInvolution
