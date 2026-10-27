module

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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.ONan

open MulAction

theorem even_ncard_orbit {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]
    (C A : Ω) (hAC : A ≠ C) (hA : A ∈ orbit G C) (R' : Set G)
    (hR'C : ∀ ρ ∈ R', ρ • C = C) (hR'A : ∀ ρ ∈ R', ρ • A = A)
    (hnorm : ∀ g : G, g • C = C → ∀ ρ ∈ R', g * ρ * g⁻¹ ∈ R')
    (hfix : ∀ D ∈ orbit G C, (∀ ρ ∈ R', ρ • D = D) → D = C ∨ D = A) :
    Even (orbit G C).ncard := by
  classical
  obtain ⟨h₀, hh₀⟩ := hA
  have hh₀' : h₀ • C = A := hh₀
  have hN : ∀ g : G, g • C = C → g • A = A := by
    intro g hg
    have hD : g • A ∈ orbit G C := ⟨g * h₀, by show (g * h₀) • C = g • A; rw [mul_smul, hh₀']⟩
    have hfixed : ∀ ρ ∈ R', ρ • (g • A) = g • A := by
      intro ρ hρ
      have h1 : g⁻¹ * ρ * g⁻¹⁻¹ ∈ R' := hnorm g⁻¹ (by rw [inv_smul_eq_iff, hg]) ρ hρ
      rw [inv_inv] at h1
      calc ρ • (g • A) = (ρ * g) • A := (mul_smul _ _ _).symm
        _ = (g * (g⁻¹ * ρ * g)) • A := by group
        _ = g • ((g⁻¹ * ρ * g) • A) := mul_smul _ _ _
        _ = g • A := by rw [hR'A _ h1]
    rcases hfix _ hD hfixed with h' | h'
    · exact absurd (MulAction.injective g (h'.trans hg.symm)) hAC
    · exact h'
  have hst : stabilizer G A = stabilizer G C := by
    have hle : stabilizer G C ≤ stabilizer G A := fun g hg => by
      rw [mem_stabilizer_iff] at hg ⊢
      exact hN g hg
    have hcard : Nat.card (stabilizer G A) = Nat.card (stabilizer G C) := by
      rw [← hh₀', stabilizer_smul_eq_stabilizer_map_conj]
      exact Subgroup.card_map_of_injective (MulAut.conj h₀).injective
    exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  have hAorb : A ∈ orbit G C := ⟨h₀, hh₀⟩
  have hWC : {E | E ∈ orbit G C ∧ stabilizer G E = stabilizer G C} = {C, A} := by
    ext E
    constructor
    · rintro ⟨hE, hEst⟩
      apply hfix E hE
      intro ρ hρ
      have : ρ ∈ stabilizer G E := by
        rw [hEst, mem_stabilizer_iff]
        exact hR'C ρ hρ
      exact mem_stabilizer_iff.mp this
    · rintro (rfl | rfl)
      · exact ⟨mem_orbit_self _, rfl⟩
      · exact ⟨hAorb, hst⟩
  have hW : ∀ h : G, {E | E ∈ orbit G C ∧ stabilizer G E = stabilizer G (h • C)} =
      (fun E => h • E) '' {E | E ∈ orbit G C ∧ stabilizer G E = stabilizer G C} := by
    intro h
    ext E
    constructor
    · rintro ⟨hE, hEst⟩
      refine ⟨h⁻¹ • E, ⟨?_, ?_⟩, by simp⟩
      · obtain ⟨k, hk⟩ := hE
        have hk' : k • C = E := hk
        exact ⟨h⁻¹ * k, by show (h⁻¹ * k) • C = h⁻¹ • E; rw [mul_smul, hk']⟩
      · have e1 := stabilizer_smul_eq_stabilizer_map_conj h⁻¹ E
        have e2 := stabilizer_smul_eq_stabilizer_map_conj h⁻¹ (h • C)
        rw [inv_smul_smul] at e2
        rw [e1, hEst, ← e2]
    · rintro ⟨E', ⟨hE', hE'st⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := hE'
        have hk' : k • C = E' := hk
        exact ⟨h * k, by show (h * k) • C = h • E'; rw [mul_smul, hk']⟩
      · rw [stabilizer_smul_eq_stabilizer_map_conj, stabilizer_smul_eq_stabilizer_map_conj, hE'st]
  have hcard2 : ∀ D ∈ orbit G C,
      {E | E ∈ orbit G C ∧ stabilizer G E = stabilizer G D}.ncard = 2 := by
    rintro D ⟨h, hD⟩
    have hD' : h • C = D := hD
    rw [← hD', hW h, Set.ncard_image_of_injective _ (MulAction.injective h), hWC,
      Set.ncard_pair hAC.symm]
  have hfin : (orbit G C).Finite := Set.finite_range _
  let T := hfin.toFinset
  have hsum := Finset.card_eq_sum_card_image (fun D => stabilizer G D) T
  have h2 : ∀ b ∈ T.image (fun D => stabilizer G D),
      (T.filter (fun D => stabilizer G D = b)).card = 2 := by
    intro b hb
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hb
    have := hcard2 D (hfin.mem_toFinset.mp hD)
    rw [← this, ← Set.ncard_coe_finset]
    congr 1
    ext E
    simp [T]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul] at hsum
  have h3 : (orbit G C).ncard = T.card := Set.ncard_eq_toFinset_card _ hfin
  exact ⟨(T.image (fun D => stabilizer G D)).card, by omega⟩

end CFSG.QuasithinUnique.ONan
