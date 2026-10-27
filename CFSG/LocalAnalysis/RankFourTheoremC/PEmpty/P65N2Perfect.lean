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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup

theorem trivial_of_perfect {A : Type} [Group A] [Finite A] {p : ℕ} (hp : p.Prime)
    {X D N : Subgroup A}
    (hperf : ∀ (M : Subgroup ↥X) [M.Normal], IsPGroup p (↥X ⧸ M) → M = ⊤)
    (hDX : D ≤ X) (hDn : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hD : ¬ p ∣ Nat.card D)
    (hNX : N ≤ X) (hXDN : ∀ x ∈ X, ∃ d ∈ D, ∃ n ∈ N, x = d * n)
    {Q : Type} [CommGroup Q] [Finite Q] (χ : ↥N →* Q) :
    ∀ (a : A) (ha : a ∈ N) (k : ℕ), a ^ (p ^ k) = 1 → χ ⟨a, ha⟩ = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, m, hm, hQ⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := Q)).ne' p
    hp.ne_one
  let K₀ : Subgroup ↥N := ((powMonoidHom m : Q →* Q).comp χ).ker
  have hK₀ : ∀ n : ↥N, n ^ (p ^ e) ∈ K₀ := by
    intro n
    show (χ (n ^ (p ^ e))) ^ m = 1
    rw [map_pow, ← pow_mul, ← hQ]
    exact pow_card_eq_one'
  have hNconj : ∀ n : ↥N, ∀ d ∈ D, (n : A) * d * (n : A)⁻¹ ∈ D := fun n d hd => hDn n (hNX n.2) d hd
  let M₁A : Subgroup A :=
    { carrier := {y | ∃ d ∈ D, ∃ n : ↥N, n ∈ K₀ ∧ y = d * (n : A)}
      mul_mem' := by
        rintro _ _ ⟨d₁, hd₁, n₁, hn₁, rfl⟩ ⟨d₂, hd₂, n₂, hn₂, rfl⟩
        refine ⟨d₁ * ((n₁ : A) * d₂ * (n₁ : A)⁻¹), D.mul_mem hd₁ (hNconj n₁ d₂ hd₂), n₁ * n₂,
          K₀.mul_mem hn₁ hn₂, ?_⟩
        simp only [Subgroup.coe_mul]
        group
      one_mem' := ⟨1, D.one_mem, 1, K₀.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨d, hd, n, hn, rfl⟩
        refine ⟨(n⁻¹ : ↥N) * d⁻¹ * ((n⁻¹ : ↥N) : A)⁻¹, ?_, n⁻¹, K₀.inv_mem hn, ?_⟩
        · simpa using hNconj n⁻¹ d⁻¹ (D.inv_mem hd)
        · simp only [Subgroup.coe_inv]
          group }
  have hM₁X : M₁A ≤ X := by
    rintro _ ⟨d, hd, n, -, rfl⟩
    exact X.mul_mem (hDX hd) (hNX n.2)
  have hDM : ∀ d ∈ D, d ∈ M₁A := fun d hd => ⟨d, hd, 1, K₀.one_mem, by simp⟩
  have hKM : ∀ n : ↥N, n ∈ K₀ → (n : A) ∈ M₁A := fun n hn => ⟨1, D.one_mem, n, hn, by simp⟩
  let M : Subgroup ↥X := M₁A.subgroupOf X
  haveI hMn : M.Normal := by
    refine ⟨fun y hy g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    obtain ⟨d, hd, n, hn, hyd⟩ := hy
    obtain ⟨d₀, hd₀, n₀, hn₀, hg⟩ := hXDN (g : A) g.2
    have hn₀X : (n₀ : A) ∈ X := hNX hn₀
    have hK₀n : (⟨n₀, hn₀⟩ : ↥N) * n * (⟨n₀, hn₀⟩ : ↥N)⁻¹ ∈ K₀ := by
      show ((powMonoidHom m : Q →* Q).comp χ) _ = 1
      simp only [map_mul, map_inv, MonoidHom.comp_apply]
      have hn' : ((powMonoidHom m : Q →* Q).comp χ) n = 1 := hn
      simp only [MonoidHom.comp_apply] at hn'
      rw [hn', mul_one, mul_inv_cancel]
    set n' : ↥N := (⟨n₀, hn₀⟩ : ↥N) * n * (⟨n₀, hn₀⟩ : ↥N)⁻¹ with hn'
    set d' : A := n₀ * d * n₀⁻¹ with hd'
    have hd'D : d' ∈ D := hDn n₀ hn₀X d hd
    have hn'X : (n' : A) ∈ X := hNX n'.2
    have hd'' : d₀ * d' * ((n' : A) * d₀⁻¹ * (n' : A)⁻¹) ∈ D :=
      D.mul_mem (D.mul_mem hd₀ hd'D) (hDn n' hn'X d₀⁻¹ (D.inv_mem hd₀))
    refine ⟨_, hd'', n', hK₀n, ?_⟩
    have e1 : (g : A) = d₀ * n₀ := hg
    have e2 : (↑(g * y * g⁻¹) : A) = (g : A) * (y : A) * (g : A)⁻¹ := by simp
    rw [e2, e1]
    have e3 : (y : A) = d * (n : A) := hyd
    rw [e3]
    simp only [hn', hd', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hMp : IsPGroup p (↥X ⧸ M) := by
    intro q
    induction q using QuotientGroup.induction_on with | _ g => ?_
    obtain ⟨d₀, hd₀, n₀, hn₀, hg⟩ := hXDN (g : A) g.2
    refine ⟨e, ?_⟩
    have hd₀M : (⟨d₀, hDX hd₀⟩ : ↥X) ∈ M := Subgroup.mem_subgroupOf.mpr (hDM d₀ hd₀)
    have hgd : g = (⟨d₀, hDX hd₀⟩ : ↥X) * (⟨n₀, hNX hn₀⟩ : ↥X) := Subtype.ext hg
    have hn₀p : (⟨n₀, hNX hn₀⟩ : ↥X) ^ (p ^ e) ∈ M := by
      rw [Subgroup.mem_subgroupOf]
      exact hKM ((⟨n₀, hn₀⟩ : ↥N) ^ (p ^ e)) (hK₀ _)
    have hmk : (QuotientGroup.mk g : ↥X ⧸ M) = QuotientGroup.mk (⟨n₀, hNX hn₀⟩ : ↥X) := by
      rw [hgd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hd₀M, one_mul]
    show (QuotientGroup.mk g : ↥X ⧸ M) ^ (p ^ e) = 1
    rw [hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hn₀p
  have hMtop : M = ⊤ := hperf M hMp
  intro a ha k hak
  have haM : (⟨a, hNX ha⟩ : ↥X) ∈ M := hMtop ▸ Subgroup.mem_top _
  obtain ⟨d, hd, n, hn, hand⟩ := Subgroup.mem_subgroupOf.mp haM
  have hand' : a = d * (n : A) := hand
  have hdN : d ∈ N := by
    have : d = a * (n : A)⁻¹ := by rw [hand']; group
    rw [this]
    exact N.mul_mem ha (N.inv_mem n.2)
  have hsplit : (⟨a, ha⟩ : ↥N) = ⟨d, hdN⟩ * n := Subtype.ext hand'
  set o := orderOf d with ho
  have hodvd : o ∣ Nat.card D := by
    have := orderOf_dvd_natCard (⟨d, hd⟩ : ↥D)
    rwa [Subgroup.orderOf_mk] at this
  have hpo : Nat.Coprime p o := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact fun h => hD (h.trans hodvd)
  have hχd : χ ⟨d, hdN⟩ ^ o = 1 := by
    rw [← map_pow]
    have : (⟨d, hdN⟩ : ↥N) ^ o = 1 :=
      Subtype.ext (by simp only [Subgroup.coe_pow, Subgroup.coe_one]; exact pow_orderOf_eq_one d)
    rw [this, map_one]
  have hχn : χ n ^ m = 1 := hn
  have hχa : χ ⟨a, ha⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨a, ha⟩ : ↥N) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hak)
    rw [this, map_one]
  have hχam : χ ⟨a, ha⟩ ^ (o * m) = 1 := by
    rw [hsplit, map_mul, mul_pow, pow_mul, hχd, one_pow, mul_comm o m, pow_mul, hχn, one_pow,
      one_mul]
  have hcop : Nat.Coprime (o * m) (p ^ k) := by
    have hpm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
    exact (Nat.Coprime.pow_left k (Nat.Coprime.mul_right hpo hpm)).symm
  have h1 : orderOf (χ ⟨a, ha⟩) ∣ Nat.gcd (o * m) (p ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hχam) (orderOf_dvd_of_pow_eq_one hχa)
  rw [hcop] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
