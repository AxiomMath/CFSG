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
public import Mathlib.GroupTheory.Commutator.Finite
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

namespace CFSG.GH74.AS16.E2

open Subgroup

structure TwoSzTable (K : Type) [Group K] (Q : Subgroup K) : Prop where
  exists_A : ∃ A : Subgroup K, A ≤ Q ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    (∀ a ∈ A, a * a = 1) ∧ Nat.card A = 16 ∧ center K ≤ A ∧
    (∀ x ∈ Q, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ center K) ∧
    (∀ s ∈ Q, s * s ∈ center K → s ∈ A) ∧
    (∀ b ∈ A, b ∉ center K → ∃ x ∈ Q, x * b * x⁻¹ ≠ b)

theorem card_comap_surj {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (B : Subgroup H) :
    Nat.card (B.comap f) = Nat.card B * Nat.card f.ker := by
  let g : B.comap f →* H := f.comp (B.comap f).subtype
  have hrange : g.range = B := by
    ext y
    simp only [MonoidHom.mem_range, g, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨k, rfl⟩ := hf y
      exact ⟨⟨k, hy⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card f.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, x.2⟩, fun x => ⟨⟨x.1, ?_⟩, x.2⟩, fun x => rfl,
      fun x => rfl⟩
    rw [Subgroup.mem_comap, x.2]
    exact B.one_mem
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hrange, hker] at h
  exact h

theorem twoSzTable_of_data {K : Type} [Group K] [Finite K] (Q : Subgroup K)
    (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) (hZc : Nat.card (center K) = 2)
    (hbender : ∀ T' : Subgroup (K ⧸ center K), IsPGroup 2 T' → ¬ 2 ∣ T'.index →
      (∀ x ∈ T', x ^ 2 = 1 → ∀ y ∈ T', y * x = x * y) ∧
        Nat.card ↥(T' ⊓ centralizer (T' : Set (K ⧸ center K))) = 8)
    (hgm : ∀ T : Sylow 2 K,
      (∀ b ∈ (T : Subgroup K), ∀ c ∈ (T : Subgroup K),
        (∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ center K) →
        (∀ x ∈ (T : Subgroup K), c * x * c⁻¹ * x⁻¹ ∈ center K) →
        b * c = c * b ∧ b ^ 2 = 1) ∧
      ∀ b ∈ (T : Subgroup K), (∀ x ∈ (T : Subgroup K), b * x * b⁻¹ * x⁻¹ ∈ center K) →
        b ∉ center K → ∀ z ∈ center K, ∃ x ∈ (T : Subgroup K), x * b * x⁻¹ * b⁻¹ = z) :
    TwoSzTable K Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup K := center K with hZdef
  have hZp : IsPGroup 2 ↥Z := IsPGroup.of_card (n := 1) (by rw [hZc]; norm_num)
  have hZQ : Z ≤ Q := hZp.le_sylow_of_normal (hQ.toSylow hQi)
  let π : K →* K ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hmemZ : ∀ a : K, a ∈ Z ↔ π a = 1 := fun a => by
    rw [← MonoidHom.mem_ker, hker]
  let TS : Sylow 2 K := hQ.toSylow hQi
  let TS' : Sylow 2 (K ⧸ Z) := TS.mapSurjective hπ
  have hTS' : (TS' : Subgroup (K ⧸ Z)) = Q.map π := rfl
  have hπQ : ∀ x : K, π x ∈ (TS' : Subgroup (K ⧸ Z)) ↔ x ∈ Q := by
    intro x
    rw [hTS']
    constructor
    · rintro ⟨y, hy, hyx⟩
      have h1 : y⁻¹ * x ∈ Z := by
        rw [hmemZ, map_mul, map_inv, hyx, inv_mul_cancel]
      have h2 : y⁻¹ * x ∈ Q := hZQ h1
      have := Q.mul_mem hy h2
      simpa using this
    · intro hx
      exact ⟨x, hx, rfl⟩
  obtain ⟨hT1, hEcard⟩ := hbender (TS' : Subgroup (K ⧸ Z)) TS'.isPGroup' TS'.not_dvd_index
  set E : Subgroup (K ⧸ Z) := (TS' : Subgroup (K ⧸ Z)) ⊓
    Subgroup.centralizer ((TS' : Subgroup (K ⧸ Z)) : Set (K ⧸ Z)) with hEdef
  set A : Subgroup K := E.comap π with hAdef
  have hmemA : ∀ a : K, a ∈ A ↔ π a ∈ E := fun a => Iff.rfl
  have hAQ : A ≤ Q := fun a ha => (hπQ a).1 (Subgroup.mem_inf.1 ((hmemA a).1 ha)).1
  have hcomm : ∀ x ∈ Q, ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ Z := by
    intro x hx a ha
    rw [hmemZ]
    have hπx : π x ∈ (TS' : Subgroup (K ⧸ Z)) := (hπQ x).2 hx
    have hc : π x * π a = π a * π x :=
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 ((hmemA a).1 ha)).2) (π x) hπx
    simp only [map_mul, map_inv]
    rw [hc]
    group
  have hcomm' : ∀ x ∈ Q, ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Z := by
    intro x hx a ha
    have h := Z.inv_mem (hcomm x hx a ha)
    have e : (x * a * x⁻¹ * a⁻¹)⁻¹ = a * x * a⁻¹ * x⁻¹ := by group
    rwa [e] at h
  obtain ⟨hAcomm, hA2⟩ : (∀ b ∈ A, ∀ c ∈ A, b * c = c * b) ∧ (∀ b ∈ A, b ^ 2 = 1) := by
    have key := (hgm TS).1
    refine ⟨fun b hb c hc => (key b (hAQ hb) c (hAQ hc) (fun x hx => hcomm' x hx b hb)
      (fun x hx => hcomm' x hx c hc)).1, fun b hb => (key b (hAQ hb) b (hAQ hb)
      (fun x hx => hcomm' x hx b hb) (fun x hx => hcomm' x hx b hb)).2⟩
  refine ⟨⟨A, hAQ, hAcomm, fun a ha => by rw [← pow_two]; exact hA2 a ha, ?_, ?_, hcomm, ?_, ?_⟩⟩
  · rw [hAdef, card_comap_surj π hπ E, hEcard, hker, hZc]
  · intro z hz
    rw [hmemA]
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 fun y _ => ?_⟩
    · rw [(hmemZ z).1 hz]; exact (TS' : Subgroup (K ⧸ Z)).one_mem
    · rw [(hmemZ z).1 hz]; simp
  · intro s hs hs2
    rw [hmemA]
    refine Subgroup.mem_inf.2 ⟨(hπQ s).2 hs, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hs2' : π s ^ 2 = 1 := by
      rw [← map_pow, pow_two]
      exact (hmemZ _).1 hs2
    exact hT1 (π s) ((hπQ s).2 hs) hs2' y hy
  · intro b hb hbZ
    have key := (hgm TS).2
    have : Nontrivial ↥Z := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    obtain ⟨z₀, hz₀⟩ := exists_ne (1 : ↥Z)
    have hz₀1 : (z₀ : K) ≠ 1 := fun h => hz₀ (Subtype.ext h)
    obtain ⟨x, hx, hxb⟩ := key b (hAQ hb) (fun x hx => hcomm' x hx b hb) hbZ z₀ z₀.2
    refine ⟨x, hx, fun h => hz₀1 ?_⟩
    rw [← hxb, h]
    group

end CFSG.GH74.AS16.E2
