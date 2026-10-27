module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvChar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEng
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Core

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix Module CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Generic

variable {p₀ f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p₀ f₀ K)

theorem u4_core_generic {α : MulAut (hypPSU h 2 0)} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (hypPSU h 2 0)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : fixSub α ≤ normalizer (X : Set (hypPSU h 2 0)))
    (Good : hypPSU h 2 0 → Prop) (hGood : (∀ y ∈ X, Good y) → False)
    (irred : ∀ W : Submodule K (HypIndex 2 0 → K),
      (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α → ∀ w ∈ W,
        ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (lifted : ¬ p ∣ p₀ ^ f₀ → ∀ X₀ : Subgroup ↥(hypSU h 2 0), IsPGroup p ↥X₀ →
      (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α →
        g ∈ normalizer (X₀ : Set ↥(hypSU h 2 0))) →
      ∀ x ∈ X₀, Good (hypProj h 2 0 x)) : False := by
  have hp : p.Prime := Fact.out
  by_cases hpq : p ∣ p₀ ^ f₀
  · have hpp₀ : p = p₀ :=
      (Nat.prime_dvd_prime_iff_eq hp h.prime).1 (hp.dvd_of_dvd_pow hpq)
    obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace_hypSU h hpp₀ hXp hX1 hN
    rcases irred W hW with hW' | hW'
    · exact hW0 hW'
    · exact hWt hW'
  · obtain ⟨X₀, hX₀p, hmap, hnormX₀⟩ := u4_exists_lift h hp2 hXp
    apply hGood
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact lifted hpq X₀ hX₀p (fun g hg => hnormX₀ g (hN hg)) x hx

theorem u4_false_of_fixed {Y : Type} [Group Y] {α : MulAut Y} {X : Subgroup Y} (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y)) = X)
    (hfix : ∀ y ∈ X, α y = y) : False := by
  apply hX1
  rw [← hcomm, eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_bot]
  rw [hfix y hy, mul_inv_cancel]

theorem u4_pow_eq_one_of_isPGroup {p : ℕ} {X₀ : Subgroup ↥(hypSU h 2 0)} (hX₀ : IsPGroup p ↥X₀)
    {x : ↥(hypSU h 2 0)} (hx : x ∈ X₀) : ∃ n : ℕ, x ^ (p ^ n) = 1 := by
  obtain ⟨n, hn⟩ := hX₀ ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

include h in
theorem u4_odd_of_ne_two (hp₀2 : p₀ ≠ 2) : Odd (p₀ ^ f₀) := (h.prime.odd_of_ne_two hp₀2).pow

include h in
theorem u4_three_le (hp₀2 : p₀ ≠ 2) : 3 ≤ p₀ ^ f₀ := by
  have h3 : 3 ≤ p₀ := by
    have := h.prime.two_le
    omega
  exact h3.trans (Nat.le_self_pow (by have := h.one_le; omega) p₀)

include h in
theorem u4_five_le (hp₀2 : p₀ ≠ 2) (h3 : ¬ p₀ ^ f₀ = 3) : 5 ≤ p₀ ^ f₀ := by
  obtain ⟨m, hm⟩ := u4_odd_of_ne_two h hp₀2
  have := u4_three_le h hp₀2
  omega

theorem u4_lifted_cls13 (hp₀2 : p₀ ≠ 2) {α : MulAut (hypPSU h 2 0)} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (Good : hypPSU h 2 0 → Prop)
    (hcent : 5 ≤ p₀ ^ f₀ → ∀ x : ↥(hypSU h 2 0),
      (∀ ι : SL(2, ↥h.fixedField) →* ↥(hypSU h 2 0), (∀ g, hypProj h 2 0 (ι g) ∈ fixSub α) →
        ∀ g, x * ι g = ι g * x) → Good (hypProj h 2 0 x))
    (hcent3 : p₀ ^ f₀ = 3 → ∀ x : ↥(hypSU h 2 0), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
      (∀ a b : ↥(hypSU h 2 0), hypProj h 2 0 a ∈ fixSub α → hypProj h 2 0 b ∈ fixSub α →
        x * ⁅a, b⁆ = ⁅a, b⁆ * x) → Good (hypProj h 2 0 x)) :
    ¬ p ∣ p₀ ^ f₀ → ∀ X₀ : Subgroup ↥(hypSU h 2 0), IsPGroup p ↥X₀ →
      (∀ g : ↥(hypSU h 2 0), hypProj h 2 0 g ∈ fixSub α →
        g ∈ normalizer (X₀ : Set ↥(hypSU h 2 0))) →
      ∀ x ∈ X₀, Good (hypProj h 2 0 x) := by
  intro hpq X₀ hX₀ hnorm x hx
  have hp : p.Prime := Fact.out
  have hqodd := u4_odd_of_ne_two h hp₀2
  by_cases h3 : p₀ ^ f₀ = 3
  · have hp3 : p ≠ 3 := fun hp3 => hpq (by rw [h3, hp3])
    have : IsCyclic ↥X₀ := u4_cyclic_three h h3 hp2 hp3 hX₀
    obtain ⟨n, hn⟩ := u4_pow_eq_one_of_isPGroup h hX₀ hx
    refine hcent3 h3 x ⟨p, n, hp, five_le_of_ne hp2 hp3, hn⟩ ?_
    intro a b ha hb
    exact commutator_centralizes_of_cyclic (hnorm a ha) (hnorm b hb) x hx
  · have h5 := u4_five_le h hp₀2 h3
    refine hcent h5 x ?_
    intro ι hι g
    exact (u4_sl2_engineQ h hqodd h5 hp2 hpq hX₀ ι (fun g => hnorm _ (hι g)) g x hx).symm

end Generic

section Classes

variable {p₀ f₀ : ℕ} {K : Type} [Field K]

theorem u4_class1_core (h1 : U4Cls1) [Finite K] (h : UnitaryFieldData p₀ f₀ K)
    (hp₀2 : p₀ ≠ 2) {α : MulAut (hypPSU h 2 0)} (hS : SurvU4Cls1 h α) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup (hypPSU h 2 0)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : hypPSU h 2 0 => x * (α x)⁻¹) '' (X : Set _)) = X)
    (hN : fixSub α ≤ normalizer (X : Set (hypPSU h 2 0))) : False := by
  obtain ⟨hirr, hcent, hcent3⟩ := h1 p₀ f₀ K h
  have hqodd := u4_odd_of_ne_two h hp₀2
  exact u4_core_generic h hp2 hXp hX1 hN (fun y => α y = y) (u4_false_of_fixed hX1 hcomm)
    (hirr hqodd α hS)
    (u4_lifted_cls13 h hp₀2 hp2 (fun y => α y = y) (fun h5 => hcent hqodd h5 α hS)
      (fun h3 => hcent3 h3 α hS))

theorem u4_class2_core (h2 : U4Cls2) [Finite K] (h : UnitaryFieldData p₀ f₀ K)
    (hp₀2 : p₀ ≠ 2) {α : MulAut (hypPSU h 2 0)} (hS : SurvU4Cls2 h α) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup (hypPSU h 2 0)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : hypPSU h 2 0 => x * (α x)⁻¹) '' (X : Set _)) = X)
    (hN : fixSub α ≤ normalizer (X : Set (hypPSU h 2 0))) : False := by
  obtain ⟨hirr, hcentK⟩ := h2 p₀ f₀ K h
  have hqodd := u4_odd_of_ne_two h hp₀2
  have h3 := u4_three_le h hp₀2
  refine u4_core_generic h hp2 hXp hX1 hN (fun y => α y = y) (u4_false_of_fixed hX1 hcomm)
    (hirr hqodd α hS) ?_
  intro hpq X₀ hX₀ hnorm x hx
  refine hcentK hqodd α hS x ?_
  intro ι hι g
  exact (u4_sl2_engineK h hqodd h3 hp2 hpq hX₀ ι (fun g => hnorm _ (hι g)) g x hx).symm

theorem u4_class3_core (h3 : U4Cls3) [Finite K] (h : UnitaryFieldData p₀ f₀ K)
    (hp₀2 : p₀ ≠ 2) {α : MulAut (hypPSU h 2 0)} (hS : SurvU4Cls3 h α) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup (hypPSU h 2 0)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : fixSub α ≤ normalizer (X : Set (hypPSU h 2 0))) : False := by
  obtain ⟨hirr, hcent, hcent3⟩ := h3 p₀ f₀ K h
  have hqodd := u4_odd_of_ne_two h hp₀2
  have hone : ∀ x : ↥(hypSU h 2 0), x ∈ hypScalars h 2 0 → hypProj h 2 0 x = 1 := fun x hx =>
    MonoidHom.mem_ker.1 (((SetLike.ext_iff.1 (ker_hypProj h 2 0)) x).2 hx)
  refine u4_core_generic h hp2 hXp hX1 hN (fun y => y = 1) ?_ (hirr hqodd α hS)
    (u4_lifted_cls13 h hp₀2 hp2 (fun y => y = 1)
      (fun h5 x hx => hone x (hcent hqodd h5 α hS x hx))
      (fun h3' x hx hc => hone x (hcent3 h3' α hS x hx hc)))
  intro hall
  exact hX1 (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hall y hy))

theorem u4SurvCore_of_classes (h1 : U4Cls1) (h2 : U4Cls2) (h3 : U4Cls3) : U4SurvCore := by
  intro p₀ f₀ K _ _ h _ hp₀2 _ α _ hS p _ hp2 X hXp hX1 hcomm hN
  rcases (survU4Orth_iff h α).1 hS with hS | hS | hS
  · exact u4_class1_core h1 h hp₀2 hS hp2 hXp hX1 hcomm hN
  · exact u4_class2_core h2 h hp₀2 hS hp2 hXp hX1 hcomm hN
  · exact u4_class3_core h3 h hp₀2 hS hp2 hXp hX1 hN

end Classes

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
