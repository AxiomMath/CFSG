module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEng
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvL4Cell

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups commutatorElement

theorem l4_core_generic {F : Type} [Field F] [Finite F] {p₀ f₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀2 : p₀ ≠ 2) (hcard : Nat.card F = p₀ ^ f₀) {α : MulAut (projectiveSL 4 F)} {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup (projectiveSL 4 F)} (hXp : IsPGroup p ↥X)
    (hX1 : X ≠ ⊥) (hN : fixSub α ≤ normalizer (X : Set (projectiveSL 4 F)))
    (Good : projectiveSL 4 F → Prop) (hGood : (∀ y ∈ X, Good y) → False)
    (irred : ∀ W : Submodule F (Fin 4 → F),
      (∀ A : SL(4, F), proj 4 F A ∈ fixSub α → ∀ w ∈ W,
        (A : Matrix (Fin 4) (Fin 4) F) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤)
    (cent : 5 ≤ Nat.card F → ∀ x : SL(4, F),
      (∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) → ∀ g, x * ι g = ι g * x) →
      Good (proj 4 F x))
    (cent3 : Nat.card F = 3 → ∀ x : SL(4, F), (∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1) →
      (∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
        x * ⁅a, b⁆ = ⁅a, b⁆ * x) → Good (proj 4 F x)) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp₀.odd_of_ne_two hp₀2).pow
  by_cases hpq : p ∣ Nat.card F
  · have hpp₀ : p = p₀ := by
      rw [hcard] at hpq
      exact (Nat.prime_dvd_prime_iff_eq hp hp₀).1 (hp.dvd_of_dvd_pow hpq)
    have hchar : CharP F p := by
      have := Fintype.ofFinite F
      exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard, hpp₀])
    obtain ⟨W, hW0, hWt, hW⟩ := exists_proper_invariant_subspace_projectiveSL hXp hX1 hN
    rcases irred W hW with h | h
    · exact hW0 h
    · exact hWt h
  · obtain ⟨X₀, hX₀p, hmap, hnormX₀⟩ := l4_exists_lift hp2 hXp
    apply hGood
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨n, hn⟩ := hX₀p ⟨x, hx⟩
    have hxn : x ^ (p ^ n) = 1 := by simpa using congrArg Subtype.val hn
    by_cases h3 : Nat.card F = 3
    · have hp3 : p ≠ 3 := fun h => hpq (by rw [h3, h])
      have : IsCyclic ↥X₀ := l4_cyclic_three h3 hp2 hp3 hX₀p
      refine cent3 h3 x ⟨p, n, hp, five_le_of_ne hp2 hp3, hxn⟩ ?_
      intro a b ha hb
      exact commutator_centralizes_of_cyclic (hnormX₀ a (hN ha)) (hnormX₀ b (hN hb)) x hx
    · have h5 : 5 ≤ Nat.card F := by
        obtain ⟨m, hm⟩ := hqodd
        have : 1 < Nat.card F := Finite.one_lt_card
        omega
      refine cent h5 x ?_
      intro ι hι g
      exact (l4_sl2_engine hqodd h5 hp2 hpq hX₀p ι (fun g => hnormX₀ _ (hN (hι g))) g x hx).symm

theorem l4_false_of_fixed {F : Type} [Field F] {α : MulAut (projectiveSL 4 F)}
    {X : Subgroup (projectiveSL 4 F)} (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : projectiveSL 4 F => x * (α x)⁻¹) '' (X : Set _)) = X)
    (hfix : ∀ y ∈ X, α y = y) : False := by
  apply hX1
  rw [← hcomm, eq_bot_iff, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_bot]
  rw [hfix y hy, mul_inv_cancel]

theorem l4_class1_core (h : L4Cls1) {F : Type} [Field F] [Finite F] {p₀ f₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀2 : p₀ ≠ 2) (hcard : Nat.card F = p₀ ^ f₀) {α : MulAut (projectiveSL 4 F)}
    {B : GL (Fin 4) F} (hBB : B * B = 1)
    (hdim : Module.finrank F (LinearMap.ker (toLin' B.val - 1)) = 2) (hα : α = conjAut 4 F B)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X : Subgroup (projectiveSL 4 F)} (hXp : IsPGroup p ↥X)
    (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : projectiveSL 4 F => x * (α x)⁻¹) '' (X : Set _)) = X)
    (hN : fixSub α ≤ normalizer (X : Set (projectiveSL 4 F))) : False := by
  obtain ⟨hirr, hcent, hcent3⟩ := h F
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp₀.odd_of_ne_two hp₀2).pow
  exact l4_core_generic hp₀ hp₀2 hcard hp2 hXp hX1 hN (fun y => α y = y)
    (l4_false_of_fixed hX1 hcomm) (hirr hqodd hBB hdim hα)
    (fun h5 => hcent hqodd h5 hBB hdim hα) (fun h3 => hcent3 h3 hBB hdim hα)

theorem l4_class2_core (h : L4Cls2) {F : Type} [Field F] [Finite F] {p₀ f₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀2 : p₀ ≠ 2) (hcard : Nat.card F = p₀ ^ f₀) {α : MulAut (projectiveSL 4 F)}
    {A : GL (Fin 4) F} {c : Fˣ} (hAA : A * A = GeneralLinearGroup.scalar (Fin 4) c)
    (hc : ¬ IsSquare (c : F)) (hα : α = conjAut 4 F A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (projectiveSL 4 F)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hcomm : Subgroup.closure ((fun x : projectiveSL 4 F => x * (α x)⁻¹) '' (X : Set _)) = X)
    (hN : fixSub α ≤ normalizer (X : Set (projectiveSL 4 F))) : False := by
  obtain ⟨hirr, hcent, hcent3⟩ := h F
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp₀.odd_of_ne_two hp₀2).pow
  exact l4_core_generic hp₀ hp₀2 hcard hp2 hXp hX1 hN (fun y => α y = y)
    (l4_false_of_fixed hX1 hcomm) (hirr hqodd hAA hc hα)
    (fun h5 => hcent hqodd h5 hAA hc hα) (fun h3 => hcent3 h3 hAA hc hα)

theorem l4_class3_core (h : L4Cls3) {F : Type} [Field F] [Finite F] {p₀ f₀ : ℕ} (hp₀ : p₀.Prime)
    (hp₀2 : p₀ ≠ 2) (hcard : Nat.card F = p₀ ^ f₀) {α : MulAut (projectiveSL 4 F)}
    {A : GL (Fin 4) F} (hAt : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = A)
    (hα : α = conjAut 4 F A * dualAut 4 F) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {X : Subgroup (projectiveSL 4 F)} (hXp : IsPGroup p ↥X) (hX1 : X ≠ ⊥)
    (hN : fixSub α ≤ normalizer (X : Set (projectiveSL 4 F))) : False := by
  obtain ⟨hirr, hcent, hcent3⟩ := h F
  have hqodd : Odd (Nat.card F) := by
    rw [hcard]
    exact (hp₀.odd_of_ne_two hp₀2).pow
  refine l4_core_generic hp₀ hp₀2 hcard hp2 hXp hX1 hN (fun y => y = 1) ?_
    (hirr hqodd hAt hα) (fun h5 x hx => proj_eq_one_iff.2 (hcent hqodd h5 hAt hα x hx))
    (fun h3 x hx hc => proj_eq_one_iff.2 (hcent3 h3 hAt hα x hx hc))
  intro hall
  exact hX1 (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hall y hy))

theorem l4SurvCore_of_classes (h1 : L4Cls1) (h2 : L4Cls2) (h3 : L4Cls3) : L4SurvCore := by
  intro F _ _ p₀ f₀ hp₀ hp₀2 _ hcard _ α _ hS p _ hp2 X hXp hX1 hcomm hN
  rcases hS with ⟨B, hBB, hdim, hα⟩ | ⟨A, c, hAA, hc, hα⟩ | ⟨A, hα, hAt⟩
  · exact l4_class1_core h1 hp₀ hp₀2 hcard hBB hdim hα hp2 hXp hX1 hcomm hN
  · exact l4_class2_core h2 hp₀ hp₀2 hcard hAA hc hα hp2 hXp hX1 hcomm hN
  · exact l4_class3_core h3 hp₀ hp₀2 hcard hAt hα hp2 hXp hX1 hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
