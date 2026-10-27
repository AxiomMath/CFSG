module
public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Rank
public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Order.CompletePartialOrder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped ComplexConjugate

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

def classFun (G : Type*) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ x y : G, IsConj x y → f x = f y}
  add_mem' {f g} hf hg := fun x y h => by simp [hf x y h, hg x y h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' c f hf := fun x y h => by simp [hf x y h]

@[simp]
theorem mem_classFun {f : G → ℂ} :
    f ∈ classFun G ↔ ∀ x y : G, IsConj x y → f x = f y := Iff.rfl

theorem classFun.apply_eq_of_isConj {f : G → ℂ} (hf : f ∈ classFun G) {x y : G}
    (h : IsConj x y) : f x = f y := hf x y h

theorem classFun.apply_conj {f : G → ℂ} (hf : f ∈ classFun G) (x c : G) :
    f (c * x * c⁻¹) = f x :=
  hf _ _ (isConj_iff.2 ⟨c⁻¹, by group⟩)

theorem character_mem_classFun (V : FDRep ℂ G) : FDRep.character V ∈ classFun G := by
  intro x y h
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (V.char_conj x c).symm

def Irr (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Representation.IsIrreducible V.ρ ∧ FDRep.character V = χ}

theorem mem_Irr {χ : G → ℂ} :
    χ ∈ Irr G ↔ ∃ V : FDRep ℂ G, Representation.IsIrreducible V.ρ ∧ FDRep.character V = χ :=
  Iff.rfl

theorem character_mem_Irr (V : FDRep ℂ G) (h : Representation.IsIrreducible V.ρ) :
    FDRep.character V ∈ Irr G := ⟨V, h, rfl⟩

theorem Irr_subset_classFun : Irr G ⊆ classFun G := by
  rintro χ ⟨V, -, rfl⟩
  exact character_mem_classFun V

section Inner

variable {α : Type*} [Fintype α]

noncomputable def cfInner (f h : α → ℂ) : ℂ :=
  (Nat.card α : ℂ)⁻¹ * ∑ g : α, f g * conj (h g)

theorem cfInner_def (f h : α → ℂ) :
    cfInner f h = (Nat.card α : ℂ)⁻¹ * ∑ g : α, f g * conj (h g) := (rfl)

theorem conj_cfInner (f h : α → ℂ) : conj (cfInner f h) = cfInner h f := by
  simp only [cfInner_def, map_mul, map_sum, Complex.conj_conj, map_inv₀, Complex.conj_natCast,
    mul_comm]

theorem cfInner_add_left (f₁ f₂ h : α → ℂ) :
    cfInner (f₁ + f₂) h = cfInner f₁ h + cfInner f₂ h := by
  simp only [cfInner_def, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem cfInner_smul_left (c : ℂ) (f h : α → ℂ) :
    cfInner (c • f) h = c * cfInner f h := by
  simp only [cfInner_def, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

theorem cfInner_zero_left (h : α → ℂ) : cfInner 0 h = 0 := by
  simp [cfInner_def]

theorem cfInner_self_eq_sum_norm_sq (f : α → ℂ) :
    cfInner f f = (Nat.card α : ℂ)⁻¹ * ∑ g : α, (‖f g‖ : ℂ) ^ 2 := by
  simp [cfInner_def, Complex.mul_conj']

theorem cfInner_eq_zero_of_disjoint_support {f h : α → ℂ}
    (hd : Disjoint (Function.support f) (Function.support h)) : cfInner f h = 0 := by
  rw [cfInner_def, Finset.sum_eq_zero, mul_zero]
  intro g _
  by_cases hg : f g = 0
  · simp [hg]
  · have : h g = 0 := by
      by_contra hh
      exact Set.disjoint_left.mp hd hg hh
    simp [this]

end Inner

theorem card_setOf_isConj_mul_card_centralizer (a : G) :
    Nat.card {g : G | IsConj g a} * Nat.card (Subgroup.centralizer ({a} : Set G)) = Nat.card G := by
  have hsub : {g : G | IsConj g a} = MulAction.orbit (ConjAct G) a := by
    ext g; simp [ConjAct.mem_orbit_conjAct]
  rw [hsub, Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer, mul_comm, Subgroup.card_mul_index]
  exact Nat.card_congr ConjAct.ofConjAct.toEquiv

variable [Fintype G]

theorem cfInner_self_eq_sum_over_reps {A : Set G} {f : G → ℂ} (hf : f ∈ classFun G)
    (hf0 : ∀ g ∉ A, f g = 0) (R : Finset G)
    (hRpw : ∀ a ∈ R, ∀ b ∈ R, IsConj a b → a = b)
    (hRcov : ∀ g ∈ A, ∃ a ∈ R, IsConj g a) :
    cfInner f f = ∑ a ∈ R,
      (‖f a‖ : ℂ) ^ 2 / (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) := by
  classical
  set F : G → ℂ := fun g => (‖f g‖ : ℂ) ^ 2 with hF
  set t : G → Finset G := fun a => {g | IsConj g a} with ht
  have hmem : ∀ a g : G, g ∈ t a ↔ IsConj g a := by intro a g; simp [ht]
  have hdisj : (R : Set G).PairwiseDisjoint t := by
    intro a ha b hb hab
    simp only [Finset.disjoint_left]
    intro g hga hgb
    exact hab (hRpw a ha b hb (((hmem a g).1 hga).symm.trans ((hmem b g).1 hgb)))
  have hsum : ∑ g : G, F g = ∑ a ∈ R, ∑ g ∈ t a, F g := by
    rw [← Finset.sum_biUnion hdisj]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro g _ hg
    have hgA : g ∉ A := fun hgA => by
      obtain ⟨a, haR, hga⟩ := hRcov g hgA
      exact hg (Finset.mem_biUnion.2 ⟨a, haR, (hmem a g).2 hga⟩)
    simp [hF, hf0 g hgA]
  have hclass : ∀ a : G, ∑ g ∈ t a, F g = (Nat.card {g : G | IsConj g a} : ℂ) * F a := by
    intro a
    rw [Finset.sum_congr rfl (fun g hg => ?_), Finset.sum_const, nsmul_eq_mul]
    · congr 1
      simp [ht, Nat.card_eq_fintype_card, Fintype.card_subtype]
    · show F g = F a
      simp only [hF, hf g a ((hmem a g).1 hg)]
  rw [cfInner_def]
  have hcast : ∀ g : G, f g * conj (f g) = F g := fun g => by simp [hF, Complex.mul_conj']
  simp only [hcast]
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hclass a]
  have hcne : (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hGne : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hcC : (Nat.card {g : G | IsConj g a} : ℂ) *
      (Nat.card (Subgroup.centralizer ({a} : Set G)) : ℂ) = (Nat.card G : ℂ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (card_setOf_isConj_mul_card_centralizer a)
  field_simp
  linear_combination F a * hcC

end CFSG.FeitThompson
