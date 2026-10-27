module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CauchySchwarzProjection

open ComplexConjugate
open scoped ComplexOrder

variable {G : Type*}

section ClassFun

variable [Group G]

def classFun (G : Type*) [Group G] : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ g x : G, f (x * g * x⁻¹) = f g}
  add_mem' {f₁ f₂} h₁ h₂ := fun g x => by
    simp only [Set.mem_ofPred_eq] at h₁ h₂
    simp only [Pi.add_apply, h₁ g x, h₂ g x]
  zero_mem' := fun _ _ => rfl
  smul_mem' c f hf := fun g x => by
    simp only [Set.mem_ofPred_eq] at hf
    simp only [Pi.smul_apply, hf g x]

@[simp] lemma mem_classFun {f : G → ℂ} :
    f ∈ classFun G ↔ ∀ g x : G, f (x * g * x⁻¹) = f g := Iff.rfl

def irr (G : Type*) [Group G] : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Representation.IsIrreducible V.ρ ∧ V.character = χ}

lemma mem_irr {χ : G → ℂ} :
    χ ∈ irr G ↔ ∃ V : FDRep ℂ G, Representation.IsIrreducible V.ρ ∧ V.character = χ := Iff.rfl

lemma character_mem_irr {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    {ρ : Representation ℂ G V} (hρ : Representation.IsIrreducible ρ) : ρ.character ∈ irr G := by
  refine ⟨FDRep.of ρ, by rwa [FDRep.of_ρ'], funext fun g => ?_⟩
  simp [FDRep.character, Representation.character, FDRep.of_ρ']

lemma irr_subset_classFun : irr G ⊆ classFun G := by
  rintro χ ⟨V, -, rfl⟩
  exact fun g x => V.char_conj g x

end ClassFun

section Inner

variable [Fintype G]

noncomputable def classFunInner (f h : G → ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g, f g * conj (h g)

lemma classFunInner_apply (f h : G → ℂ) :
    classFunInner f h = (Fintype.card G : ℂ)⁻¹ * ∑ g, f g * conj (h g) := (rfl)

lemma classFunInner_add_left (f₁ f₂ h : G → ℂ) :
    classFunInner (f₁ + f₂) h = classFunInner f₁ h + classFunInner f₂ h := by
  simp only [classFunInner_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma classFunInner_add_right (f h₁ h₂ : G → ℂ) :
    classFunInner f (h₁ + h₂) = classFunInner f h₁ + classFunInner f h₂ := by
  simp only [classFunInner_apply, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

lemma classFunInner_sub_left (f₁ f₂ h : G → ℂ) :
    classFunInner (f₁ - f₂) h = classFunInner f₁ h - classFunInner f₂ h := by
  simp only [classFunInner_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

lemma classFunInner_sub_right (f h₁ h₂ : G → ℂ) :
    classFunInner f (h₁ - h₂) = classFunInner f h₁ - classFunInner f h₂ := by
  simp only [classFunInner_apply, Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

lemma classFunInner_smul_left (c : ℂ) (f h : G → ℂ) :
    classFunInner (c • f) h = c * classFunInner f h := by
  simp only [classFunInner_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma classFunInner_smul_right (c : ℂ) (f h : G → ℂ) :
    classFunInner f (c • h) = conj c * classFunInner f h := by
  simp only [classFunInner_apply, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, ← mul_assoc]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma classFunInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (h : G → ℂ) :
    classFunInner (∑ i ∈ s, f i) h = ∑ i ∈ s, classFunInner (f i) h := by
  simp only [classFunInner_apply, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma classFunInner_sum_right {ι : Type*} (s : Finset ι) (f : G → ℂ) (h : ι → G → ℂ) :
    classFunInner f (∑ i ∈ s, h i) = ∑ i ∈ s, classFunInner f (h i) := by
  simp only [classFunInner_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

lemma classFunInner_conj_symm (f h : G → ℂ) : conj (classFunInner f h) = classFunInner h f := by
  simp only [classFunInner_apply, map_mul, map_sum, map_inv₀, Complex.conj_natCast,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  exact congrArg _ (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

lemma classFunInner_self_eq_ofReal (f : G → ℂ) :
    classFunInner f f = (((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ ^ 2 : ℝ) : ℂ) := by
  rw [classFunInner_apply]
  push_cast
  refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
  simpa using Complex.mul_conj' (f g)

lemma classFunInner_self_re (f : G → ℂ) :
    (classFunInner f f).re = (Fintype.card G : ℝ)⁻¹ * ∑ g, ‖f g‖ ^ 2 := by
  rw [classFunInner_self_eq_ofReal, Complex.ofReal_re]

lemma classFunInner_self_nonneg (f : G → ℂ) : 0 ≤ classFunInner f f := by
  rw [classFunInner_self_eq_ofReal, Complex.zero_le_real]
  positivity

lemma classFunInner_self_eq_zero {f : G → ℂ} : classFunInner f f = 0 ↔ f = 0 := by
  rw [classFunInner_self_eq_ofReal]
  simp only [Complex.ofReal_eq_zero, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero]
  constructor
  · rintro (h | h)
    · have he : IsEmpty G := Fintype.card_eq_zero_iff.1 h
      exact funext fun g => (he.false g).elim
    · funext g
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h g
        (Finset.mem_univ g)
      simpa using this
  · rintro rfl
    exact Or.inr (by simp)

lemma classFunInner_eq_inner (f h : G → ℂ) :
    classFunInner f h = (Fintype.card G : ℂ)⁻¹ *
      inner ℂ (WithLp.toLp 2 h : EuclideanSpace ℂ G) (WithLp.toLp 2 f) := by
  simp [classFunInner_apply, PiLp.inner_apply, RCLike.inner_apply]

private lemma norm_sq_toLp (f : G → ℂ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℂ G)‖ ^ 2 = ∑ g, ‖f g‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem norm_classFunInner_sq_le (f h : G → ℂ) :
    ((‖classFunInner f h‖ ^ 2 : ℝ) : ℂ) ≤ classFunInner f f * classFunInner h h := by
  rw [classFunInner_self_eq_ofReal, classFunInner_self_eq_ofReal, ← Complex.ofReal_mul,
    Complex.real_le_real, classFunInner_eq_inner, norm_mul, ← norm_sq_toLp f, ← norm_sq_toLp h]
  have hcc : ‖((Fintype.card G : ℂ)⁻¹)‖ = (Fintype.card G : ℝ)⁻¹ := by simp
  rw [hcc, mul_pow]
  calc ((Fintype.card G : ℝ)⁻¹) ^ 2 *
        ‖inner ℂ (WithLp.toLp 2 h : EuclideanSpace ℂ G) (WithLp.toLp 2 f)‖ ^ 2
      ≤ ((Fintype.card G : ℝ)⁻¹) ^ 2 *
        (‖(WithLp.toLp 2 h : EuclideanSpace ℂ G)‖ *
          ‖(WithLp.toLp 2 f : EuclideanSpace ℂ G)‖) ^ 2 := by
        gcongr
        exact norm_inner_le_norm _ _
    _ = _ := by ring

theorem norm_classFunInner_sq_le_re (f h : G → ℂ) :
    ‖classFunInner f h‖ ^ 2 ≤ (classFunInner f f).re * (classFunInner h h).re := by
  have H := norm_classFunInner_sq_le f h
  rw [classFunInner_self_eq_ofReal f, classFunInner_self_eq_ofReal h, ← Complex.ofReal_mul,
    Complex.real_le_real] at H
  rw [classFunInner_self_re, classFunInner_self_re]
  exact H

def IsOrthonormalIn (E : Finset (G → ℂ)) : Prop :=
  ∀ e ∈ E, ∀ e' ∈ E, classFunInner e e' = if e = e' then 1 else 0

noncomputable def classFunProj (E : Finset (G → ℂ)) (f : G → ℂ) : G → ℂ :=
  ∑ e ∈ E, classFunInner f e • e

lemma classFunProj_apply (E : Finset (G → ℂ)) (f : G → ℂ) :
    classFunProj E f = ∑ e ∈ E, classFunInner f e • e := (rfl)

variable {E : Finset (G → ℂ)}

lemma classFunProj_mem_span (E : Finset (G → ℂ)) (f : G → ℂ) :
    classFunProj E f ∈ Submodule.span ℂ (E : Set (G → ℂ)) :=
  Submodule.sum_mem _ fun _ he => Submodule.smul_mem _ _ (Submodule.subset_span he)

lemma classFunInner_classFunProj_right_of_forall {u f : G → ℂ}
    (hu : ∀ e ∈ E, classFunInner u e = 0) : classFunInner u (classFunProj E f) = 0 := by
  rw [classFunProj_apply, classFunInner_sum_right]
  exact Finset.sum_eq_zero fun e he => by rw [classFunInner_smul_right, hu e he, mul_zero]

lemma IsOrthonormalIn.classFunInner_classFunProj_left (hE : IsOrthonormalIn E) (f : G → ℂ)
    {e' : G → ℂ} (he' : e' ∈ E) :
    classFunInner (classFunProj E f) e' = classFunInner f e' := by
  rw [classFunProj_apply, classFunInner_sum_left, Finset.sum_eq_single_of_mem e' he']
  · rw [classFunInner_smul_left, hE e' he' e' he', if_pos rfl, mul_one]
  · intro e he hne
    rw [classFunInner_smul_left, hE e he e' he', if_neg hne, mul_zero]

lemma IsOrthonormalIn.classFunInner_sub_classFunProj (hE : IsOrthonormalIn E) (f : G → ℂ) :
    classFunInner (f - classFunProj E f) (classFunProj E f) = 0 :=
  classFunInner_classFunProj_right_of_forall fun e he => by
    rw [classFunInner_sub_left, hE.classFunInner_classFunProj_left f he, sub_self]

lemma IsOrthonormalIn.classFunProj_eq_self (hE : IsOrthonormalIn E) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℂ (E : Set (G → ℂ))) : classFunProj E f = f := by
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hf
  have key : ∀ e' ∈ E, classFunInner (∑ e ∈ E, c e • e) e' = c e' := by
    intro e' he'
    rw [classFunInner_sum_left, Finset.sum_eq_single_of_mem e' he']
    · rw [classFunInner_smul_left, hE e' he' e' he', if_pos rfl, mul_one]
    · intro e he hne
      rw [classFunInner_smul_left, hE e he e' he', if_neg hne, mul_zero]
  exact Finset.sum_congr rfl fun e he => by rw [key e he]

lemma IsOrthonormalIn.classFunInner_self_eq (hE : IsOrthonormalIn E) (f : G → ℂ) :
    classFunInner f f = classFunInner (classFunProj E f) (classFunProj E f)
      + classFunInner (f - classFunProj E f) (f - classFunProj E f) := by
  have h₁ : classFunInner (f - classFunProj E f) (classFunProj E f) = 0 :=
    hE.classFunInner_sub_classFunProj f
  have h₂ : classFunInner (classFunProj E f) (f - classFunProj E f) = 0 := by
    rw [← classFunInner_conj_symm, h₁, map_zero]
  have hsum : classFunProj E f + (f - classFunProj E f) = f := add_sub_cancel _ _
  calc classFunInner f f
      = classFunInner (classFunProj E f + (f - classFunProj E f))
          (classFunProj E f + (f - classFunProj E f)) := by rw [hsum]
    _ = _ := by
        rw [classFunInner_add_left, classFunInner_add_right, classFunInner_add_right, h₁, h₂]
        ring

theorem classFunInner_classFunProj_self_le (hE : IsOrthonormalIn E) (f : G → ℂ) :
    classFunInner (classFunProj E f) (classFunProj E f) ≤ classFunInner f f := by
  rw [hE.classFunInner_self_eq f]
  exact le_add_of_nonneg_right (classFunInner_self_nonneg _)

theorem classFunInner_classFunProj_self_eq_iff (hE : IsOrthonormalIn E) (f : G → ℂ) :
    classFunInner (classFunProj E f) (classFunProj E f) = classFunInner f f ↔
      f ∈ Submodule.span ℂ (E : Set (G → ℂ)) := by
  constructor
  · intro h
    rw [hE.classFunInner_self_eq f, left_eq_add, classFunInner_self_eq_zero, sub_eq_zero] at h
    exact h ▸ classFunProj_mem_span E f
  · intro hf
    rw [hE.classFunProj_eq_self hf]

end Inner

end CauchySchwarzProjection

end CFSG.FeitThompson
