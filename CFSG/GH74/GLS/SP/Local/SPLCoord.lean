module

public import CFSG.GH74.GLS.SP.Local.SPLCoordDef
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

public section

namespace CFSG.GH74.GLS.SP.Local

section ZeroNeg

variable {A : Type*} [AddGroup A] {P : Type*} [Group P]

private theorem map_zero_of_add {f : A → P} (hf : ∀ s s', f (s + s') = f s * f s') : f 0 = 1 := by
  simpa using hf 0 0

private theorem map_neg_of_add {f : A → P} (hf : ∀ s s', f (s + s') = f s * f s') (s : A) :
    f (-s) = (f s)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← hf, neg_add_cancel, map_zero_of_add hf]

end ZeroNeg

section Basic

variable {F : Type*} [Field F] {P : Type*} [Group P] {x₁ x₂ x₃ x₄ : F → P}

theorem SPLCoord.zero₁ (h : SPLCoord x₁ x₂ x₃ x₄) : x₁ 0 = 1 := map_zero_of_add h.add₁

theorem SPLCoord.zero₂ (h : SPLCoord x₁ x₂ x₃ x₄) : x₂ 0 = 1 := map_zero_of_add h.add₂

theorem SPLCoord.zero₃ (h : SPLCoord x₁ x₂ x₃ x₄) : x₃ 0 = 1 := map_zero_of_add h.add₃

theorem SPLCoord.zero₄ (h : SPLCoord x₁ x₂ x₃ x₄) : x₄ 0 = 1 := map_zero_of_add h.add₄

theorem SPLCoord.neg₁ (h : SPLCoord x₁ x₂ x₃ x₄) (s : F) : x₁ (-s) = (x₁ s)⁻¹ :=
  map_neg_of_add h.add₁ s

theorem SPLCoord.neg₂ (h : SPLCoord x₁ x₂ x₃ x₄) (c : F) : x₂ (-c) = (x₂ c)⁻¹ :=
  map_neg_of_add h.add₂ c

theorem SPLCoord.x₄_mul_x₃ (h : SPLCoord x₁ x₂ x₃ x₄) (a b : F) :
    x₄ b * x₃ a = x₃ a * x₄ b * x₂ (-(a * b)) := by
  rw [h.neg₂, h.c34 a b]
  group

theorem SPLCoord.x₄_mul_x₁ (h : SPLCoord x₁ x₂ x₃ x₄) (s b : F) :
    x₄ b * x₁ s = x₁ s * x₄ b * x₃ (-(s * b)) * x₂ (-(s * b ^ 2 / 2)) := by
  have e := h.c14 (-s) b
  rw [h.neg₁, show -s * b = -(s * b) by ring, show -s * b ^ 2 / 2 = -(s * b ^ 2 / 2) by ring] at e
  calc x₄ b * x₁ s = x₁ s * ((x₁ s)⁻¹ * x₄ b) * x₁ s := by group
    _ = x₁ s * (x₄ b * x₃ (-(s * b)) * x₂ (-(s * b ^ 2 / 2)) * (x₁ s)⁻¹) * x₁ s := by rw [e]
    _ = x₁ s * x₄ b * x₃ (-(s * b)) * x₂ (-(s * b ^ 2 / 2)) := by group

section Rules

variable (h : SPLCoord x₁ x₂ x₃ x₄)
include h

private theorem SPLCoord.swap₂₁ (c s : F) (g : P) : x₂ c * (x₁ s * g) = x₁ s * (x₂ c * g) := by
  rw [← mul_assoc, h.cen₂ c (x₁ s), mul_assoc]

private theorem SPLCoord.swap₃₁ (a s : F) (g : P) : x₃ a * (x₁ s * g) = x₁ s * (x₃ a * g) := by
  rw [← mul_assoc, ← h.c13 s a, mul_assoc]

private theorem SPLCoord.swap₃₂ (a c : F) (g : P) : x₃ a * (x₂ c * g) = x₂ c * (x₃ a * g) := by
  rw [← mul_assoc, ← h.cen₂ c (x₃ a), mul_assoc]

private theorem SPLCoord.swap₄₂ (b c : F) (g : P) : x₄ b * (x₂ c * g) = x₂ c * (x₄ b * g) := by
  rw [← mul_assoc, ← h.cen₂ c (x₄ b), mul_assoc]

private theorem SPLCoord.swap₄₃ (b a : F) (g : P) :
    x₄ b * (x₃ a * g) = x₃ a * (x₄ b * (x₂ (-(a * b)) * g)) := by
  rw [← mul_assoc, h.x₄_mul_x₃, mul_assoc, mul_assoc]

private theorem SPLCoord.swap₄₁ (b s : F) (g : P) : x₄ b * (x₁ s * g) =
    x₁ s * (x₄ b * (x₃ (-(s * b)) * (x₂ (-(s * b ^ 2 / 2)) * g))) := by
  rw [← mul_assoc, h.x₄_mul_x₁]
  simp only [mul_assoc]

private theorem SPLCoord.merge₁ (s s' : F) (g : P) : x₁ s * (x₁ s' * g) = x₁ (s + s') * g := by
  rw [h.add₁, mul_assoc]

private theorem SPLCoord.merge₂ (c c' : F) (g : P) : x₂ c * (x₂ c' * g) = x₂ (c + c') * g := by
  rw [h.add₂, mul_assoc]

private theorem SPLCoord.merge₃ (a a' : F) (g : P) : x₃ a * (x₃ a' * g) = x₃ (a + a') * g := by
  rw [h.add₃, mul_assoc]

private theorem SPLCoord.merge₄ (b b' : F) (g : P) : x₄ b * (x₄ b' * g) = x₄ (b + b') * g := by
  rw [h.add₄, mul_assoc]

end Rules

theorem SPLCoord.two_mul_inv_two (h : SPLCoord x₁ x₂ x₃ x₄) : (2 : F) * 2⁻¹ = 1 := by
  have key : x₄ (1 + 1) * (x₁ 1 * 1) = x₄ 1 * (x₄ 1 * (x₁ 1 * 1)) := by
    rw [h.add₄, mul_assoc]
  simp only [h.swap₃₂, h.swap₄₂, h.swap₄₃, h.swap₄₁, h.merge₂, h.merge₃, h.merge₄] at key
  simp only [mul_one, ← mul_assoc] at key
  obtain ⟨-, hC, -, -⟩ := h.inj _ _ _ _ _ _ _ _ key
  linear_combination (-1 : F) * hC

end Basic

theorem SPLCoord.mul_law {F : Type*} [Field F] {P : Type*} [Group P] {x₁ x₂ x₃ x₄ : F → P}
    (h : SPLCoord x₁ x₂ x₃ x₄) (s c a b s' c' a' b' : F) :
    (x₁ s * x₂ c * x₃ a * x₄ b) * (x₁ s' * x₂ c' * x₃ a' * x₄ b') =
      x₁ (s + s') * x₂ (c + c' + s' * b ^ 2 / 2 - a' * b) * x₃ (a + a' - s' * b) * x₄ (b + b') := by
  have h2 := h.two_mul_inv_two
  simp only [mul_assoc, h.swap₂₁, h.swap₃₁, h.swap₃₂, h.swap₄₂, h.swap₄₃, h.swap₄₁, h.merge₁, h.merge₂,
    h.merge₃, ← h.add₄]
  congr 4
  · linear_combination (-(s' * b ^ 2)) * h2
  · ring

section Iso

private theorem exists_mulEquiv_of_coord {T P P' : Type*} [Group P] [Group P'] (m : T → T → T)
    (E : T → P) (E' : T → P') (hE : Function.Bijective E) (hE' : Function.Bijective E')
    (hm : ∀ t t', E t * E t' = E (m t t')) (hm' : ∀ t t', E' t * E' t' = E' (m t t')) :
    ∃ φ : P ≃* P', ∀ t, φ (E t) = E' t := by
  obtain ⟨e, he⟩ : ∃ e : T ≃ P, ∀ t, e t = E t := ⟨Equiv.ofBijective E hE, fun _ => rfl⟩
  obtain ⟨e', he'⟩ : ∃ e' : T ≃ P', ∀ t, e' t = E' t := ⟨Equiv.ofBijective E' hE', fun _ => rfl⟩
  have hs : ∀ t, e.symm (E t) = t := fun t => by rw [← he, Equiv.symm_apply_apply]
  refine ⟨MulEquiv.mk' (e.symm.trans e') ?_, fun t => ?_⟩
  · intro g g'
    obtain ⟨t, rfl⟩ := hE.2 g
    obtain ⟨t', rfl⟩ := hE.2 g'
    simp only [Equiv.trans_apply, hm, hs, he', hm']
  · change e' (e.symm (E t)) = E' t
    rw [hs, he']

variable {F : Type*} [Field F] {P : Type*} [Group P] {x₁ x₂ x₃ x₄ : F → P}

private theorem SPLCoord.bijective_coord (h : SPLCoord x₁ x₂ x₃ x₄) :
    Function.Bijective (fun t : F × F × F × F => x₁ t.1 * x₂ t.2.1 * x₃ t.2.2.1 * x₄ t.2.2.2) := by
  refine ⟨?_, fun g => ?_⟩
  · rintro ⟨s, c, a, b⟩ ⟨s', c', a', b'⟩ ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h.inj s c a b s' c' a' b' ht
    rfl
  · obtain ⟨s, c, a, b, rfl⟩ := h.surj g
    exact ⟨(s, c, a, b), rfl⟩

end Iso

theorem SPLCoord.exists_mulEquiv {F : Type*} [Field F] {P P' : Type*} [Group P] [Group P']
    {x₁ x₂ x₃ x₄ : F → P} {x₁' x₂' x₃' x₄' : F → P'}
    (h : SPLCoord x₁ x₂ x₃ x₄) (h' : SPLCoord x₁' x₂' x₃' x₄') :
    ∃ φ : P ≃* P', ∀ s, φ (x₁ s) = x₁' s ∧ φ (x₂ s) = x₂' s ∧ φ (x₃ s) = x₃' s ∧ φ (x₄ s) = x₄' s := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_coord
    (fun t t' : F × F × F × F => (t.1 + t'.1,
      t.2.1 + t'.2.1 + t'.1 * t.2.2.2 ^ 2 / 2 - t'.2.2.1 * t.2.2.2,
      t.2.2.1 + t'.2.2.1 - t'.1 * t.2.2.2, t.2.2.2 + t'.2.2.2))
    (fun t => x₁ t.1 * x₂ t.2.1 * x₃ t.2.2.1 * x₄ t.2.2.2)
    (fun t => x₁' t.1 * x₂' t.2.1 * x₃' t.2.2.1 * x₄' t.2.2.2)
    h.bijective_coord h'.bijective_coord
    (fun t t' => h.mul_law _ _ _ _ _ _ _ _) (fun t t' => h'.mul_law _ _ _ _ _ _ _ _)
  refine ⟨φ, fun s => ⟨?_, ?_, ?_, ?_⟩⟩
  · simpa [h.zero₂, h.zero₃, h.zero₄, h'.zero₂, h'.zero₃, h'.zero₄] using hφ (s, 0, 0, 0)
  · simpa [h.zero₁, h.zero₃, h.zero₄, h'.zero₁, h'.zero₃, h'.zero₄] using hφ (0, s, 0, 0)
  · simpa [h.zero₁, h.zero₂, h.zero₄, h'.zero₁, h'.zero₂, h'.zero₄] using hφ (0, 0, s, 0)
  · simpa [h.zero₁, h.zero₂, h.zero₃, h'.zero₁, h'.zero₂, h'.zero₃] using hφ (0, 0, 0, s)

end CFSG.GH74.GLS.SP.Local
