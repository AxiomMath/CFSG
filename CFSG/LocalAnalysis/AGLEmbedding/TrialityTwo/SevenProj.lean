module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open Polynomial QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_eq_zero_of_eq {R : Type*} [Ring R] [Algebra K R] {t : R} (h7 : t ^ 7 = 1)
    (h2 : (2 : K) = 0) {p : K[X]} (q r : K[X]) (h : p = (X ^ 7 - 1) * q + 2 * r) :
    aeval t p = 0 := by
  have h2' : (2 : R) = 0 := by rw [← map_ofNat (algebraMap K R) 2, h2, map_zero]
  rw [h, map_add, map_mul, map_mul, map_sub, map_pow, aeval_X, h7, map_one, sub_self, zero_mul,
    map_ofNat, h2', zero_mul, add_zero]

@[expose] def projC (t : Module.End K V) : Module.End K V :=
  1 + t + t ^ 2 + t ^ 3 + t ^ 4 + t ^ 5 + t ^ 6

@[expose] def projU₁ (t : Module.End K V) : Module.End K V := 1 + t + t ^ 2 + t ^ 4

@[expose] def projU₂ (t : Module.End K V) : Module.End K V := 1 + t ^ 3 + t ^ 5 + t ^ 6

@[expose] def fixC (t : Module.End K V) : Submodule K V := LinearMap.ker (t - 1)

@[expose] def spU₁ (t : Module.End K V) : Submodule K V := LinearMap.range (projU₁ t)

@[expose] def spU₂ (t : Module.End K V) : Submodule K V := LinearMap.range (projU₂ t)

variable {t : Module.End K V}

theorem projC_eq : projC t = aeval t (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 : K[X]) := by
  simp [projC]

theorem projU₁_eq : projU₁ t = aeval t (1 + X + X ^ 2 + X ^ 4 : K[X]) := by
  simp [projU₁]

theorem projU₂_eq : projU₂ t = aeval t (1 + X ^ 3 + X ^ 5 + X ^ 6 : K[X]) := by
  simp [projU₂]

section Identities

variable (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
include h7 h2

theorem projC_add_projU₁_add_projU₂ : projC t + projU₁ t + projU₂ t = 1 := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) + (1 + X + X ^ 2 + X ^ 4) +
      (1 + X ^ 3 + X ^ 5 + X ^ 6) - 1) 0 (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)
    (by ring)
  rw [map_sub, map_add, map_add, ← projC_eq, ← projU₁_eq, ← projU₂_eq, map_one,
    sub_eq_zero] at h
  exact h

theorem projC_mul_projU₁ : projC t * projU₁ t = 0 := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * (1 + X + X ^ 2 + X ^ 4))
    (3 + 2 * X + X ^ 2 + X ^ 3)
    (2 + 2 * X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6) (by ring)
  rwa [map_mul, ← projC_eq, ← projU₁_eq] at h

theorem projC_mul_projU₂ : projC t * projU₂ t = 0 := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) * (1 + X ^ 3 + X ^ 5 + X ^ 6))
    (3 + 3 * X + 3 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5)
    (2 + 2 * X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6) (by ring)
  rwa [map_mul, ← projC_eq, ← projU₂_eq] at h

theorem projU₁_mul_projU₂ : projU₁ t * projU₂ t = 0 := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (1 + X + X ^ 2 + X ^ 4) * (1 + X ^ 3 + X ^ 5 + X ^ 6))
    (3 + X + X ^ 2 + X ^ 3) (2 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) (by ring)
  rwa [map_mul, ← projU₁_eq, ← projU₂_eq] at h

theorem projC_sub_one : projC t - 1 = (t + t ^ 3 + t ^ 5) * (t - 1) := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) - 1 - (X + X ^ 3 + X ^ 5) * (X - 1))
    0 (X + X ^ 3 + X ^ 5) (by ring)
  rw [map_sub, map_sub, ← projC_eq, map_one, map_mul, sub_eq_zero] at h
  simpa using h

theorem mul_projC : t * projC t = projC t := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := X * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) -
      (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) 1 0 (by ring)
  rw [map_sub, map_mul, ← projC_eq, aeval_X, sub_eq_zero] at h
  exact h

theorem pow_three_mul_projU₁ : t ^ 3 * projU₁ t = (t + 1) * projU₁ t := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := X ^ 3 * (1 + X + X ^ 2 + X ^ 4) - (X + 1) * (1 + X + X ^ 2 + X ^ 4)) 1 (-X - X ^ 2)
    (by ring)
  rw [map_sub, map_mul, map_mul, ← projU₁_eq, sub_eq_zero] at h
  simpa using h

theorem inv_mul_projU₁ : (t + 1) * (t ^ 2 + t) * projU₁ t = projU₁ t := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (X + 1) * (X ^ 2 + X) * (1 + X + X ^ 2 + X ^ 4) - (1 + X + X ^ 2 + X ^ 4)) 1
    (X ^ 2 + 2 * X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6) (by ring)
  rw [map_sub, map_mul, map_mul, ← projU₁_eq, sub_eq_zero] at h
  simpa using h

theorem inv_mul_projU₂ : (t + 1) * t ^ 2 * projU₂ t = projU₂ t := by
  have h := aeval_eq_zero_of_eq h7 h2
    (p := (X + 1) * X ^ 2 * (1 + X ^ 3 + X ^ 5 + X ^ 6) - (1 + X ^ 3 + X ^ 5 + X ^ 6))
    (1 + 2 * X + X ^ 2) (X + X ^ 2) (by ring)
  rw [map_sub, map_mul, map_mul, ← projU₂_eq, sub_eq_zero] at h
  simpa using h

end Identities

theorem commute_aeval (p : K[X]) : t * aeval t p = aeval t p * t := by
  have h := ((Commute.all (X : K[X]) p).map (aeval t)).eq
  rwa [aeval_X] at h

theorem commute_projU₁ : t * projU₁ t = projU₁ t * t := by
  rw [projU₁_eq]; exact commute_aeval _

theorem commute_projU₂ : t * projU₂ t = projU₂ t * t := by
  rw [projU₂_eq]; exact commute_aeval _

theorem aeval_mul_comm (p q : K[X]) : aeval t p * aeval t q = aeval t q * aeval t p := by
  rw [← map_mul, mul_comm, map_mul]

theorem pow_two_apply (x : V) : (t ^ 2) x = t (t x) := by
  rw [pow_two, Module.End.mul_apply]

theorem pow_three_apply (x : V) : (t ^ 3) x = t (t (t x)) := by
  rw [pow_succ, Module.End.mul_apply, pow_two_apply]

theorem mem_fixC_iff {x : V} : x ∈ fixC t ↔ t x = x := by
  rw [fixC, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

theorem apply_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) : t x ∈ spU₁ t := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨t y, (LinearMap.congr_fun commute_projU₁ y).symm⟩

theorem apply_mem_spU₂ {x : V} (hx : x ∈ spU₂ t) : t x ∈ spU₂ t := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨t y, (LinearMap.congr_fun commute_projU₂ y).symm⟩

theorem projU₁_apply_mem (x : V) : projU₁ t x ∈ spU₁ t := ⟨x, rfl⟩

theorem projU₂_apply_mem (x : V) : projU₂ t x ∈ spU₂ t := ⟨x, rfl⟩

section Vectors

variable (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0)
include h7 h2

theorem projU₁_mul_projC : projU₁ t * projC t = 0 := by
  rw [projU₁_eq, projC_eq, aeval_mul_comm, ← projU₁_eq, ← projC_eq, projC_mul_projU₁ h7 h2]

theorem projU₂_mul_projC : projU₂ t * projC t = 0 := by
  rw [projU₂_eq, projC_eq, aeval_mul_comm, ← projU₂_eq, ← projC_eq, projC_mul_projU₂ h7 h2]

theorem projU₂_mul_projU₁ : projU₂ t * projU₁ t = 0 := by
  rw [projU₂_eq, projU₁_eq, aeval_mul_comm, ← projU₂_eq, ← projU₁_eq, projU₁_mul_projU₂ h7 h2]

theorem projU₁_mul_self : projU₁ t * projU₁ t = projU₁ t := by
  have h := congrArg (projU₁ t * ·) (projC_add_projU₁_add_projU₂ h7 h2)
  simp only [mul_add, mul_one, projU₁_mul_projC h7 h2, projU₁_mul_projU₂ h7 h2, add_zero,
    zero_add] at h
  exact h

theorem projU₂_mul_self : projU₂ t * projU₂ t = projU₂ t := by
  have h := congrArg (projU₂ t * ·) (projC_add_projU₁_add_projU₂ h7 h2)
  simp only [mul_add, mul_one, projU₂_mul_projC h7 h2, projU₂_mul_projU₁ h7 h2, zero_add] at h
  exact h

theorem projC_add_projU₁_add_projU₂_apply (x : V) :
    projC t x + projU₁ t x + projU₂ t x = x := by
  have h := LinearMap.congr_fun (projC_add_projU₁_add_projU₂ h7 h2) x
  rwa [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply] at h

theorem mem_spU₁_iff {x : V} : x ∈ spU₁ t ↔ projU₁ t x = x :=
  ⟨by rintro ⟨y, rfl⟩; exact LinearMap.congr_fun (projU₁_mul_self h7 h2) y, fun h => ⟨x, h⟩⟩

theorem mem_spU₂_iff {x : V} : x ∈ spU₂ t ↔ projU₂ t x = x :=
  ⟨by rintro ⟨y, rfl⟩; exact LinearMap.congr_fun (projU₂_mul_self h7 h2) y, fun h => ⟨x, h⟩⟩

theorem projC_apply_mem_fixC (x : V) : projC t x ∈ fixC t :=
  (mem_fixC_iff).2 (LinearMap.congr_fun (mul_projC h7 h2) x)

theorem projC_apply_of_mem_fixC {x : V} (hx : x ∈ fixC t) : projC t x = x := by
  have h := LinearMap.congr_fun (projC_sub_one h7 h2) x
  rw [LinearMap.sub_apply, Module.End.one_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, (mem_fixC_iff).1 hx, sub_self, map_zero, sub_eq_zero] at h
  exact h

theorem projC_apply_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) : projC t x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun (projC_mul_projU₁ h7 h2) y

theorem projC_apply_of_mem_spU₂ {x : V} (hx : x ∈ spU₂ t) : projC t x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun (projC_mul_projU₂ h7 h2) y

theorem projU₂_apply_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) : projU₂ t x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun (projU₂_mul_projU₁ h7 h2) y

theorem projU₁_apply_of_mem_spU₂ {x : V} (hx : x ∈ spU₂ t) : projU₁ t x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun (projU₁_mul_projU₂ h7 h2) y

theorem projU₂_apply_of_mem_fixC {x : V} (hx : x ∈ fixC t) : projU₂ t x = 0 := by
  rw [← projC_apply_of_mem_fixC h7 h2 hx]
  exact LinearMap.congr_fun (projU₂_mul_projC h7 h2) x

theorem eq_zero_of_mem_spU₁_of_mem_fixC {x : V} (h₁ : x ∈ spU₁ t) (hC : x ∈ fixC t) : x = 0 := by
  rw [← projC_apply_of_mem_fixC h7 h2 hC, projC_apply_of_mem_spU₁ h7 h2 h₁]

theorem eq_zero_of_mem_spU₂_of_mem_fixC {x : V} (h₂ : x ∈ spU₂ t) (hC : x ∈ fixC t) : x = 0 := by
  rw [← projC_apply_of_mem_fixC h7 h2 hC, projC_apply_of_mem_spU₂ h7 h2 h₂]

theorem apply_apply_apply_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) : t (t (t x)) = t x + x := by
  obtain ⟨y, rfl⟩ := hx
  have h := LinearMap.congr_fun (pow_three_mul_projU₁ h7 h2) y
  rwa [Module.End.mul_apply, Module.End.mul_apply, pow_three_apply, LinearMap.add_apply,
    Module.End.one_apply] at h

theorem eq_apply_add_of_mem_spU₁ {x : V} (hx : x ∈ spU₁ t) :
    t (t (t x) + t x) + (t (t x) + t x) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h := LinearMap.congr_fun (inv_mul_projU₁ h7 h2) y
  rwa [Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.add_apply,
    pow_two_apply, Module.End.one_apply] at h

theorem eq_apply_add_of_mem_spU₂ {x : V} (hx : x ∈ spU₂ t) : t (t (t x)) + t (t x) = x := by
  obtain ⟨y, rfl⟩ := hx
  have h := LinearMap.congr_fun (inv_mul_projU₂ h7 h2) y
  rwa [Module.End.mul_apply, Module.End.mul_apply, LinearMap.add_apply, pow_two_apply,
    Module.End.one_apply] at h

end Vectors

end CFSG.AGLEmbedding.TrialityTwo.Seven
