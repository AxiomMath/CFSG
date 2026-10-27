module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.LinearAlgebra

open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem zmod2_eq_zero_of_ne_one : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide

theorem zmod2_neg (z : ZMod 2) : -z = z := by
  revert z
  decide

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  rw [eq_neg_of_add_eq_zero_left h, zmod2_neg]

theorem zmod2_vec_add_self (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem zmod2_polar_self (q : QuadraticForm (ZMod 2) V) (x : V) : polar q x x = 0 := by
  rw [polar_self, two_smul, zmod2_add_self]

theorem polar_map_of_mem_orthogonalGroup {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ orthogonalGroup q) (x y : V) : polar q (g x) (g y) = polar q x y := by
  have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg
  simp only [polar, ← map_add]
  rw [hg' (x + y), hg' x, hg' y]

theorem rank_one_isometry_eq_transvection [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hnd : (polarBilin q).Nondegenerate)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ orthogonalGroup q)
    (hrk : finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1) :
    ∃ v : V, v ≠ 0 ∧ q v = 1 ∧ ∀ x, a x = x + polar q x v • v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v', hv'0, hspan⟩ := finrank_eq_one_iff'.1 hrk
  set v : V := (v' : V) with hvdef
  have hv0 : v ≠ 0 := fun h => hv'0 (Subtype.ext h)
  have hcoef : ∀ x, ∃ c : ZMod 2, a x = x + c • v := by
    intro x
    obtain ⟨c, hc⟩ := hspan ⟨(((a : V →ₗ[ZMod 2] V) - LinearMap.id : V →ₗ[ZMod 2] V) x),
      LinearMap.mem_range_self _ _⟩
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    simp only [SetLike.val_smul, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      at h1
    rw [← hvdef] at h1
    rw [h1]
    abel
  obtain ⟨y, hy⟩ : ∃ y, a y = y + v := by
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 v'.2
    refine ⟨y, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at hy
    rw [hvdef, ← hy]
    abel
  have hrel : ∀ x c, a x = x + c • v → polar q x v = c * polar q v y := by
    intro x c hx
    have h1 := polar_map_of_mem_orthogonalGroup ha x y
    rw [hx, hy, polar_add_left, polar_add_right, polar_add_right, polar_smul_left,
      polar_smul_left, zmod2_polar_self, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at h1
    have h2 : polar q x v + c * polar q v y = 0 := by
      rw [add_assoc] at h1
      exact add_eq_left.1 h1
    exact zmod2_eq_of_add_eq_zero h2
  have hvy : polar q v y = 1 := by
    by_contra hne
    have h0 : polar q v y = 0 := zmod2_eq_zero_of_ne_one _ hne
    apply hv0
    apply hnd.1 v
    intro x
    obtain ⟨c, hc⟩ := hcoef x
    rw [polarBilin_apply_apply, polar_comm, hrel x c hc, h0, mul_zero]
  have hform : ∀ x, a x = x + polar q x v • v := by
    intro x
    obtain ⟨c, hc⟩ := hcoef x
    rw [hc, hrel x c hc, hvy, mul_one]
  have hqv : q v = 1 := by
    have h1 : q (a y) = q y := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 ha y
    rw [hy, QuadraticMap.map_add (⇑q) y v] at h1
    have hyv : polar q y v = 1 := by
      have := hrel y 1 (by rw [hy, one_smul])
      rw [this, hvy, one_mul]
    rw [hyv] at h1
    have h2 : q v + 1 = 0 := by
      rw [add_assoc] at h1
      exact add_eq_left.1 h1
    exact zmod2_eq_of_add_eq_zero h2
  exact ⟨v, hv0, hqv, hform⟩

theorem transvection_comp_apply (q : QuadraticForm (ZMod 2) V) (v w y : V) :
    (y + polar q y w • w) + polar q (y + polar q y w • w) v • v =
      y + polar q y w • w + (polar q y v + polar q y w * polar q w v) • v := by
  rw [polar_add_left, polar_smul_left, smul_eq_mul]

theorem binary_reflection_normalizer_small_rank_obstruction [FiniteDimensional (ZMod 2) V]
    {q : QuadraticForm (ZMod 2) V} (hnd : (polarBilin q).Nondegenerate)
    {G : Subgroup (V ≃ₗ[ZMod 2] V)} (hG : G ≤ orthogonalGroup q)
    (hsmall : ∀ g ∈ G, (orderOf g = 2 ∨ orderOf g = 3) →
      3 ≤ finrank (ZMod 2) (LinearMap.range ((g : V →ₗ[ZMod 2] V) - LinearMap.id)))
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ orthogonalGroup q)
    (haN : a ∈ Subgroup.normalizer (G : Set (V ≃ₗ[ZMod 2] V)))
    (hrk : finrank (ZMod 2) (LinearMap.range ((a : V →ₗ[ZMod 2] V) - LinearMap.id)) = 1) :
    ∀ g ∈ G, a * g = g * a := by
  classical
  obtain ⟨v, -, -, ha'⟩ := rank_one_isometry_eq_transvection hnd ha hrk
  intro g hg
  have hgO := hG hg
  have hcG : a * g * a⁻¹ * g⁻¹ ∈ G :=
    mul_mem ((Subgroup.mem_normalizer_iff.1 haN g).1 hg) (inv_mem hg)
  have haa : ∀ x, a (a x) = x := by
    intro x
    rw [ha' (a x), ha' x, polar_add_left, polar_smul_left, zmod2_polar_self, smul_eq_mul,
      mul_zero, add_zero, add_assoc, zmod2_vec_add_self, add_zero]
  have hainv : ∀ x, a⁻¹ x = a x := by
    intro x
    change a.symm x = a x
    rw [LinearEquiv.symm_apply_eq, haa]
  set s := polar q (g v) v with hs
  have hc : ∀ x, (a * g * a⁻¹ * g⁻¹) x =
      x + polar q x (g v) • g v + (polar q x v + polar q x (g v) * s) • v := by
    intro x
    have h1 : polar q (g⁻¹ x) v = polar q x (g v) := by
      have := polar_map_of_mem_orthogonalGroup hgO (g⁻¹ x) v
      rw [← this]
      congr 1
      change g (g.symm x) = x
      exact g.apply_symm_apply x
    have h2 : g (g⁻¹ x) = x := g.apply_symm_apply x
    simp only [LinearEquiv.mul_apply]
    rw [hainv, ha' (g⁻¹ x), map_add, map_smul, h1, h2, ha', polar_add_left, polar_smul_left,
      smul_eq_mul]
  have hpv : ∀ x, polar q ((a * g * a⁻¹ * g⁻¹) x) v = polar q x v + polar q x (g v) * s := by
    intro x
    rw [hc, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, zmod2_polar_self,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero]
  have hpw : ∀ x, polar q ((a * g * a⁻¹ * g⁻¹) x) (g v) =
      polar q x (g v) + (polar q x v + polar q x (g v) * s) * s := by
    intro x
    rw [hc, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, zmod2_polar_self,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero, polar_comm q v (g v)]
  have hrank : finrank (ZMod 2) (LinearMap.range
      (((a * g * a⁻¹ * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id)) ≤ 2 := by
    have hle : LinearMap.range
        (((a * g * a⁻¹ * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) ≤
        Submodule.span (ZMod 2) ((({g v, v} : Finset V)) : Set V) := by
      rintro _ ⟨x, rfl⟩
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
      rw [hc, add_assoc, add_sub_cancel_left]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    calc finrank (ZMod 2) (LinearMap.range
          (((a * g * a⁻¹ * g⁻¹ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id))
        ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) ((({g v, v} : Finset V)) : Set V)) :=
          Submodule.finrank_mono hle
      _ ≤ ({g v, v} : Finset V).card := finrank_span_finset_le_card _
      _ ≤ 2 := Finset.card_le_two
  have hpow : (a * g * a⁻¹ * g⁻¹) ^ 2 = 1 ∨ (a * g * a⁻¹ * g⁻¹) ^ 3 = 1 := by
    have hs01 : s = 0 ∨ s = 1 := by
      generalize s = z
      revert z
      decide
    rcases hs01 with h0 | h1
    · left
      ext x
      rw [pow_two, LinearEquiv.mul_apply, LinearEquiv.coe_one, id, hc ((a * g * a⁻¹ * g⁻¹) x),
        hpv, hpw, hc x, h0]
      generalize polar q x v = α
      generalize polar q x (g v) = β
      match_scalars <;> (revert α β; decide)
    · right
      ext x
      rw [pow_succ, pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_one, id,
        hc ((a * g * a⁻¹ * g⁻¹) ((a * g * a⁻¹ * g⁻¹) x)), hpv ((a * g * a⁻¹ * g⁻¹) x),
        hpw ((a * g * a⁻¹ * g⁻¹) x), hc ((a * g * a⁻¹ * g⁻¹) x), hpv x, hpw x, hc x, h1]
      generalize polar q x v = α
      generalize polar q x (g v) = β
      match_scalars <;> (revert α β; decide)
  have hc1 : a * g * a⁻¹ * g⁻¹ = 1 := by
    by_contra hne
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (a * g * a⁻¹ * g⁻¹) = 2 ∨ orderOf (a * g * a⁻¹ * g⁻¹) = 3 := by
      rcases hpow with h | h
      · exact Or.inl (orderOf_eq_prime h hne)
      · exact Or.inr (orderOf_eq_prime h hne)
    have := hsmall _ hcG hord
    omega
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc1
  exact hc1

end CFSG.LinearAlgebra
