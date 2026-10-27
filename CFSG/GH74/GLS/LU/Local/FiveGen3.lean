module

public import Mathlib.GroupTheory.FixedPointFree

public section

open Subgroup

namespace CFSG.GH74.GLS.LU.Local.Five

section Gen3

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_in_coset {X : Subgroup G} {z r : G} (hz2 : z * z = 1)
    (hzX : ∀ x ∈ X, z * x * z⁻¹ ∈ X) (hXodd : Odd (Nat.card ↥X))
    (hr : (z * r * z⁻¹)⁻¹ * r ∈ X) : ∃ x ∈ X, z * (r * x) * z⁻¹ = r * x := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  set x₁ : G := (z * r * z⁻¹)⁻¹ * r with hx₁
  have hx₁z : z * x₁ * z⁻¹ = x₁⁻¹ := by
    rw [hx₁]
    calc z * ((z * r * z⁻¹)⁻¹ * r) * z⁻¹ = z * (z * r⁻¹ * z⁻¹ * r) * z⁻¹ := by group
      _ = (z * z) * r⁻¹ * (z⁻¹ * (r * z⁻¹)) := by group
      _ = r⁻¹ * (z⁻¹ * (r * z⁻¹)) := by rw [hz2, one_mul]
      _ = ((z * r * z⁻¹)⁻¹ * r)⁻¹ := by
          rw [hz]; group
  let τ : ↥X → ↥X := fun x => ⟨x₁⁻¹ * (z * x * z⁻¹), mul_mem (inv_mem hr) (hzX x x.2)⟩
  have hτ : ∀ x, τ (τ x) = x := by
    intro x
    apply Subtype.ext
    show x₁⁻¹ * (z * (x₁⁻¹ * (z * x * z⁻¹)) * z⁻¹) = x
    have : z * (x₁⁻¹ * (z * x * z⁻¹)) * z⁻¹ = (z * x₁⁻¹ * z⁻¹) * ((z * z) * x * (z⁻¹ * z⁻¹)) := by
      group
    rw [this, hz2]
    have h2 : z * x₁⁻¹ * z⁻¹ = x₁ := by
      have := congrArg (fun y => y⁻¹) hx₁z
      simpa [mul_assoc] using this
    rw [h2]
    have h3 : z⁻¹ * z⁻¹ = 1 := by rw [hz]; exact hz2
    rw [h3]; group
  let σ : Equiv.Perm ↥X := ⟨τ, τ, hτ, hτ⟩
  have hσ2 : σ * σ = 1 := by
    ext x
    exact congrArg Subtype.val (hτ x)
  have hσ : σ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hσ2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype ↥X := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) (by
      intro hd
      have h1 : Nat.card ↥X = Fintype.card ↥X := Nat.card_eq_fintype_card
      rw [← h1] at hd
      exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr hd)) hσ
  refine ⟨x, x.2, ?_⟩
  have hx' : x₁⁻¹ * (z * (x : G) * z⁻¹) = x := congrArg Subtype.val hx
  calc z * (r * x) * z⁻¹ = (z * r * z⁻¹) * (z * (x : G) * z⁻¹) := by group
    _ = (z * r * z⁻¹) * (x₁ * x) := by
        congr 1
        calc z * (x : G) * z⁻¹ = x₁ * (x₁⁻¹ * (z * (x : G) * z⁻¹)) := by group
          _ = x₁ * x := by rw [hx']
    _ = r * x := by rw [hx₁]; group

theorem inverts_quotient_of_fixed {M₀ R X : Subgroup G} {z : G}
    (hz2 : z * z = 1) (hzM : z ∈ M₀) (hRM : M₀ ≤ Subgroup.normalizer (R : Set G))
    (hXM : M₀ ≤ Subgroup.normalizer (X : Set G)) (hXR : X ≤ R)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hXodd : Odd (Nat.card ↥X))
    (hfix : ∀ r ∈ R, z * r * z⁻¹ = r → r ∈ X) :
    (∀ r ∈ R, (z * r * z⁻¹) * r ∈ X) ∧ (∀ r ∈ R, ∀ s ∈ R, r * s * r⁻¹ * s⁻¹ ∈ X) := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzR : ∀ r ∈ R, z * r * z⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hRM hzM) r).mp hr
  have hzX : ∀ x ∈ X, z * x * z⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hXM hzM) x).mp hx
  have hXs : (X.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXR).mpr hRX
  let α₀ : ↥R →* ↥R :=
    { toFun := fun r => ⟨z * r * z⁻¹, hzR r r.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [mul_assoc] }
  have hle : X.subgroupOf R ≤ (X.subgroupOf R).comap α₀ := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hzX x (Subgroup.mem_subgroupOf.mp hx)
  let α : ↥R ⧸ X.subgroupOf R →* ↥R ⧸ X.subgroupOf R :=
    QuotientGroup.map (X.subgroupOf R) (X.subgroupOf R) α₀ hle
  have hα : ∀ r : ↥R, α (QuotientGroup.mk r) = QuotientGroup.mk (α₀ r) := fun r =>
    QuotientGroup.map_mk _ _ _ _ _
  have hfpf : MonoidHom.FixedPointFree α := by
    intro q hq
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hα, QuotientGroup.eq] at hq
    have hq' : (z * (r : G) * z⁻¹)⁻¹ * (r : G) ∈ X := Subgroup.mem_subgroupOf.mp hq
    obtain ⟨x, hx, hxf⟩ := exists_fixed_in_coset hz2 hzX hXodd hq'
    have := hfix _ (mul_mem r.2 (hXR hx)) hxf
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h2 : (r : G) = (r * x) * x⁻¹ := by group
    rw [h2]
    exact mul_mem this (inv_mem hx)
  have hinv : Function.Involutive α := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hα, hα]
    congr 1
    apply Subtype.ext
    show z * (z * (r : G) * z⁻¹) * z⁻¹ = r
    calc z * (z * (r : G) * z⁻¹) * z⁻¹ = (z * z) * r * (z⁻¹ * z⁻¹) := by group
      _ = r := by rw [hz2, hz]; rw [← hz] at hz2 ⊢; simp [hz2]
  have hcoe : ⇑α = (·⁻¹) := hfpf.coe_eq_inv_of_involutive hinv
  have hcomm := hfpf.commute_all_of_involutive hinv
  constructor
  · intro r hr
    have h1 : α (QuotientGroup.mk ⟨r, hr⟩) = (QuotientGroup.mk ⟨r, hr⟩)⁻¹ := by
      rw [hcoe]
    rw [hα] at h1
    have h2 : QuotientGroup.mk (α₀ ⟨r, hr⟩ * ⟨r, hr⟩) = (1 : ↥R ⧸ X.subgroupOf R) := by
      rw [QuotientGroup.mk_mul, h1, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  · intro r hr s hs
    have h1 := hcomm (QuotientGroup.mk ⟨r, hr⟩) (QuotientGroup.mk ⟨s, hs⟩)
    have h2 : QuotientGroup.mk (⟨r, hr⟩ * ⟨s, hs⟩ * ⟨r, hr⟩⁻¹ * ⟨s, hs⟩⁻¹ : ↥R) =
        (1 : ↥R ⧸ X.subgroupOf R) := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [h1]; group
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2

end Gen3

end CFSG.GH74.GLS.LU.Local.Five
