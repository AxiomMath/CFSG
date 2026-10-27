module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public section

open scoped Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u v

universe w

theorem exists_equivariant_point_sylow_bijection (p : ℕ) [Fact p.Prime] (F : Type u)
    [Field F] [Finite F] [CharP F p] {Γ : Type v} [Group Γ] [Finite Γ] (L : Subgroup Γ)
    [L.Normal] (ρ : Γ →* Equiv.Perm (Omega F)) (hinj : Function.Injective (ρ.comp L.subtype))
    (hrange : L.map ρ = coordinateG F) :
    ∃ β : Omega F → Sylow p L, Function.Bijective β ∧
      (∀ (γ : Γ) (ω : Omega F), β (ρ γ ω) = MulAut.conjNormal (H := L) γ • β ω) ∧
      ∀ γ : Γ, (Nat.card {ω : Omega F // ρ γ ω = ω} : ℤ) - 1 =
        (Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) γ • P = P} : ℤ) - 1 := by
  obtain ⟨-, -, β₀, -, hβ₀bij, -, hβ₀fix, -, -⟩ :=
    CFSG.LinearGroups.linear_two_point_Sylow_bijection p F
  have hmem : ∀ x : L, ρ x ∈ coordinateG F := fun x => hrange ▸ ⟨x, x.2, rfl⟩
  let f : L →* coordinateG F := (ρ.comp L.subtype).codRestrict _ hmem
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun y => ?_⟩
    have hy : (y : Equiv.Perm (Omega F)) ∈ L.map ρ := by rw [hrange]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let e : L ≃* coordinateG F := MulEquiv.ofBijective f hf
  have he : ∀ x : L, ((e x : coordinateG F) : Equiv.Perm (Omega F)) = ρ x := fun _ => rfl
  have hrangeTop : ∀ P : Sylow p (coordinateG F), (P : Subgroup (coordinateG F)) ≤
      e.toMonoidHom.range := fun P x _ => ⟨e.symm x, e.apply_symm_apply x⟩
  have heinj : Function.Injective e.toMonoidHom := fun a b h => e.injective h
  let β : Omega F → Sylow p L := fun ω =>
    (β₀ ω).comapOfInjective e.toMonoidHom heinj (hrangeTop (β₀ ω))
  have hβmem : ∀ ω (u : L), u ∈ (β ω : Subgroup L) ↔ e u ∈ (β₀ ω : Subgroup (coordinateG F)) := by
    intro ω u
    change u ∈ ((β₀ ω).comapOfInjective e.toMonoidHom heinj _ : Subgroup L) ↔ _
    rw [Sylow.coe_comapOfInjective, Subgroup.mem_comap]
    rfl
  have hfix : ∀ ω, {x : Omega F | ∀ u ∈ (β ω : Subgroup L), ρ u x = x} = {ω} := by
    intro ω
    rw [← hβ₀fix ω]
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h v hv
      have hu : e.symm v ∈ (β ω : Subgroup L) := by
        rw [hβmem, MulEquiv.apply_symm_apply]
        exact hv
      have h' := h _ hu
      rw [← he, MulEquiv.apply_symm_apply] at h'
      exact h'
    · intro h u hu
      rw [← he]
      exact h _ ((hβmem ω u).mp hu)
  have hβinj : Function.Injective β := fun ω₁ ω₂ h => by
    have h1 := hfix ω₁
    rw [h, hfix ω₂] at h1
    exact (Set.singleton_eq_singleton_iff.mp h1).symm
  have hβsurj : Function.Surjective β := by
    intro P
    have hesurj : Function.Surjective e.toMonoidHom := fun y => ⟨e.symm y, e.apply_symm_apply y⟩
    obtain ⟨ω, hω⟩ := hβ₀bij.2 (Sylow.mapSurjective (f := e.toMonoidHom) hesurj P)
    refine ⟨ω, Sylow.ext ?_⟩
    change ((β₀ ω).comapOfInjective e.toMonoidHom heinj _ : Subgroup L) = P
    rw [Sylow.coe_comapOfInjective, hω, Sylow.coe_mapSurjective,
      Subgroup.comap_map_eq_self_of_injective heinj]
  have hconjmem : ∀ (γ : Γ) (P : Sylow p L) (u : L),
      u ∈ ((MulAut.conjNormal (H := L) γ • P : Sylow p L) : Subgroup L) ↔
        (MulAut.conjNormal (H := L) γ⁻¹ u) ∈ (P : Subgroup L) := by
    intro γ P u
    rw [Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
    rfl
  have hequiv : ∀ (γ : Γ) (ω : Omega F), β (ρ γ ω) = MulAut.conjNormal (H := L) γ • β ω := by
    intro γ ω
    obtain ⟨ω', hω'⟩ := hβsurj (MulAut.conjNormal (H := L) γ • β ω)
    have hfix' : {x : Omega F | ∀ u ∈ ((MulAut.conjNormal (H := L) γ • β ω : Sylow p L) :
        Subgroup L), ρ u x = x} = {ρ γ ω} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro h
        have hx : ρ γ⁻¹ x ∈ {x : Omega F | ∀ u ∈ (β ω : Subgroup L), ρ u x = x} := by
          intro v hv
          have hu : MulAut.conjNormal (H := L) γ v ∈
              ((MulAut.conjNormal (H := L) γ • β ω : Sylow p L) : Subgroup L) := by
            rw [hconjmem, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              MulAut.one_apply]
            exact hv
          have h' := h _ hu
          rw [MulAut.conjNormal_apply, map_mul, map_mul, Equiv.Perm.mul_apply,
            Equiv.Perm.mul_apply] at h'
          have h'' := congrArg (ρ γ⁻¹) h'
          rw [← Equiv.Perm.mul_apply (ρ γ⁻¹) (ρ γ), ← map_mul, inv_mul_cancel, map_one,
            Equiv.Perm.one_apply] at h''
          exact h''
        rw [hfix ω, Set.mem_singleton_iff] at hx
        rw [← hx, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply]
      · rintro rfl u hu
        rw [hconjmem] at hu
        have hω : ω ∈ {x : Omega F | ∀ u ∈ (β ω : Subgroup L), ρ u x = x} := by
          rw [hfix ω]
          exact Set.mem_singleton ω
        have h' := hω _ hu
        rw [MulAut.conjNormal_apply, inv_inv, map_mul, map_mul, Equiv.Perm.mul_apply,
          Equiv.Perm.mul_apply] at h'
        have h'' := congrArg (ρ γ) h'
        rw [← Equiv.Perm.mul_apply (ρ γ) (ρ γ⁻¹), ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply] at h''
        exact h''
    rw [← hω', hfix ω'] at hfix'
    rw [← hω', Set.singleton_eq_singleton_iff.mp hfix']
  refine ⟨β, ⟨hβinj, hβsurj⟩, hequiv, fun γ => ?_⟩
  have hcard : Nat.card {ω : Omega F // ρ γ ω = ω} =
      Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) γ • P = P} := by
    refine Nat.card_congr ((Equiv.ofBijective β ⟨hβinj, hβsurj⟩).subtypeEquiv fun ω => ?_)
    change ρ γ ω = ω ↔ MulAut.conjNormal (H := L) γ • β ω = β ω
    rw [← hequiv]
    exact ⟨fun h => by rw [h], fun h => hβinj h⟩
  rw [hcard]

theorem projective_point_action_is_intrinsic_sylow_action (p : ℕ) [Fact p.Prime] (F : Type u)
    [Field F] [Finite F] [CharP F p] {Γ : Type v} [Group Γ] [Finite Γ] (L : Subgroup Γ)
    [L.Normal] (ρ : Γ →* Equiv.Perm (Omega F)) (hinj : Function.Injective (ρ.comp L.subtype))
    (hrange : L.map ρ = coordinateG F) :
    (∃ β : Omega F → Sylow p L, Function.Bijective β ∧
      ∀ (γ : Γ) (ω : Omega F), β (ρ γ ω) = MulAut.conjNormal (H := L) γ • β ω) ∧
      (∀ γ : Γ, (Nat.card {ω : Omega F // ρ γ ω = ω} : ℤ) - 1 =
        (Nat.card {P : Sylow p L // MulAut.conjNormal (H := L) γ • P = P} : ℤ) - 1) ∧
      ∀ (F' : Type w) [Field F'] [Finite F'] [CharP F' p] (ρ' : Γ →* Equiv.Perm (Omega F')),
        Function.Injective (ρ'.comp L.subtype) → L.map ρ' = coordinateG F' → ∀ γ : Γ,
          (Nat.card {ω : Omega F' // ρ' γ ω = ω} : ℤ) - 1 =
            (Nat.card {ω : Omega F // ρ γ ω = ω} : ℤ) - 1 := by
  obtain ⟨β, hβ, hequiv, hcount⟩ :=
    exists_equivariant_point_sylow_bijection p F L ρ hinj hrange
  refine ⟨⟨β, hβ, hequiv⟩, hcount, fun F' _ _ _ ρ' hinj' hrange' γ => ?_⟩
  obtain ⟨-, -, -, hcount'⟩ := exists_equivariant_point_sylow_bijection p F' L ρ' hinj' hrange'
  rw [hcount' γ, hcount γ]

end CFSG.Semidihedral.Principal
