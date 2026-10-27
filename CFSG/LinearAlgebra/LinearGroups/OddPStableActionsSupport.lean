module

public import CFSG.GroupTheory.PStableAction
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.GroupTheory.LocalCores.NormalPKernelPreimage
public import CFSG.GroupTheory.LocalCores.PrimeSetCoreIsomorphism
public import CFSG.Assembly.OrderReductions.ElementaryRepresentation
public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.LinearGroups

open scoped IsMulCommutative
open CFSG.GroupTheory CFSG.OrderReductions.FrattiniAutomorphisms
  CFSG.OrderReductions.ElementaryRepresentation CFSG.LocalCores

universe u

theorem pCore_eq_piCore {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) :
    CFSG.pCore p G = CFSG.piCore {⟨p, hp⟩} G := by
  have : Fact p.Prime := ⟨hp⟩
  unfold CFSG.pCore CFSG.piCore
  congr 1
  ext K
  refine and_congr_right fun _ => ⟨fun hK q hq => ?_, fun hK => ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
    rw [hk] at hq
    exact Set.mem_singleton_iff.mpr
      (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow hq)))
  · refine IsPGroup.of_card
      (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdvd => ?_)
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp (hK ⟨d, hd⟩ hdvd))

theorem isPStableAction_of_quadratic_images {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    {p : ℕ} [Fact p.Prime]
    (hlin : ∀ {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
      (τ : H →* LinearMap.GeneralLinearGroup (ZMod p) V) (x : H),
      ((τ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 → τ.rangeRestrict x ∈ CFSG.pCore p τ.range)
    (P : Type u) [Group P] [Finite P] (hP : IsPGroup p P) (ρ : H →* MulAut P) :
    IsPStableAction p ρ := by
  have hp : p.Prime := Fact.out
  intro x hx
  have hfix : ∀ u : P, ρ x⁻¹ (u⁻¹ * ρ x⁻¹ u) = u⁻¹ * ρ x⁻¹ u := fun u =>
    (double_commutator_eq_one_iff ρ u x).mp (hx u)
  obtain ⟨-, -, -, helem, -⟩ := frattini_elementary_quotient hP
  have : FiniteDimensional (ZMod p) (Additive (P ⧸ frattini P)) := by
    have : Finite (Additive (P ⧸ frattini P)) := inferInstanceAs (Finite (P ⧸ frattini P))
    exact Module.Finite.of_finite
  let χ := (linearRepresentation p
    ((quotientAutomorphism (frattini P)).comp ρ.range.subtype)).asGroupHom
  let τ : H →* LinearMap.GeneralLinearGroup (ZMod p) (Additive (P ⧸ frattini P)) :=
    χ.comp ρ.rangeRestrict
  have hmap : (frattini P).map (ρ x⁻¹).toMonoidHom = frattini P :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance (ρ x⁻¹)
  have hτ : (τ x⁻¹ : Module.End (ZMod p) (Additive (P ⧸ frattini P))) =
      quotientLinearMap p (frattini P) (ρ x⁻¹) (le_comap_of_map_eq _ hmap) := by
    apply LinearMap.ext
    intro v
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    obtain rfl : v = Additive.ofMul (u : P ⧸ frattini P) := by rw [hu]; rfl
    rw [quotientLinearMap_apply]
    change Additive.ofMul (quotientAutomorphism (frattini P) (ρ x⁻¹)
      (QuotientGroup.mk' (frattini P) u)) = _
    rw [quotientAutomorphism_apply]
    rfl
  have hquad := quadratic_elementary_quotient p (frattini P) (ρ x⁻¹) hmap hfix
  rw [← hτ] at hquad
  have hcore := hlin τ x⁻¹ hquad
  have : Finite ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have : Finite τ.range := Finite.of_surjective _ τ.rangeRestrict_surjective
  rw [pCore_eq_piCore hp] at hcore
  have hN : IsPGroup p χ.ker := by
    change IsPGroup p (linearRepresentation p
      ((quotientAutomorphism (frattini P)).comp ρ.range.subtype)).asGroupHom.ker
    rw [linearRepresentation_kernel, ← MonoidHom.comap_ker]
    exact (frattini_automorphism_kernel hP).2.comap_subtype
  have hrange : χ.range = τ.range := by
    change χ.range = (χ.comp ρ.rangeRestrict).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ρ.rangeRestrict_surjective,
      ← MonoidHom.range_eq_map]
  let e : ρ.range ⧸ χ.ker ≃* τ.range :=
    (QuotientGroup.quotientKerEquivRange χ).trans (MulEquiv.subgroupCongr hrange)
  have he : e (ρ.rangeRestrict x⁻¹ : ρ.range ⧸ χ.ker) = τ.rangeRestrict x⁻¹ := rfl
  have h₁ : (ρ.rangeRestrict x⁻¹ : ρ.range ⧸ χ.ker) ∈ CFSG.piCore {⟨p, hp⟩} (ρ.range ⧸ χ.ker) := by
    rw [← prime_set_core_isomorphism e, Subgroup.mem_map_equiv, ← he,
      MulEquiv.symm_apply_apply] at hcore
    exact hcore
  have h₂ : ρ.rangeRestrict x⁻¹ ∈ CFSG.piCore {⟨p, hp⟩} ρ.range := by
    rw [← normal_p_kernel_core_preimage hp χ.ker hN]
    exact h₁
  have h₃ : ρ.rangeRestrict x ∈ CFSG.piCore {⟨p, hp⟩} ρ.range := by
    have h := inv_mem h₂
    rwa [← map_inv, inv_inv] at h
  let e₁ : H ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  have he₁ : e₁ (x : H ⧸ ρ.ker) = ρ.rangeRestrict x := rfl
  rw [← prime_set_core_isomorphism e₁, Subgroup.mem_map_equiv, ← he₁,
    MulEquiv.symm_apply_apply] at h₃
  change QuotientGroup.mk' ρ.ker x ∈ CFSG.pCore p (H ⧸ ρ.ker)
  rw [pCore_eq_piCore hp]
  exact h₃

end CFSG.LinearGroups
