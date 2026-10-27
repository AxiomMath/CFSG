module

public import CFSG.GroupTheory.MonomialProjRank
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis

public section

namespace CFSG.GroupTheory

open Matrix LinearMap
open scoped commutatorElement

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem card_le_pow_finrank_sub_one_mul_card_scalar
    {F : Type} {V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrF : r ∣ Nat.card F - 1)
    (R : Subgroup (V ≃ₗ[F] V)) (hR : IsPGroup r R)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, ∃ a : F, ∀ v, (x * y * x⁻¹ * y⁻¹) v = a • v)
    (hpow : ∀ x ∈ R, ∃ a : F, ∀ v, (x ^ r) v = a • v) :
    Nat.card R ≤ r ^ (Module.finrank F V - 1) *
      Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} := by
  classical
  set m := Module.finrank F V with hm_def
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have hfin : Module.finrank F V = 0 := by rw [← hm_def, hm]
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hfin
    haveI : Subsingleton (V ≃ₗ[F] V) := inferInstance
    have hRbot : R = ⊥ := Subgroup.eq_bot_of_subsingleton R
    have hsub : Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} = 1 := by
      apply Nat.card_eq_one_iff_unique.mpr
      refine ⟨inferInstance, ⟨⟨1, 1, ?_⟩⟩⟩
      intro v
      simp
    rw [hsub, hRbot, Subgroup.card_bot, hm]
    simp
  · have hmpos : 0 < m := hm
    let b : Module.Basis (Fin m) F V := Module.finBasis F V
    let ψ : (V ≃ₗ[F] V) ≃* GL (Fin m) F := b.toGL
    let R' : Subgroup (GL (Fin m) F) := R.map ψ.toMonoidHom
    haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [← hm_def]; exact hm)
    have hR' : IsPGroup r R' := hR.map ψ.toMonoidHom
    have hcoeff : ∀ {x : V ≃ₗ[F] V} {a : F}, (∀ v, x v = a • v) → a ≠ 0 := by
      intro x a hx h0
      have hx0 : ∀ v, x v = 0 := by
        intro v
        rw [hx v, h0, zero_smul]
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (x.injective (by rw [hx0 v, map_zero]))
    have hpow' : ∀ x ∈ R', x ^ r ∈ Subgroup.center (GL (Fin m) F) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨a, ha⟩ := hpow y hy
      have ha0 : a ≠ 0 := hcoeff ha
      have hy_eq : (y : V ≃ₗ[F] V) ^ r = LinearEquiv.smulOfUnit (Units.mk0 a ha0) := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.smulOfUnit_apply]
        exact ha v
      have hmat : (ψ y) ^ r =
          Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 a ha0) := by
        rw [← map_pow ψ y r]
        change b.toGL ((y : V ≃ₗ[F] V) ^ r) =
          Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 a ha0)
        rw [hy_eq, b.toGL_smulOfUnit]
      change (ψ y) ^ r ∈ Subgroup.center (GL (Fin m) F)
      rw [hmat, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact MonoidHom.mem_range.2 ⟨Units.mk0 a ha0, rfl⟩
    have hcomm' : ∀ x ∈ R', ∀ z ∈ R',
        ⁅x, z⁆ ∈ Subgroup.center (GL (Fin m) F) := by
      intro x hx z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨a, ha⟩ := hcomm y hy w hw
      have ha0 : a ≠ 0 := hcoeff ha
      have hcomm_eq : (y * w * y⁻¹ * w⁻¹ : V ≃ₗ[F] V) =
          LinearEquiv.smulOfUnit (Units.mk0 a ha0) := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.smulOfUnit_apply]
        exact ha v
      have hmat : ⁅ψ y, ψ w⁆ =
          Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 a ha0) := by
        rw [← map_commutatorElement]
        change b.toGL ((y * w * y⁻¹ * w⁻¹ : V ≃ₗ[F] V)) =
          Matrix.GeneralLinearGroup.scalar (Fin m) (Units.mk0 a ha0)
        rw [hcomm_eq, b.toGL_smulOfUnit]
      change ⁅ψ y, ψ w⁆ ∈ Subgroup.center (GL (Fin m) F)
      rw [hmat, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact MonoidHom.mem_range.2 ⟨Units.mk0 a ha0, rfl⟩
    have hRR' : Nat.card R' = Nat.card R :=
      Subgroup.card_map_of_injective (K := R) ψ.injective
    have hmatrix := card_le_pow_sub_one_mul_card_inf_scalars_GL
      (F := F) (m := m) (r := r) hr hr2 hrF R' hR' hcomm' hpow'
    have hscalar : Nat.card {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} =
        Nat.card ↥(R' ⊓ Subgroup.center (GL (Fin m) F)) := by
      let Φ : {x : R // ∃ a : F, ∀ v, (x : V ≃ₗ[F] V) v = a • v} →
          ↥(R' ⊓ Subgroup.center (GL (Fin m) F)) := fun x =>
        ⟨ψ x.1, ⟨Subgroup.mem_map_of_mem ψ.toMonoidHom x.1.2, by
          obtain ⟨a, ha⟩ := x.2
          have ha0 : a ≠ 0 := hcoeff ha
          have hx_eq : (x.1 : V ≃ₗ[F] V) =
              LinearEquiv.smulOfUnit (Units.mk0 a ha0) := by
            apply LinearEquiv.ext
            intro v
            rw [LinearEquiv.smulOfUnit_apply]
            exact ha v
          rw [hx_eq, b.toGL_smulOfUnit, Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact MonoidHom.mem_range.2 ⟨Units.mk0 a ha0, rfl⟩⟩⟩
      have hΦinj : Function.Injective Φ := by
        intro x x' h
        apply Subtype.ext
        apply Subtype.ext
        apply ψ.injective
        exact congrArg Subtype.val h
      have hΦsurj : Function.Surjective Φ := by
        intro y
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 y.2.1
        have hyS : y.1 ∈ (Matrix.GeneralLinearGroup.scalar (Fin m)).range := by
          rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact y.2.2
        obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hyS
        have hz_eq : z = LinearEquiv.smulOfUnit u := by
          apply ψ.injective
          calc ψ z = ↑y := hzy
            _ = Matrix.GeneralLinearGroup.scalar (Fin m) u := hu.symm
            _ = ψ (LinearEquiv.smulOfUnit u) := (b.toGL_smulOfUnit u).symm
        refine ⟨⟨⟨z, hz⟩, ⟨(u : F), fun v => ?_⟩⟩, ?_⟩
        · change z v = (u : F) • v
          rw [hz_eq, LinearEquiv.smulOfUnit_apply]
        · apply Subtype.ext
          exact hzy
      exact Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩)
    rw [hscalar]
    calc Nat.card R = Nat.card R' := hRR'.symm
      _ ≤ r ^ (m - 1) * Nat.card ↥(R' ⊓ Subgroup.center (GL (Fin m) F)) := hmatrix

end CFSG.GroupTheory
