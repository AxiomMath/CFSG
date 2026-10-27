module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.Core

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

universe u v

namespace ExtData

section Twist

variable {M W N : Type*} [Group M] [CommGroup W] [Group N] {ρ : M →* MulAut W}
  (X : ExtData ρ N) (τ : M)

theorem conj_eq_one_iff {g : M} : τ⁻¹ * g * τ = 1 ↔ g = 1 := by
  constructor
  · intro h
    calc g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rintro rfl
    group

@[expose] def twist : ExtData ρ N where
  π :=
    { toFun := fun n => τ⁻¹ * X.π n * τ
      map_one' := by simp
      map_mul' := fun x y => by simp only [map_mul]; group }
  eT n := ρ τ⁻¹ (X.eT n)
  π_surjective := fun m => by
    obtain ⟨n, hn⟩ := X.π_surjective (τ * m * τ⁻¹)
    refine ⟨n, ?_⟩
    show τ⁻¹ * X.π n * τ = m
    rw [hn]
    group
  eT_mul := fun x y hx hy => by
    have hx' : X.π x = 1 := (conj_eq_one_iff τ).1 hx
    have hy' : X.π y = 1 := (conj_eq_one_iff τ).1 hy
    show ρ τ⁻¹ (X.eT (x * y)) = ρ τ⁻¹ (X.eT x) * ρ τ⁻¹ (X.eT y)
    rw [X.eT_mul x y hx' hy', map_mul]
  eT_conj := fun n x hx => by
    have hx' : X.π x = 1 := (conj_eq_one_iff τ).1 hx
    have hcancel : ∀ w : W, ρ τ (ρ τ⁻¹ w) = w := fun w => by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    show ρ τ⁻¹ (X.eT (n * x * n⁻¹)) = ρ (τ⁻¹ * X.π n * τ) (ρ τ⁻¹ (X.eT x))
    rw [X.eT_conj n x hx', map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hcancel]
  eT_inj := fun x y hx hy hxy => by
    have hx' : X.π x = 1 := (conj_eq_one_iff τ).1 hx
    have hy' : X.π y = 1 := (conj_eq_one_iff τ).1 hy
    exact X.eT_inj x y hx' hy' ((ρ τ⁻¹).injective hxy)
  eT_surj := fun w => by
    obtain ⟨x, hx, hxe⟩ := X.eT_surj (ρ τ w)
    refine ⟨x, ?_, ?_⟩
    · show τ⁻¹ * X.π x * τ = 1
      rw [hx]
      group
    · show ρ τ⁻¹ (X.eT x) = w
      rw [hxe, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]

end Twist

end ExtData

section Duad

variable {N : Type u} {N₀ : Type v} [Group N] [Group N₀]
  {X : ExtData (rho11 AutPerm le_rfl) N} {X₀ : ExtData (rho11 AutPerm le_rfl) N₀}

theorem conj_mem_K22_iff {τ : ↥AutPerm} {i j : Fin 24}
    (hτ0 : (τ : Equiv.Perm (Fin 24)) 0 = i) (hτ1 : (τ : Equiv.Perm (Fin 24)) 1 = j)
    (σ : ↥AutPerm) :
    τ⁻¹ * σ * τ ∈ K22 ↔
      (σ : Equiv.Perm (Fin 24)) i = i ∧ (σ : Equiv.Perm (Fin 24)) j = j := by
  rw [mem_K22_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, hτ0, hτ1]
  rw [Equiv.Perm.inv_eq_iff_eq, Equiv.Perm.inv_eq_iff_eq, hτ0, hτ1]

theorem exists_mulEquiv_of_extData_duad
    {i j : Fin 24} (hij : i ≠ j)
    {B : Subgroup N} {B₀ : Subgroup N₀}
    (hB : ∀ n, n ∈ B ↔ ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) i = i ∧
      ((X.π n : ↥AutPerm) : Equiv.Perm (Fin 24)) j = j)
    (θ : ↥B ≃* ↥B₀) (hθπ : ∀ b : ↥B, X₀.π (θ b) = X.π b)
    (hθe : ∀ b : ↥B, X.π b = 1 → X₀.eT (θ b) = X.eT b) :
    ∃ Ψ : N ≃* N₀, (∀ x, X.π x = 1 → X₀.eT (Ψ x) = X.eT x) ∧ ∀ n, X₀.π (Ψ n) = X.π n := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two i j hij
  let t : ↥AutPerm := ⟨τ, hτ⟩
  have hB' : ∀ n, n ∈ B ↔ (X.twist t).π n ∈ K22 := fun n =>
    (hB n).trans (conj_mem_K22_iff hτ0 hτ1 (X.π n)).symm
  have hθπ' : ∀ b : ↥B, (X₀.twist t).π (θ b) = (X.twist t).π b := fun b => by
    show t⁻¹ * X₀.π (θ b) * t = t⁻¹ * X.π b * t
    rw [hθπ]
  have hθe' : ∀ b : ↥B, (X.twist t).π b = 1 → (X₀.twist t).eT (θ b) = (X.twist t).eT b :=
    fun b hb => by
      have hb' : X.π b = 1 := (ExtData.conj_eq_one_iff t).1 hb
      show rho11 AutPerm le_rfl t⁻¹ (X₀.eT (θ b)) = rho11 AutPerm le_rfl t⁻¹ (X.eT b)
      rw [hθe b hb']
  obtain ⟨Ψ, hΨe, hΨπ⟩ := exists_mulEquiv_of_extData (X := X.twist t) (X₀ := X₀.twist t)
    hB' θ hθπ' hθe'
  refine ⟨Ψ, fun x hx => ?_, fun n => ?_⟩
  · have hx' : (X.twist t).π x = 1 := by
      show t⁻¹ * X.π x * t = 1
      rw [hx]
      group
    have h1 := hΨe x hx'
    exact (rho11 AutPerm le_rfl t⁻¹).injective h1
  · have h1 := hΨπ n
    change t⁻¹ * X₀.π (Ψ n) * t = t⁻¹ * X.π n * t at h1
    simpa using h1

end Duad

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
