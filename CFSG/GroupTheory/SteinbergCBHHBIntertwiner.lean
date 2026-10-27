module

public import CFSG.GroupTheory.SteinbergCBHHBIrreducibleCore
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K W G : Type*} [Field K] [AddCommGroup W] [Module K W] [Group G]

theorem eq_smul_one_of_commute_irreducible [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W]
    (ρ : G →* (Module.End K W)ˣ)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤)
    (B : Module.End K W) (hB : ∀ g, B * ((ρ g : (Module.End K W)ˣ) : Module.End K W) =
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) * B) :
    ∃ μ : K, B = μ • 1 := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue B
  refine ⟨μ, ?_⟩
  have hinv : ∀ g : G, ∀ w ∈ B.eigenspace μ,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ B.eigenspace μ := by
    intro g w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    rw [← Module.End.mul_apply, hB g, Module.End.mul_apply, hw, map_smul]
  rcases hirr _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hμ)
  · ext w
    have : w ∈ B.eigenspace μ := h ▸ Submodule.mem_top
    rw [Module.End.mem_eigenspace_iff] at this
    rw [this, LinearMap.smul_apply, Module.End.one_apply]

@[expose] def unitOfEquiv (T : W ≃ₗ[K] W) : (Module.End K W)ˣ where
  val := T.toLinearMap
  inv := T.symm.toLinearMap
  val_inv := by ext; simp
  inv_val := by ext; simp

theorem exists_intertwiner [IsAlgClosed K] [FiniteDimensional K W] [Nontrivial W] [Finite G]
    (ρ : G →* (Module.End K W)ˣ) (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K W)ˣ) : Module.End K W) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hirr : ∀ W₁ : Submodule K W, (∀ g : G, ∀ w ∈ W₁,
      ((ρ g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = ⊤)
    (θ : MulAut G) (hθZ : ∀ c ∈ Subgroup.center G, θ c = c) {N : ℕ} (hN : 0 < N)
    (hθN : ∀ g, (θ ^ N) g = g) :
    ∃ A : (Module.End K W)ˣ, A ^ N = 1 ∧ ∀ g, A * ρ g * A⁻¹ = ρ (θ g) := by
  classical
  set b := Basis.mk (linearIndependent_rho_out ρ hρ hsc hcl)
    (span_range_rho_out ρ hsc hirr).ge with hbdef
  have hbx : ∀ x, b x = ((ρ x.out : (Module.End K W)ˣ) : Module.End K W) := fun x => by
    rw [hbdef, Basis.mk_apply]
  set L : Module.End K W →ₗ[K] Module.End K W :=
    b.constr K fun x => ((ρ (θ x.out) : (Module.End K W)ˣ) : Module.End K W) with hLdef
  have hLρ : ∀ g, L ((ρ g : (Module.End K W)ˣ) : Module.End K W) =
      ((ρ (θ g) : (Module.End K W)ˣ) : Module.End K W) := by
    intro g
    rw [rho_eq_smul_rho_out ρ hsc g, map_smul, ← hbx, hLdef, b.constr_basis]
    set x := (g : G ⧸ Subgroup.center G)
    have hc : x.out⁻¹ * g ∈ Subgroup.center G := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have h1 : θ g = θ x.out * (x.out⁻¹ * g) := by
      rw [← hθZ _ hc, ← map_mul, mul_inv_cancel_left]
    rw [h1, map_mul, Units.val_mul]
    change _ = _ * ((ρ ((⟨x.out⁻¹ * g, hc⟩ : Subgroup.center G) : G) :
      (Module.End K W)ˣ) : Module.End K W)
    rw [centralScalar_spec ρ hsc, mul_smul_comm, mul_one]
  have hspan := span_range_rho ρ hirr
  have hmul₁ : ∀ (φ : Module.End K W) (h : G), L (φ * ((ρ h : (Module.End K W)ˣ) :
      Module.End K W)) = L φ * L ((ρ h : (Module.End K W)ˣ) : Module.End K W) := by
    intro φ h
    have := LinearMap.ext_on_range hspan (f := L.comp (LinearMap.mulRight K
      ((ρ h : (Module.End K W)ˣ) : Module.End K W)))
      (g := (LinearMap.mulRight K (L ((ρ h : (Module.End K W)ˣ) : Module.End K W))).comp L)
      fun g => by
        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
        rw [← Units.val_mul, ← map_mul, hLρ, hLρ, hLρ, map_mul, map_mul, Units.val_mul]
    exact congrArg (fun F => F φ) this
  have hmul : ∀ φ ψ : Module.End K W, L (φ * ψ) = L φ * L ψ := by
    intro φ ψ
    have := LinearMap.ext_on_range hspan (f := L.comp (LinearMap.mulLeft K φ))
      (g := (LinearMap.mulLeft K (L φ)).comp L) fun h => by
        simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
        exact hmul₁ φ h
    exact congrArg (fun F => F ψ) this
  have hone : L 1 = 1 := by
    have := hLρ 1
    simp only [map_one, Units.val_one] at this
    exact this
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨((ρ (θ.symm g) : (Module.End K W)ˣ) : Module.End K W), ?_⟩
    rw [hLρ, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective L := LinearMap.injective_iff_surjective.2 hsurj
  let Lalg : Module.End K W ≃ₐ[K] Module.End K W :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩) hone hmul
  obtain ⟨T, hT⟩ := Lalg.eq_linearEquivConjAlgEquiv
  set A₀ := unitOfEquiv T with hA₀
  have hA₀ρ : ∀ g, A₀ * ρ g * A₀⁻¹ = ρ (θ g) := by
    intro g
    apply Units.ext
    have h1 := congrArg (fun F : Module.End K W ≃ₐ[K] Module.End K W =>
      F ((ρ g : (Module.End K W)ˣ) : Module.End K W)) hT
    have h2 : L ((ρ g : (Module.End K W)ˣ) : Module.End K W) =
        T.toLinearMap ∘ₗ ((ρ g : (Module.End K W)ˣ) : Module.End K W) ∘ₗ
          T.symm.toLinearMap := h1
    rw [hLρ] at h2
    rw [h2]
    rfl
  have hA₀n : ∀ (n : ℕ) (g : G), A₀ ^ n * ρ g * (A₀ ^ n)⁻¹ = ρ ((θ ^ n) g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' θ n, MulAut.mul_apply, ← hA₀ρ, ← ih, pow_succ' A₀ n]
      group
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_commute_irreducible ρ hirr ((A₀ ^ N : (Module.End K W)ˣ) :
      Module.End K W) fun g => by
    have h1 := hA₀n N g
    rw [hθN] at h1
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc A₀ ^ N * ρ g = (A₀ ^ N * ρ g * (A₀ ^ N)⁻¹) * A₀ ^ N := by group
      _ = ρ g * A₀ ^ N := by rw [h1]
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have := (A₀ ^ N).ne_zero
    rw [hμ, zero_smul] at this
    exact this rfl
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq μ hN
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hν
    exact hμ0 hν.symm
  have hA₀inv : (A₀ : Module.End K W) * ((A₀⁻¹ : (Module.End K W)ˣ) : Module.End K W) = 1 :=
    Units.mul_inv A₀
  have hA₀inv' : ((A₀⁻¹ : (Module.End K W)ˣ) : Module.End K W) * (A₀ : Module.End K W) = 1 :=
    Units.inv_mul A₀
  let A : (Module.End K W)ˣ :=
    { val := ν⁻¹ • (A₀ : Module.End K W)
      inv := ν • ((A₀⁻¹ : (Module.End K W)ˣ) : Module.End K W)
      val_inv := by rw [smul_mul_smul_comm, hA₀inv, inv_mul_cancel₀ hν0, one_smul]
      inv_val := by rw [smul_mul_smul_comm, hA₀inv', mul_inv_cancel₀ hν0, one_smul] }
  refine ⟨A, ?_, fun g => ?_⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change (ν⁻¹ • (A₀ : Module.End K W)) ^ N = 1
    rw [smul_pow, ← Units.val_pow_eq_pow_val, hμ, smul_smul, inv_pow, hν,
      inv_mul_cancel₀ hμ0, one_smul]
  · apply Units.ext
    have h1 := congrArg Units.val (hA₀ρ g)
    rw [Units.val_mul, Units.val_mul] at h1 ⊢
    change ν⁻¹ • (A₀ : Module.End K W) * _ * (ν • ((A₀⁻¹ : (Module.End K W)ˣ) :
      Module.End K W)) = _
    rw [← h1, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hν0,
      one_smul]

end CFSG.GroupTheory.HallHigmanB
