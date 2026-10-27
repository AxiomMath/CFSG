module

public import CFSG.GroupTheory.SteinbergCBHHBIntertwiner
public import CFSG.GroupTheory.SteinbergCBHHBEigenspaces
public import Mathlib.GroupTheory.Nilpotent

public noncomputable section

namespace CFSG.GroupTheory.HallHigmanB

open Module

variable {K U G : Type*} [Field K] [AddCommGroup U] [Module K U] [Group G]

section Restrict

@[expose] def restrictRep (ρ : G →* (Module.End K U)ˣ) (W : Submodule K U)
    (hW : ∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W) :
    G →* (Module.End K W)ˣ where
  toFun g :=
    { val := ((ρ g : (Module.End K U)ˣ) : Module.End K U).restrict (hW g)
      inv := ((ρ g⁻¹ : (Module.End K U)ˣ) : Module.End K U).restrict (hW g⁻¹)
      val_inv := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((ρ g : (Module.End K U)ˣ) : Module.End K U)
          (((ρ g⁻¹ : (Module.End K U)ˣ) : Module.End K U) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
          Units.val_one, Module.End.one_apply]
      inv_val := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((ρ g⁻¹ : (Module.End K U)ˣ) : Module.End K U)
          (((ρ g : (Module.End K U)ˣ) : Module.End K U) w) = w
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
          Units.val_one, Module.End.one_apply] }
  map_one' := by
    ext w
    simp
  map_mul' g h := by
    ext w
    simp

theorem restrictRep_apply (ρ : G →* (Module.End K U)ˣ) (W : Submodule K U)
    (hW : ∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W) (g : G) (w : W) :
    ((((restrictRep ρ W hW g : (Module.End K W)ˣ) : Module.End K W) w : W) : U) =
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) w :=
  rfl

theorem restrictRep_irreducible (ρ : G →* (Module.End K U)ˣ) (W : Submodule K U)
    (hW : ∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W)
    (hmin : ∀ W₁ : Submodule K U, W₁ ≤ W → (∀ g, ∀ w ∈ W₁,
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = W)
    (W₁ : Submodule K W) (hW₁ : ∀ g, ∀ w ∈ W₁,
      ((restrictRep ρ W hW g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁) :
    W₁ = ⊥ ∨ W₁ = ⊤ := by
  have hinv : ∀ g, ∀ u ∈ W₁.map W.subtype,
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) u ∈ W₁.map W.subtype := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨_, hW₁ g w hw, rfl⟩
  rcases hmin _ (by simp [Submodule.map_subtype_le]) hinv with h | h
  · left
    rw [← Submodule.map_bot W.subtype] at h
    exact Submodule.map_injective_of_injective W.injective_subtype h
  · right
    rw [eq_top_iff]
    intro w _
    have : (w : U) ∈ W₁.map W.subtype := by rw [h]; exact w.2
    obtain ⟨w', hw', hww'⟩ := this
    rwa [show w' = w from Subtype.ext hww'] at hw'

theorem exists_minimal_invariant [FiniteDimensional K U] [Nontrivial U]
    (ρ : G →* (Module.End K U)ˣ) : ∃ W : Submodule K U, W ≠ ⊥ ∧
      (∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W) ∧
      ∀ W₁ : Submodule K U, W₁ ≤ W → (∀ g, ∀ w ∈ W₁,
        ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = W := by
  classical
  have hex : ∃ n, ∃ W : Submodule K U, W ≠ ⊥ ∧
      (∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W) ∧
      finrank K W = n := ⟨_, ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  obtain ⟨W, hW0, hWinv, hWn⟩ := Nat.find_spec hex
  refine ⟨W, hW0, hWinv, fun W₁ hW₁ hW₁inv => ?_⟩
  by_cases h : W₁ = ⊥
  · exact Or.inl h
  right
  have hle : finrank K W ≤ finrank K W₁ := by
    rw [hWn]
    exact Nat.find_min' hex ⟨W₁, h, hW₁inv, rfl⟩
  exact Submodule.eq_of_le_of_finrank_le hW₁ hle

theorem restrictRep_injective [Finite G] {q : ℕ} [Fact q.Prime] (hGq : IsPGroup q G)
    (ρ : G →* (Module.End K U)ˣ) (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K U)ˣ) : Module.End K U) = μ • 1)
    (W : Submodule K U) (hW0 : W ≠ ⊥)
    (hW : ∀ g, ∀ w ∈ W, ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W) :
    Function.Injective (restrictRep ρ W hW) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have : Group.IsNilpotent G := hGq.isNilpotent
  obtain ⟨⟨c, hc⟩, hc1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hc1 : c ≠ 1 := fun h => hc1' (Subtype.ext h)
  obtain ⟨hcker, hcZ⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨μ, hμ⟩ := hsc c hcZ
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have h1 : ((ρ c : (Module.End K U)ˣ) : Module.End K U) w = w := by
    have := congrArg (fun A : (Module.End K W)ˣ => (((A : Module.End K W) ⟨w, hwW⟩ : W) : U))
      (MonoidHom.mem_ker.1 hcker)
    simpa [restrictRep_apply] using this
  rw [hμ, LinearMap.smul_apply, Module.End.one_apply] at h1
  have hμ1 : μ = 1 := by
    have h2 : (μ - 1) • w = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hw0)
  apply hc1
  apply hρ
  apply Units.ext
  rw [hμ, hμ1, one_smul, map_one, Units.val_one]

end Restrict

section HomRep

variable {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂]

@[expose] def homRep (ρ₁ : G →* (Module.End K W₁)ˣ) (ρ₂ : G →* (Module.End K W₂)ˣ) :
    Submodule K (W₁ →ₗ[K] W₂) where
  carrier := {φ | ∀ g, φ ∘ₗ ((ρ₁ g : (Module.End K W₁)ˣ) : Module.End K W₁) =
    ((ρ₂ g : (Module.End K W₂)ˣ) : Module.End K W₂) ∘ₗ φ}
  add_mem' {φ ψ} hφ hψ g := by
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' g := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' a φ hφ g := by rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

end HomRep

section Core

variable [IsAlgClosed K] [FiniteDimensional K U] [Nontrivial U] [Finite G]

theorem extraspecial_core {p q m : ℕ} [hp : Fact p.Prime] [CharP K p] [hq : Fact q.Prime]
    (hGq : IsPGroup q G) (ρ : G →* (Module.End K U)ˣ) (hρ : Function.Injective ρ)
    (hsc : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ c : (Module.End K U)ˣ) : Module.End K U) = μ • 1)
    (hcl : ∀ s t : G, t * s * t⁻¹ * s⁻¹ ∈ Subgroup.center G)
    (hnab : ∃ g : G, g ∉ Subgroup.center G) (y : (Module.End K U)ˣ) (θ : MulAut G)
    (hyθ : ∀ g, y * ρ g * y⁻¹ = ρ (θ g)) (hm : 1 ≤ m) (hyP : y ^ (p ^ m) = 1)
    (hfpf : ∀ g : G, g⁻¹ * (θ ^ (p ^ (m - 1))) g ∈ Subgroup.center G →
      g ∈ Subgroup.center G) :
    ((y : Module.End K U) - 1) ^ (p ^ m - 1) ≠ 0 ∨
      ∃ k, 1 ≤ k ∧ p ^ m - 1 = q ^ k ∧ ((y : Module.End K U) - 1) ^ (p ^ m - 2) ≠ 0 := by
  classical
  set P := p ^ m with hPdef
  have hP0 : 0 < P := pow_pos hp.out.pos m
  have hθZ : ∀ c ∈ Subgroup.center G, θ c = c := fun c hc => hρ (by
    obtain ⟨μ, hμ⟩ := hsc c hc
    rw [← hyθ]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hμ, mul_smul_comm, mul_one, smul_mul_assoc, Units.mul_inv])
  have hyθn : ∀ (n : ℕ) (g : G), y ^ n * ρ g * (y ^ n)⁻¹ = ρ ((θ ^ n) g) := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [pow_succ' θ n, MulAut.mul_apply, ← hyθ, ← ih, pow_succ' y n]
      group
  have hθP : ∀ g, (θ ^ P) g = g := fun g => hρ (by rw [← hyθn, hyP]; group)
  obtain ⟨W, hW0, hWinv, hWmin⟩ := exists_minimal_invariant ρ
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW0
  set ρW := restrictRep ρ W hWinv with hρWdef
  have hρW := restrictRep_injective hGq ρ hρ hsc W hW0 hWinv
  have hscW : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρW c : (Module.End K W)ˣ) : Module.End K W) = μ • 1 := fun c hc => by
    obtain ⟨μ, hμ⟩ := hsc c hc
    refine ⟨μ, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [restrictRep_apply, hμ]
    rfl
  have hirrW := restrictRep_irreducible ρ W hWinv hWmin
  obtain ⟨A, hAP, hAρ⟩ := exists_intertwiner ρW hρW hscW hcl hirrW θ hθZ hP0 hθP
  have hAinv : ∀ g, ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) *
      ((ρW g : (Module.End K W)ˣ) : Module.End K W) =
      ((ρW (θ.symm g) : (Module.End K W)ˣ) : Module.End K W) *
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) := fun g => by
    have h1 := hAρ (θ.symm g)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [← Units.val_mul, ← Units.val_mul, ← h1]
    congr 1
    group
  have hyinv : ∀ g, (y : Module.End K U) * ((ρ (θ.symm g) : (Module.End K U)ˣ) :
      Module.End K U) = ((ρ g : (Module.End K U)ˣ) : Module.End K U) * (y : Module.End K U) :=
    fun g => by
      have h1 := hyθ (θ.symm g)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← Units.val_mul, ← Units.val_mul, ← h1]
      congr 1
      group
  set M := homRep ρW ρ with hMdef
  have hτmem : ∀ φ ∈ M, (y : Module.End K U) ∘ₗ φ ∘ₗ
      ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) ∈ M := by
    intro φ hφ g
    refine LinearMap.ext fun w => ?_
    have h1 := congrArg (fun F : Module.End K W => F w) (hAinv g)
    have h2 := congrArg (fun F : W →ₗ[K] U => F (((A⁻¹ : (Module.End K W)ˣ) :
      Module.End K W) w)) (hφ (θ.symm g))
    have h3 := congrArg (fun F : Module.End K U => F (φ (((A⁻¹ : (Module.End K W)ˣ) :
      Module.End K W) w))) (hyinv g)
    simp only [Module.End.mul_apply, LinearMap.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
  let τ : Module.End K M :=
    { toFun := fun φ => ⟨(y : Module.End K U) ∘ₗ φ.1 ∘ₗ
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W), hτmem φ.1 φ.2⟩
      map_add' := fun φ ψ => by
        apply Subtype.ext
        simp [LinearMap.comp_add, LinearMap.add_comp]
      map_smul' := fun a φ => by
        apply Subtype.ext
        simp [LinearMap.comp_smul, LinearMap.smul_comp] }
  have hτpow : ∀ (n : ℕ) (φ : M), ((τ ^ n) φ : W →ₗ[K] U) =
      ((y ^ n : (Module.End K U)ˣ) : Module.End K U) ∘ₗ (φ : W →ₗ[K] U) ∘ₗ
        (((A ^ n)⁻¹ : (Module.End K W)ˣ) : Module.End K W) := by
    intro n
    induction n with
    | zero =>
      intro φ
      refine LinearMap.ext fun w => ?_
      simp
    | succ n ih =>
      intro φ
      rw [pow_succ', Module.End.mul_apply]
      change (y : Module.End K U) ∘ₗ ((τ ^ n) φ : W →ₗ[K] U) ∘ₗ
        ((A⁻¹ : (Module.End K W)ˣ) : Module.End K W) = _
      rw [ih]
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply]
      rw [pow_succ' y n, pow_succ' A n, mul_inv_rev, Units.val_mul, Units.val_mul,
        Module.End.mul_apply, Module.End.mul_apply]
  have hτP : τ ^ P = 1 := by
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hτpow, hyP, hAP, inv_one, Units.val_one, Units.val_one, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
    rfl
  have hsub : W.subtype ∈ M := fun g => LinearMap.ext fun w => rfl
  have hMnt : Nontrivial M := ⟨⟨⟨_, hsub⟩, 0, fun h => by
    have := congrArg Subtype.val h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h2 := congrArg (fun F : W →ₗ[K] U => F w) this
    simp only [Submodule.subtype_apply, ZeroMemClass.coe_zero, LinearMap.zero_apply] at h2
    exact hw (Subtype.ext h2)⟩⟩
  obtain ⟨φ₀, hφ₀, hφ₀0⟩ : ∃ φ₀ : M, τ φ₀ = φ₀ ∧ φ₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective ((τ - 1 : Module.End K M) : M → M) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro φ hφ
      by_contra hne
      exact hne (hcon φ (sub_eq_zero.1 hφ))
    have hzero : (τ - 1 : Module.End K M) ^ P = 0 := by
      rw [hPdef, sub_one_pow_char_pow (p := p), ← hPdef, hτP]
      exact sub_self (1 : Module.End K M)
    have hinjP : Function.Injective (((τ - 1 : Module.End K M) ^ P : Module.End K M) :
        M → M) := by
      rw [Module.End.coe_pow]
      exact hinj.iterate P
    obtain ⟨φ, hφ⟩ := exists_ne (0 : M)
    exact hφ (hinjP (by rw [hzero, LinearMap.zero_apply, map_zero]))
  set φ := (φ₀ : W →ₗ[K] U) with hφdef
  have hφeq : ∀ g w, φ (((ρW g : (Module.End K W)ˣ) : Module.End K W) w) =
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) (φ w) := fun g w =>
    congrArg (fun F : W →ₗ[K] U => F w) (φ₀.2 g)
  have hφy : ∀ w, (y : Module.End K U) (φ w) = φ ((A : Module.End K W) w) := fun w => by
    have h1 := congrArg (fun ψ : M => (ψ : W →ₗ[K] U) ((A : Module.End K W) w)) hφ₀
    simp only [τ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply] at h1
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at h1
    exact h1
  have hφinj : Function.Injective φ := by
    have hker : ∀ g, ∀ w ∈ LinearMap.ker φ,
        ((ρW g : (Module.End K W)ˣ) : Module.End K W) w ∈ LinearMap.ker φ := by
      intro g w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hφeq, hw, map_zero]
    rcases hirrW _ hker with h | h
    · exact LinearMap.ker_eq_bot.1 h
    · exfalso
      apply hφ₀0
      apply Subtype.ext
      exact LinearMap.ker_eq_top.1 h
  set W' := LinearMap.range φ with hW'def
  have hW'inv : ∀ g, ∀ u ∈ W', ((ρ g : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    rintro g _ ⟨w, rfl⟩
    exact ⟨_, hφeq g w⟩
  have hW'y : ∀ u ∈ W', (y : Module.End K U) u ∈ W' := by
    rintro _ ⟨w, rfl⟩
    exact ⟨_, (hφy w).symm⟩
  have hW'ypow : ∀ (n : ℕ), ∀ u ∈ W', ((y ^ n : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    intro n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      rw [pow_succ', Units.val_mul, Module.End.mul_apply]
      exact hW'y _ (ih u hu)
  have hW'yinv : ∀ u ∈ W', ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) u ∈ W' := by
    intro u hu
    have : y⁻¹ = y ^ (P - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hP0, hyP]
    rw [this]
    exact hW'ypow _ u hu
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hφ₀0
    apply Subtype.ext
    exact LinearMap.range_eq_bot.1 h
  have hW'min : ∀ W₁ : Submodule K U, W₁ ≤ W' → (∀ g, ∀ w ∈ W₁,
      ((ρ g : (Module.End K U)ˣ) : Module.End K U) w ∈ W₁) → W₁ = ⊥ ∨ W₁ = W' := by
    intro W₁ hW₁ hW₁inv
    have hinv : ∀ g, ∀ w ∈ W₁.comap φ,
        ((ρW g : (Module.End K W)ˣ) : Module.End K W) w ∈ W₁.comap φ := by
      intro g w hw
      rw [Submodule.mem_comap] at hw ⊢
      rw [hφeq]
      exact hW₁inv g _ hw
    have hmap : (W₁.comap φ).map φ = W₁ := by
      rw [Submodule.map_comap_eq, inf_eq_right.2 hW₁]
    rcases hirrW _ hinv with h | h
    · left
      rw [← hmap, h, Submodule.map_bot]
    · right
      rw [← hmap, h, Submodule.map_top]
  have : Nontrivial W' := Submodule.nontrivial_iff_ne_bot.2 hW'0
  set ρ' := restrictRep ρ W' hW'inv with hρ'def
  have hρ' := restrictRep_injective hGq ρ hρ hsc W' hW'0 hW'inv
  have hsc' : ∀ c ∈ Subgroup.center G, ∃ μ : K,
      ((ρ' c : (Module.End K W')ˣ) : Module.End K W') = μ • 1 := fun c hc => by
    obtain ⟨μ, hμ⟩ := hsc c hc
    refine ⟨μ, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [restrictRep_apply, hμ]
    rfl
  have hirr' := restrictRep_irreducible ρ W' hW'inv hW'min
  let y' : (Module.End K W')ˣ :=
    { val := (y : Module.End K U).restrict hW'y
      inv := ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U).restrict hW'yinv
      val_inv := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change (y : Module.End K U) (((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) w) = w
        rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      inv_val := by
        refine LinearMap.ext fun w => Subtype.ext ?_
        change ((y⁻¹ : (Module.End K U)ˣ) : Module.End K U) ((y : Module.End K U) w) = w
        rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] }
  have hy'apply : ∀ (n : ℕ) (w : W'), ((((y' : Module.End K W') - 1) ^ n) w : U) =
      (((y : Module.End K U) - 1) ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have hy'θ : ∀ g, y' * ρ' g * y'⁻¹ = ρ' (θ g) := fun g => by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    have h1 := congrArg (fun F : Module.End K U => F w) (congrArg Units.val (hyθ g))
    simp only [Units.val_mul, Module.End.mul_apply] at h1
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact h1
  have hy'P : y' ^ P = 1 := by
    apply Units.ext
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hpow : ∀ (n : ℕ) (w : W'), (((y' ^ n : (Module.End K W')ˣ) : Module.End K W') w : U) =
        ((y ^ n : (Module.End K U)ˣ) : Module.End K U) w := by
      intro n
      induction n with
      | zero => intro w; rfl
      | succ n ih =>
        intro w
        rw [pow_succ', Units.val_mul, Module.End.mul_apply, pow_succ', Units.val_mul,
          Module.End.mul_apply, ← ih]
        rfl
    rw [hpow, hyP]
    rfl
  have hcore := irreducible_core hm ρ' hρ' hsc' hcl hirr' hnab y' θ hy'θ hy'P hfpf
  have htransfer : ∀ n, ((y' : Module.End K W') - 1) ^ n ≠ 0 →
      ((y : Module.End K U) - 1) ^ n ≠ 0 := by
    intro n hn h0
    apply hn
    refine LinearMap.ext fun w => Subtype.ext ?_
    rw [hy'apply, h0]
    rfl
  rcases hcore with h | ⟨hd, h⟩
  · exact Or.inl (htransfer _ h)
  right
  have hd2 := finrank_sq_eq_card_quotient_center ρ' hρ' hsc' hcl hirr'
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 (hGq.to_quotient (Subgroup.center G)))
  rw [ha] at hd2
  obtain ⟨k, hk, hdk⟩ := (Nat.dvd_prime_pow hq.out).1 (show finrank K W' ∣ q ^ a from
    ⟨finrank K W', by rw [← sq, hd2]⟩)
  have hd2' : 2 ≤ finrank K W' := by
    have hcard : 2 ≤ Nat.card (G ⧸ Subgroup.center G) := by
      obtain ⟨g, hg⟩ := hnab
      have hne : ((g : G ⧸ Subgroup.center G)) ≠ 1 := fun h =>
        hg ((QuotientGroup.eq_one_iff g).1 h)
      have : Fintype (G ⧸ Subgroup.center G) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card_iff.2 ⟨_, _, hne⟩
    rw [ha, ← hd2] at hcard
    by_contra hlt
    have : finrank K W' ≤ 1 := by omega
    nlinarith
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero] at hdk
      omega
    · exact h
  exact ⟨k, hk1, by rw [← hd, hdk], htransfer _ h⟩

end Core

end CFSG.GroupTheory.HallHigmanB
