module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.Certificates

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def funAct (g : LinearMap.GeneralLinearGroup K V) (q : V → K) : V → K :=
  fun v => q (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v)

theorem funAct_mul (g h : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    funAct (g * h) q = funAct g (funAct h q) := by
  funext v
  simp only [funAct, mul_inv_rev, Units.val_mul, Module.End.mul_apply]

theorem funAct_one (q : V → K) : funAct (1 : LinearMap.GeneralLinearGroup K V) q = q := by
  funext v
  simp only [funAct, inv_one, Units.val_one, Module.End.one_apply]

theorem funAct_inv_funAct (g : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    funAct g⁻¹ (funAct g q) = q := by
  rw [← funAct_mul, inv_mul_cancel, funAct_one]

theorem funAct_funAct_inv (g : LinearMap.GeneralLinearGroup K V) (q : V → K) :
    funAct g (funAct g⁻¹ q) = q := by
  rw [← funAct_mul, mul_inv_cancel, funAct_one]

@[expose] def funStab (X : Set (V → K)) : Subgroup (LinearMap.GeneralLinearGroup K V) where
  carrier := {g | ∀ q ∈ X, funAct g q ∈ X ∧ funAct g⁻¹ q ∈ X}
  mul_mem' {g h} hg hh q hq := by
    refine ⟨?_, ?_⟩
    · rw [funAct_mul]
      exact (hg _ (hh q hq).1).1
    · rw [mul_inv_rev, funAct_mul]
      exact (hh _ (hg q hq).2).2
  one_mem' q hq := by
    rw [inv_one, funAct_one]
    exact ⟨hq, hq⟩
  inv_mem' {g} hg q hq := by
    rw [inv_inv]
    exact ⟨(hg q hq).2, (hg q hq).1⟩

theorem invariant_function_differences_faithful_action [FiniteDimensional K V]
    (X : Set (V → K)) (hX : X.Finite) (q₀ : V → K) (hq₀ : q₀ ∈ X)
    (_hlin : ∀ q ∈ X, ∃ φ : Module.Dual K V, ∀ v, φ v = q v - q₀ v)
    (hspan : Submodule.span K {φ : Module.Dual K V | ∃ q ∈ X, ∀ v, φ v = q v - q₀ v} = ⊤)
    {I : Type*} (A : I → LinearMap.GeneralLinearGroup K V)
    (hA : ∀ i, ∀ q ∈ X, funAct (A i) q ∈ X) :
    ∃ ρ : Subgroup.closure (Set.range A) →* Equiv.Perm X,
      (∀ g q, ((ρ g q : X) : V → K) = funAct (g : LinearMap.GeneralLinearGroup K V) q) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨A i, Subgroup.subset_closure (Set.mem_range_self i)⟩) := by
  classical
  have : Finite X := hX.to_subtype
  have hAinv : ∀ i, ∀ q ∈ X, funAct (A i)⁻¹ q ∈ X := by
    intro i q hq
    let T : X → X := fun r => ⟨funAct (A i) r, hA i r r.2⟩
    have hT : Function.Injective T := by
      intro r s hrs
      have h := congrArg (fun f : X => funAct (A i)⁻¹ (f : V → K)) hrs
      simp only [T, funAct_inv_funAct] at h
      exact Subtype.ext h
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.1 hT) ⟨q, hq⟩
    have hrq : funAct (A i) r = q := congrArg Subtype.val hr
    rw [← hrq, funAct_inv_funAct]
    exact r.2
  have hle : Subgroup.closure (Set.range A) ≤ funStab X := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩ q hq
    exact ⟨hA i q hq, hAinv i q hq⟩
  let ρ : Subgroup.closure (Set.range A) →* Equiv.Perm X :=
    { toFun := fun g =>
        { toFun := fun q => ⟨funAct (g : LinearMap.GeneralLinearGroup K V) q,
            (hle g.2 q q.2).1⟩
          invFun := fun q => ⟨funAct (g : LinearMap.GeneralLinearGroup K V)⁻¹ q,
            (hle g.2 q q.2).2⟩
          left_inv := fun q => Subtype.ext
            (funAct_inv_funAct (g : LinearMap.GeneralLinearGroup K V) (q : V → K))
          right_inv := fun q => Subtype.ext
            (funAct_funAct_inv (g : LinearMap.GeneralLinearGroup K V) (q : V → K)) }
      map_one' := Equiv.ext fun q => Subtype.ext (funAct_one (q : V → K))
      map_mul' := fun g h => Equiv.ext fun q => Subtype.ext (funAct_mul _ _ (q : V → K)) }
  have hρ : ∀ g q, ((ρ g q : X) : V → K) = funAct (g : LinearMap.GeneralLinearGroup K V) q :=
    fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    set h : V →ₗ[K] V :=
      (((g : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V) :
        V →ₗ[K] V) with hh
    have hfix : ∀ q ∈ X, ∀ v, q (h v) = q v := by
      intro q hq v
      have := congrArg (fun f : Equiv.Perm X => ((f ⟨q, hq⟩ : X) : V → K) v) hg
      exact this
    let S : Submodule K (Module.Dual K V) :=
      { carrier := {φ | ∀ v, φ (h v) = φ v}
        add_mem' := fun {φ ψ} hφ hψ v => by
          simp only [LinearMap.add_apply, hφ v, hψ v]
        zero_mem' := fun v => rfl
        smul_mem' := fun c φ hφ v => by
          simp only [LinearMap.smul_apply, hφ v] }
    have hS : S = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro φ ⟨q, hq, hφ⟩ v
      rw [hφ, hφ, hfix q hq, hfix q₀ hq₀]
    have hhv : ∀ v, h v = v := by
      intro v
      have h0 : ∀ φ : Module.Dual K V, φ (h v - v) = 0 := by
        intro φ
        have hφ : φ ∈ S := hS ▸ Submodule.mem_top
        rw [map_sub, hφ v, sub_self]
      exact sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff K (h v - v)).1 h0)
    have hh1 : ((g : LinearMap.GeneralLinearGroup K V)⁻¹ : LinearMap.GeneralLinearGroup K V) = 1 :=
      Units.ext (LinearMap.ext hhv)
    apply Subtype.ext
    rw [inv_eq_one] at hh1
    exact hh1
  refine ⟨ρ, hρ, hinj, ?_⟩
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage, MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨i, hi⟩ := hg
    refine ⟨i, ?_⟩
    have hgi : (⟨A i, Subgroup.subset_closure (Set.mem_range_self i)⟩ :
        Subgroup.closure (Set.range A)) = g := Subtype.ext hi
    dsimp only
    rw [hgi]
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩

end CFSG.Certificates
