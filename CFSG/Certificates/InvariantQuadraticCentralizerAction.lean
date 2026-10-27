module

public import CFSG.Certificates.InvariantFunctionAction
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Certificates

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def bilinIsometryGroup (B : LinearMap.BilinForm (ZMod 2) V) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) where
  carrier := {g | ∀ u v, B ((g : V →ₗ[ZMod 2] V) u) ((g : V →ₗ[ZMod 2] V) v) = B u v}
  mul_mem' {g h} hg hh u v := by
    change B ((g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) u))
      ((g : V →ₗ[ZMod 2] V) ((h : V →ₗ[ZMod 2] V) v)) = B u v
    rw [hg, hh]
  one_mem' u v := rfl
  inv_mem' {g} hg u v := by
    have h := hg (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) u)
      (((g⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply, Module.End.one_apply] at h
    exact h.symm

theorem invariant_quadratic_centralizer_faithful_action [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (X : Set (V → ZMod 2)) (hX : X.Finite) (_hXne : X.Nonempty)
    (_hβ : ∀ q ∈ X, ∃ β : LinearMap.BilinForm (ZMod 2) V, ∀ u v, β u v = q (u + v) + q u + q v)
    {I : Type*} (A : I → LinearMap.GeneralLinearGroup (ZMod 2) V)
    (hAB : ∀ i u v, B ((A i : V →ₗ[ZMod 2] V) u) ((A i : V →ₗ[ZMod 2] V) v) = B u v)
    (hA : ∀ i, ∀ q ∈ X, funAct (A i) q ∈ X)
    (S : Set (V → ZMod 2)) (hSX : S ⊆ X) (T : (V → ZMod 2) → Module.End (ZMod 2) V)
    (hT : ∀ q ∈ S, ∀ u v, B u (T q v) = q (u + v) + q u + q v)
    (hcomm : {T' : Module.End (ZMod 2) V | ∀ q ∈ S, T' * T q = T q * T'} = {0, 1}) :
    ∃ ρ : Subgroup.closure (Set.range A) →* Equiv.Perm X,
      (∀ g q, ((ρ g q : X) : V → ZMod 2) =
        funAct (g : LinearMap.GeneralLinearGroup (ZMod 2) V) q) ∧
      Function.Injective ρ ∧
      ρ.range = Subgroup.closure (Set.range fun i =>
        ρ ⟨A i, Subgroup.subset_closure (Set.mem_range_self i)⟩) := by
  classical
  have : Finite X := hX.to_subtype
  have hAinv : ∀ i, ∀ q ∈ X, funAct (A i)⁻¹ q ∈ X := by
    intro i q hq
    let F : X → X := fun r => ⟨funAct (A i) r, hA i r r.2⟩
    have hF : Function.Injective F := by
      intro r s hrs
      have h := congrArg (fun f : X => funAct (A i)⁻¹ (f : V → ZMod 2)) hrs
      simp only [F, funAct_inv_funAct] at h
      exact Subtype.ext h
    obtain ⟨r, hr⟩ := (Finite.injective_iff_surjective.1 hF) ⟨q, hq⟩
    have hrq : funAct (A i) r = q := congrArg Subtype.val hr
    rw [← hrq, funAct_inv_funAct]
    exact r.2
  have hle : Subgroup.closure (Set.range A) ≤ funStab X := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩ q hq
    exact ⟨hA i q hq, hAinv i q hq⟩
  have hiso : Subgroup.closure (Set.range A) ≤ bilinIsometryGroup B := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hAB i
  let ρ : Subgroup.closure (Set.range A) →* Equiv.Perm X :=
    { toFun := fun g =>
        { toFun := fun q => ⟨funAct (g : LinearMap.GeneralLinearGroup (ZMod 2) V) q,
            (hle g.2 q q.2).1⟩
          invFun := fun q => ⟨funAct (g : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ q,
            (hle g.2 q q.2).2⟩
          left_inv := fun q => Subtype.ext
            (funAct_inv_funAct (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (q : V → ZMod 2))
          right_inv := fun q => Subtype.ext
            (funAct_funAct_inv (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (q : V → ZMod 2)) }
      map_one' := Equiv.ext fun q => Subtype.ext (funAct_one (q : V → ZMod 2))
      map_mul' := fun g h => Equiv.ext fun q => Subtype.ext (funAct_mul _ _ (q : V → ZMod 2)) }
  have hρ : ∀ g q, ((ρ g q : X) : V → ZMod 2) =
      funAct (g : LinearMap.GeneralLinearGroup (ZMod 2) V) q := fun _ _ => rfl
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    set g' : V →ₗ[ZMod 2] V := ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) with hg'
    set h : V →ₗ[ZMod 2] V :=
      (((g : LinearMap.GeneralLinearGroup (ZMod 2) V)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V) with hh
    have hhg : ∀ v, h (g' v) = v := fun v => by
      rw [hh, hg', ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have hgh : ∀ v, g' (h v) = v := fun v => by
      rw [hh, hg', ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have hfix : ∀ q ∈ X, ∀ v, q (h v) = q v := by
      intro q hq v
      have := congrArg (fun f : Equiv.Perm X => ((f ⟨q, hq⟩ : X) : V → ZMod 2) v) hg
      exact this
    have hBh : ∀ u v, B (h u) (h v) = B u v :=
      hiso (inv_mem g.2)
    have hcommute : ∀ q ∈ S, g' * T q = T q * g' := by
      intro q hq
      have hconj : ∀ v, g' (T q (h v)) = T q v := by
        intro v
        refine sub_eq_zero.1 (hB.2 _ fun u => ?_)
        rw [map_sub, sub_eq_zero, ← hBh u (g' (T q (h v))), hhg, hT q hq, hT q hq, ← map_add,
          hfix q (hSX hq), hfix q (hSX hq), hfix q (hSX hq)]
      refine LinearMap.ext fun v => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, ← hconj (g' v), hhg]
    have hmem : g' ∈ {T' : Module.End (ZMod 2) V | ∀ q ∈ S, T' * T q = T q * T'} := hcommute
    rw [hcomm] at hmem
    rcases hmem with h0 | h1
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      rw [← hgh v, h0, LinearMap.zero_apply]
    · apply Subtype.ext
      exact Units.ext h1
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
