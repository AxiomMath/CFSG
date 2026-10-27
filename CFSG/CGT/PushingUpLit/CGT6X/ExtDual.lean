module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtCocycle
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

section Transfer

variable {G H V₁ V₂ : Type*} [Group G] [Group H] [CommGroup V₁] [CommGroup V₂]

theorem isCoboundary_of_equiv {ρ₁ : G →* MulAut V₁} {ρ₂ : G →* MulAut V₂} (e : V₁ ≃* V₂)
    (he : ∀ g v, e (ρ₁ g v) = ρ₂ g (e v))
    (h : ∀ c : G → V₁, IsCocycle ρ₁ c → IsCoboundary ρ₁ c) {c : G → V₂}
    (hc : IsCocycle ρ₂ c) : IsCoboundary ρ₂ c := by
  have he' : ∀ g v, e.symm (ρ₂ g v) = ρ₁ g (e.symm v) := fun g v => by
    apply e.injective
    rw [he, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hc₁ : IsCocycle ρ₁ (fun g => e.symm (c g)) := by
    intro g h'
    simp only [hc g h', map_mul, he']
  obtain ⟨m, hm⟩ := h _ hc₁
  refine ⟨e m, fun g => ?_⟩
  have := congrArg e (hm g)
  rw [MulEquiv.apply_symm_apply, map_mul, he, map_inv] at this
  exact this

theorem isCoboundary_comp {ρ : H →* MulAut V₁} (θ : G ≃* H)
    (h : ∀ c : H → V₁, IsCocycle ρ c → IsCoboundary ρ c) {c : G → V₁}
    (hc : IsCocycle (ρ.comp θ.toMonoidHom) c) : IsCoboundary (ρ.comp θ.toMonoidHom) c := by
  have hc' : IsCocycle ρ (fun x => c (θ.symm x)) := by
    intro x y
    have := hc (θ.symm x) (θ.symm y)
    simpa [map_mul] using this
  obtain ⟨m, hm⟩ := h _ hc'
  refine ⟨m, fun g => ?_⟩
  have := hm (θ g)
  simpa using this

end Transfer

section Dual

variable {H M : Type*} [Group H] [CommGroup M]

abbrev Dual (M : Type*) [CommGroup M] : Type _ := M →* Multiplicative (ZMod 2)

instance instCommGroupDual (M : Type*) [CommGroup M] : CommGroup (Dual M) :=
  inferInstanceAs (CommGroup (M →* Multiplicative (ZMod 2)))

theorem dual_mul_apply {M : Type*} [CommGroup M] (φ ψ : Dual M) (m : M) :
    (φ * ψ) m = φ m * ψ m := rfl

theorem dual_one_apply {M : Type*} [CommGroup M] (m : M) : (1 : Dual M) m = 1 := rfl

theorem dual_inv_apply {M : Type*} [CommGroup M] (φ : Dual M) (m : M) : (φ⁻¹) m = (φ m)⁻¹ := rfl

theorem act_inv_act (σ : H →* MulAut M) (h : H) (m : M) : σ h⁻¹ (σ h m) = m := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

theorem act_act_inv (σ : H →* MulAut M) (h : H) (m : M) : σ h (σ h⁻¹ m) = m := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

@[expose] noncomputable def dualAut (σ : H →* MulAut M) (h : H) : MulAut (Dual M) where
  toFun φ := φ.comp (σ h⁻¹).toMonoidHom
  invFun φ := φ.comp (σ h).toMonoidHom
  left_inv φ := by
    ext m
    show φ (σ h⁻¹ (σ h m)) = φ m
    rw [act_inv_act]
  right_inv φ := by
    ext m
    show φ (σ h (σ h⁻¹ m)) = φ m
    rw [act_act_inv]
  map_mul' φ ψ := rfl

@[expose] noncomputable def dualAct (σ : H →* MulAut M) : H →* MulAut (Dual M) where
  toFun := dualAut σ
  map_one' := by
    refine MulEquiv.ext fun φ => ?_
    ext m
    show φ ((σ 1⁻¹) m) = φ m
    rw [inv_one, map_one]
    rfl
  map_mul' h h' := by
    refine MulEquiv.ext fun φ => ?_
    ext m
    show φ ((σ (h * h')⁻¹) m) = φ ((σ h'⁻¹) ((σ h⁻¹) m))
    rw [mul_inv_rev, map_mul]
    rfl

theorem dualAct_apply (σ : H →* MulAut M) (h : H) (φ : Dual M) (m : M) :
    dualAct σ h φ m = φ (σ h⁻¹ m) := rfl

theorem isCoboundary_dual_of_equiv {σ : H →* MulAut M} (ι : M ≃* Dual M)
    (hι : ∀ h m, ι (σ h m) = dualAct σ h (ι m))
    (hM : ∀ c : H → M, IsCocycle σ c → IsCoboundary σ c) {γ : H → Dual M}
    (hγ : IsCocycle (dualAct σ) γ) : IsCoboundary (dualAct σ) γ :=
  isCoboundary_of_equiv ι hι hM hγ

end Dual

section Detect

theorem exists_addMonoidHom_eq_one {A : Type*} [AddCommGroup A] (hA : ∀ a : A, a + a = 0)
    {a : A} (ha : a ≠ 0) : ∃ ℓ : A →+ ZMod 2, ℓ a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Module (ZMod 2) A := AddCommGroup.zmodModule (fun g => by rw [two_nsmul]; exact hA g)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  exact ⟨f.toAddMonoidHom, hf⟩

theorem exists_char_eq_ofAdd_one {A : Type*} [CommGroup A] (hA : ∀ a : A, a ^ 2 = 1) {a : A}
    (ha : a ≠ 1) : ∃ χ : A →* Multiplicative (ZMod 2), χ a = Multiplicative.ofAdd 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_addMonoidHom_eq_one (A := Additive A) (fun x => by
    have := hA (Additive.toMul x)
    rw [pow_two] at this
    exact this) (a := Additive.ofMul a) (by simpa using ha)
  refine ⟨{ toFun := fun x => Multiplicative.ofAdd (ℓ (Additive.ofMul x))
            map_one' := by simp
            map_mul' := fun x y => by simp }, ?_⟩
  exact congrArg Multiplicative.ofAdd hℓ

end Detect

end CFSG.CGT.PushingUpLit.CGT6X
