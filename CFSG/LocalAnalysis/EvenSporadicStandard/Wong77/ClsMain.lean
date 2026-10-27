module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsAbstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.ClsMatrix

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Matrix CFSG.Blueprint

theorem module_classification {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (hV : Nat.card V = 2 ^ 11)
    (ρ : NativeSporadic.Carrier .M23 →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) :
    ∃ i : Fin 2, ∃ f : V ≃ₗ[ZMod 2] (Fin 11 → ZMod 2),
      (∀ v, f (ρ gA v) = (stdA i).mulVec (f v)) ∧ (∀ v, f (ρ gB v) = (stdB i).mulVec (f v)) := by
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; positivity)
  let ρl : NativeSporadic.Carrier .M23 →* Module.End (ZMod 2) V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  have hC23 : ρl cE ^ 23 = 1 := by rw [← map_pow, cE_pow, map_one]
  have hY11 : ρl hE ^ 11 = 1 := by rw [← map_pow, hE_pow, map_one]
  have hC1 : ρl cE ≠ 1 := by
    intro h
    apply cE_ne_one
    apply hρ
    rw [map_one]
    apply LinearEquiv.toLinearMap_injective
    exact h
  obtain ⟨v, b, hv, hb⟩ := exists_cyclic_basis hV (ρl cE) (ρl hE) hC23 hC1 hY11
  let N : NativeSporadic.Carrier .M23 →* Mat :=
    { toFun := fun g => LinearMap.toMatrix b b (ρl g)
      map_one' := by simp
      map_mul' := fun g h => by simp [LinearMap.toMatrix_mul] }
  have hN : ∀ g, N g = LinearMap.toMatrix b b (ρl g) := fun _ => rfl
  have hC : N cE = comp (b.repr (ρl cE (b 10))) := by
    rw [hN]; exact toMatrix_cyclic b (ρl cE) v hb
  have hb0 : ρl hE (b 0) = b 0 := by
    have : b 0 = v := by rw [hb]; simp
    rw [this]; exact hv
  have hY : N hE *ᵥ e0 = e0 := by
    rw [hN]; exact toMatrix_fixed b (ρl hE) hb0
  obtain ⟨i, hA, hB⟩ := matrix_classification N _ hC hY
  refine ⟨i, b.equivFun, fun x => ?_, fun x => ?_⟩
  · rw [← hA, hN]
    exact (LinearMap.toMatrix_mulVec_repr b b (ρl gA) x).symm
  · rw [← hB, hN]
    exact (LinearMap.toMatrix_mulVec_repr b b (ρl gB) x).symm

@[expose] def HasType {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : NativeSporadic.Carrier .M23 →* (V ≃ₗ[ZMod 2] V)) (i : Fin 2) : Prop :=
  ∃ f : V ≃ₗ[ZMod 2] (Fin 11 → ZMod 2),
    (∀ v, f (ρ gA v) = (stdA i).mulVec (f v)) ∧ (∀ v, f (ρ gB v) = (stdB i).mulVec (f v))

theorem exists_linearEquiv_of_hasType {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] {i : Fin 2}
    {ρ : NativeSporadic.Carrier .M23 →* (V ≃ₗ[ZMod 2] V)}
    {ρ' : NativeSporadic.Carrier .M23 →* (W ≃ₗ[ZMod 2] W)}
    (h : HasType ρ i) (h' : HasType ρ' i) :
    ∃ F : V ≃ₗ[ZMod 2] W, ∀ g v, F (ρ g v) = ρ' g (F v) := by
  obtain ⟨f, hfA, hfB⟩ := h
  obtain ⟨f', hfA', hfB'⟩ := h'
  refine ⟨f.trans f'.symm, ?_⟩
  have hρ1 : ∀ (g : NativeSporadic.Carrier .M23) (x : V), ρ g (ρ g⁻¹ x) = x := fun g x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hρ2 : ∀ (g : NativeSporadic.Carrier .M23) (x : W), ρ' g⁻¹ (ρ' g x) = x := fun g x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  let S : Subgroup (NativeSporadic.Carrier .M23) :=
    { carrier := {g | ∀ v, (f.trans f'.symm) (ρ g v) = ρ' g ((f.trans f'.symm) v)}
      mul_mem' := fun {g h} hg hh v => by
        simp only [map_mul, LinearEquiv.mul_apply]
        rw [hg (ρ h v), hh v]
      one_mem' := fun v => by simp
      inv_mem' := fun {g} hg v => by
        have h1 := hg (ρ g⁻¹ v)
        rw [hρ1] at h1
        calc (f.trans f'.symm) (ρ g⁻¹ v)
            = ρ' g⁻¹ (ρ' g ((f.trans f'.symm) (ρ g⁻¹ v))) := (hρ2 g _).symm
          _ = ρ' g⁻¹ ((f.trans f'.symm) v) := by rw [← h1] }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← closure_gA_gB, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · intro v
      show f'.symm (f (ρ gA v)) = ρ' gA (f'.symm (f v))
      rw [hfA, LinearEquiv.symm_apply_eq, hfA', LinearEquiv.apply_symm_apply]
    · intro v
      show f'.symm (f (ρ gB v)) = ρ' gB (f'.symm (f v))
      rw [hfB, LinearEquiv.symm_apply_eq, hfB', LinearEquiv.apply_symm_apply]
  intro g v
  have : g ∈ S := by rw [hS]; trivial
  exact this v

theorem exists_isomorphic_pair
    {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂]
    [Module (ZMod 2) V₂] [AddCommGroup V₃] [Module (ZMod 2) V₃]
    (h₁ : Nat.card V₁ = 2 ^ 11) (h₂ : Nat.card V₂ = 2 ^ 11) (h₃ : Nat.card V₃ = 2 ^ 11)
    (ρ₁ : NativeSporadic.Carrier .M23 →* (V₁ ≃ₗ[ZMod 2] V₁)) (hρ₁ : Function.Injective ρ₁)
    (ρ₂ : NativeSporadic.Carrier .M23 →* (V₂ ≃ₗ[ZMod 2] V₂)) (hρ₂ : Function.Injective ρ₂)
    (ρ₃ : NativeSporadic.Carrier .M23 →* (V₃ ≃ₗ[ZMod 2] V₃)) (hρ₃ : Function.Injective ρ₃) :
    (∃ F : V₁ ≃ₗ[ZMod 2] V₂, ∀ g v, F (ρ₁ g v) = ρ₂ g (F v)) ∨
    (∃ F : V₁ ≃ₗ[ZMod 2] V₃, ∀ g v, F (ρ₁ g v) = ρ₃ g (F v)) ∨
    (∃ F : V₂ ≃ₗ[ZMod 2] V₃, ∀ g v, F (ρ₂ g v) = ρ₃ g (F v)) := by
  obtain ⟨i₁, t₁⟩ := module_classification h₁ ρ₁ hρ₁
  obtain ⟨i₂, t₂⟩ := module_classification h₂ ρ₂ hρ₂
  obtain ⟨i₃, t₃⟩ := module_classification h₃ ρ₃ hρ₃
  have t₁' : HasType ρ₁ i₁ := t₁
  have t₂' : HasType ρ₂ i₂ := t₂
  have t₃' : HasType ρ₃ i₃ := t₃
  by_cases h12 : i₁ = i₂
  · subst h12
    exact Or.inl (exists_linearEquiv_of_hasType t₁' t₂')
  · by_cases h13 : i₁ = i₃
    · subst h13
      exact Or.inr (Or.inl (exists_linearEquiv_of_hasType t₁' t₃'))
    · have h23 : i₂ = i₃ := by omega
      subst h23
      exact Or.inr (Or.inr (exists_linearEquiv_of_hasType t₂' t₃'))

end CFSG.EvenSporadicStandard.Wong77.Cls
