module

public import CFSG.LargeExtraspecial.Setting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C2

open Module QuadraticMap CFSG.LargeExtraspecial

abbrev V4 : Type := Fin 4 → ZMod 2

abbrev Vm : Type := V4 × V4

noncomputable def q0 : QuadraticForm (ZMod 2) Vm :=
  LinearMap.BilinMap.toQuadraticMap
    ((Matrix.toBilin' (1 : Matrix (Fin 4) (Fin 4) (ZMod 2))).compl₁₂
      (LinearMap.fst (ZMod 2) V4 V4) (LinearMap.snd (ZMod 2) V4 V4))

theorem q0_apply (v : Vm) : q0 v = v.1 ⬝ᵥ v.2 := by
  simp [q0, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply, Matrix.one_apply,
    dotProduct]

@[expose] def Nsub : Submodule (ZMod 2) Vm := Submodule.prod ⊤ ⊥

@[expose] def Nssub : Submodule (ZMod 2) Vm := Submodule.prod ⊥ ⊤

theorem map_mul_eq (f g : Vm ≃ₗ[ZMod 2] Vm) (W : Submodule (ZMod 2) Vm) :
    W.map ((f * g : Vm ≃ₗ[ZMod 2] Vm) : Vm →ₗ[ZMod 2] Vm) =
      (W.map (g : Vm →ₗ[ZMod 2] Vm)).map (f : Vm →ₗ[ZMod 2] Vm) := by
  rw [← Submodule.map_comp]
  rfl

theorem map_inv_eq {f : Vm ≃ₗ[ZMod 2] Vm} {W W' : Submodule (ZMod 2) Vm}
    (h : W.map (f : Vm →ₗ[ZMod 2] Vm) = W') :
    W'.map ((f⁻¹ : Vm ≃ₗ[ZMod 2] Vm) : Vm →ₗ[ZMod 2] Vm) = W := by
  rw [← h, ← Submodule.map_comp]
  have : ((f⁻¹ : Vm ≃ₗ[ZMod 2] Vm) : Vm →ₗ[ZMod 2] Vm) ∘ₗ (f : Vm →ₗ[ZMod 2] Vm) =
      LinearMap.id := LinearMap.ext fun v => f.symm_apply_apply v
  rw [this, Submodule.map_id]

@[expose] def Hm : Subgroup (Vm ≃ₗ[ZMod 2] Vm) where
  carrier := {f | (∀ v, q0 (f v) = q0 v) ∧
    ((Nsub.map (f : Vm →ₗ[ZMod 2] Vm) = Nsub ∧ Nssub.map (f : Vm →ₗ[ZMod 2] Vm) = Nssub) ∨
      (Nsub.map (f : Vm →ₗ[ZMod 2] Vm) = Nssub ∧ Nssub.map (f : Vm →ₗ[ZMod 2] Vm) = Nsub))}
  mul_mem' := by
    rintro f g ⟨hf, hf' | hf'⟩ ⟨hg, hg' | hg'⟩
    · refine ⟨fun v => by rw [LinearEquiv.mul_apply, hf, hg], Or.inl ?_⟩
      rw [map_mul_eq, map_mul_eq, hg'.1, hg'.2, hf'.1, hf'.2]
      exact ⟨rfl, rfl⟩
    · refine ⟨fun v => by rw [LinearEquiv.mul_apply, hf, hg], Or.inr ?_⟩
      rw [map_mul_eq, map_mul_eq, hg'.1, hg'.2, hf'.1, hf'.2]
      exact ⟨rfl, rfl⟩
    · refine ⟨fun v => by rw [LinearEquiv.mul_apply, hf, hg], Or.inr ?_⟩
      rw [map_mul_eq, map_mul_eq, hg'.1, hg'.2, hf'.1, hf'.2]
      exact ⟨rfl, rfl⟩
    · refine ⟨fun v => by rw [LinearEquiv.mul_apply, hf, hg], Or.inl ?_⟩
      rw [map_mul_eq, map_mul_eq, hg'.1, hg'.2, hf'.1, hf'.2]
      exact ⟨rfl, rfl⟩
  one_mem' := by
    refine ⟨fun v => rfl, Or.inl ⟨?_, ?_⟩⟩
    · exact Submodule.map_id _
    · exact Submodule.map_id _
  inv_mem' := by
    rintro f ⟨hf, hf' | hf'⟩
    · refine ⟨fun v => ?_, Or.inl ⟨map_inv_eq hf'.1, map_inv_eq hf'.2⟩⟩
      have := hf (f⁻¹ v)
      rw [show f (f⁻¹ v) = v from f.apply_symm_apply v] at this
      exact this.symm
    · refine ⟨fun v => ?_, Or.inr ⟨map_inv_eq hf'.2, map_inv_eq hf'.1⟩⟩
      have := hf (f⁻¹ v)
      rw [show f (f⁻¹ v) = v from f.apply_symm_apply v] at this
      exact this.symm

theorem mem_Hm_iff {f : Vm ≃ₗ[ZMod 2] Vm} : f ∈ Hm ↔ (∀ v, q0 (f v) = q0 v) ∧
    ((Nsub.map (f : Vm →ₗ[ZMod 2] Vm) = Nsub ∧ Nssub.map (f : Vm →ₗ[ZMod 2] Vm) = Nssub) ∨
      (Nsub.map (f : Vm →ₗ[ZMod 2] Vm) = Nssub ∧ Nssub.map (f : Vm →ₗ[ZMod 2] Vm) = Nsub)) :=
  Iff.rfl
