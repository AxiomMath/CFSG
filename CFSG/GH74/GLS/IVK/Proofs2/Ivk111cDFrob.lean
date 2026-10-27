module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open scoped TensorProduct MonoidAlgebra

section Frob

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F] [Algebra (ZMod p) F] [CharP F p]

@[expose] noncomputable def frobLin : F →ₗ[ZMod p] F where
  toFun c := c ^ p
  map_add' x y := add_pow_char x y p
  map_smul' a c := by simp [Algebra.smul_def, mul_pow, ← map_pow, ZMod.pow_card]

omit [Finite F] in
theorem frobLin_apply (c : F) : frobLin (p := p) c = c ^ p := rfl

theorem frobLin_bijective : Function.Bijective (frobLin (p := p) (F := F)) := by
  have hinj : Function.Injective (frobLin (p := p) (F := F)) := (frobenius_inj F p)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

variable (W : Type) [AddCommGroup W] [Module (ZMod p) W]

@[expose] noncomputable def frobTensor : F ⊗[ZMod p] W →ₗ[ZMod p] F ⊗[ZMod p] W :=
  TensorProduct.map (frobLin (p := p) (F := F)) LinearMap.id

variable {W}

omit [Finite F] in
theorem frobTensor_tmul (c : F) (w : W) : frobTensor W (c ⊗ₜ[ZMod p] w) = (c ^ p) ⊗ₜ[ZMod p] w := by
  simp [frobTensor, frobLin_apply]

omit [Finite F] in
theorem frobTensor_smul (c : F) (x : F ⊗[ZMod p] W) :
    frobTensor W (c • x) = c ^ p • frobTensor W x := by
  induction x using TensorProduct.inductionOn with
  | tmul a w => simp [TensorProduct.smul_tmul', frobTensor_tmul, mul_pow]
  | add x y hx hy => simp [smul_add, hx, hy]

omit [Finite F] in
theorem frobTensor_baseChange (f : W →ₗ[ZMod p] W) (x : F ⊗[ZMod p] W) :
    frobTensor W (f.baseChange F x) = f.baseChange F (frobTensor W x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a w => simp [frobTensor_tmul]
  | add x y hx hy => simp [hx, hy]

theorem frobTensor_bijective : Function.Bijective (frobTensor (p := p) (F := F) W) := by
  have : frobTensor (p := p) (F := F) W =
      (TensorProduct.congr (LinearEquiv.ofBijective (frobLin (p := p) (F := F)) frobLin_bijective)
        (LinearEquiv.refl (ZMod p) W)) := by
    ext c w
    simp [frobTensor_tmul, frobLin_apply]
  rw [this]
  exact LinearEquiv.bijective _

end Frob

end CFSG.GH74.GLS.Stage4.Rest
