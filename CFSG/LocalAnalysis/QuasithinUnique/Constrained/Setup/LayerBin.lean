module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique
open scoped Multiplicative

section Linear

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def addEquivToLinear (f : W ≃+ W) : W ≃ₗ[ZMod 2] W :=
  { f with map_smul' := fun c x => ZMod.map_smul f.toAddMonoidHom c x }

@[simp] theorem addEquivToLinear_apply (f : W ≃+ W) (w : W) : addEquivToLinear f w = f w := rfl

end Linear

section Psi

variable {V : Type*} [Group V] {W : Type*} [AddCommGroup W]

@[expose] def addEquivOfMulAut (θ : V ≃* Multiplicative W) (φ : MulAut V) : W ≃+ W :=
  AddEquiv.toMultiplicative.symm ((θ.symm.trans φ).trans θ)

theorem addEquivOfMulAut_apply (θ : V ≃* Multiplicative W) (φ : MulAut V) (w : W) :
    addEquivOfMulAut θ φ w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) := rfl

variable [Module (ZMod 2) W]

@[expose] def mulAutOfLinear (θ : V ≃* Multiplicative W) (f : W ≃ₗ[ZMod 2] W) : MulAut V :=
  (θ.trans (AddEquiv.toMultiplicative f.toAddEquiv)).trans θ.symm

theorem mulAutOfLinear_apply (θ : V ≃* Multiplicative W) (f : W ≃ₗ[ZMod 2] W) (v : V) :
    mulAutOfLinear θ f v = θ.symm (Multiplicative.ofAdd (f (Multiplicative.toAdd (θ v)))) := rfl

@[expose] def binPsi (θ : V ≃* Multiplicative W) : MulAut V ≃* (W ≃ₗ[ZMod 2] W) where
  toFun φ := addEquivToLinear (addEquivOfMulAut θ φ)
  invFun f := mulAutOfLinear θ f
  left_inv φ := by
    apply MulEquiv.ext
    intro v
    simp [mulAutOfLinear_apply, addEquivOfMulAut_apply]
  right_inv f := by
    apply LinearEquiv.ext
    intro w
    simp [mulAutOfLinear_apply, addEquivOfMulAut_apply]
  map_mul' φ₁ φ₂ := by
    apply LinearEquiv.ext
    intro w
    simp [addEquivOfMulAut_apply]

theorem binPsi_apply (θ : V ≃* Multiplicative W) (φ : MulAut V) (w : W) :
    binPsi θ φ w = Multiplicative.toAdd (θ (φ (θ.symm (Multiplicative.ofAdd w)))) := rfl

end Psi

section Transport

variable {A B : Type*} [Group A] [Group B]

theorem isSylowTwoOf_map_mulEquiv (e : A ≃* B) {X Y : Subgroup A} :
    IsSylowTwoOf (X.map e.toMonoidHom) (Y.map e.toMonoidHom) ↔ IsSylowTwoOf X Y := by
  unfold IsSylowTwoOf
  rw [Subgroup.map_le_map_iff_of_injective e.injective]
  have h1 : IsPGroup 2 ↥(X.map e.toMonoidHom) ↔ IsPGroup 2 ↥X :=
    ⟨fun h => h.of_equiv (X.equivMapOfInjective e.toMonoidHom e.injective).symm,
      fun h => h.of_equiv (X.equivMapOfInjective e.toMonoidHom e.injective)⟩
  have h2 : ((X.map e.toMonoidHom).subgroupOf (Y.map e.toMonoidHom)).index =
      (X.subgroupOf Y).index :=
    Subgroup.relIndex_map_map_of_injective X Y e.injective
  rw [h1, h2]

theorem normal_subgroupOf_map_iff (e : A ≃* B) {X Y : Subgroup A} (hXY : X ≤ Y) :
    ((X.map e.toMonoidHom).subgroupOf (Y.map e.toMonoidHom)).Normal ↔ (X.subgroupOf Y).Normal := by
  have hXY' : X.map e.toMonoidHom ≤ Y.map e.toMonoidHom := Subgroup.map_mono hXY
  rw [Subgroup.normal_subgroupOf_iff hXY', Subgroup.normal_subgroupOf_iff hXY]
  constructor
  · intro h x y hx hy
    obtain ⟨z, hz, hz'⟩ := h (e x) (e y) ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hzeq : z = y * x * y⁻¹ := e.injective (by
      have h3 : e z = e y * e x * (e y)⁻¹ := hz'
      rw [h3, map_mul, map_mul, map_inv])
    rw [← hzeq]
    exact hz
  · rintro h _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨y * x * y⁻¹, h x y hx hy, by simp⟩

theorem solvable_map_mulEquiv_iff (e : A ≃* B) {Y : Subgroup A} :
    Group.IsSolvable ↥(Y.map e.toMonoidHom) ↔ Group.IsSolvable ↥Y := by
  have eY : ↥Y ≃* ↥(Y.map e.toMonoidHom) := Y.equivMapOfInjective e.toMonoidHom e.injective
  constructor
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := eY.toMonoidHom) eY.injective
  · intro h
    exact Group.isSolvable_of_isSolvable_injective (f := eY.symm.toMonoidHom) eY.symm.injective

theorem isElementaryAbelian_map {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (E : Subgroup X) [hE : CFSG.IsElementaryAbelian p ↥E] :
    CFSG.IsElementaryAbelian p ↥(E.map f) := CFSG.IsElementaryAbelian.subgroup_map inferInstance _

end Transport

end CFSG.QuasithinUnique.Setup.Layer
