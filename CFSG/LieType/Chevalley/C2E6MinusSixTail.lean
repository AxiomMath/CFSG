module

public import CFSG.LieType.Chevalley.C2E6MinusSixVertices
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def mapVertex (g : QuadraticMap.IsometryEquiv Q Q) (x : QVertex) : QVertex :=
  ⟨x.1.map (g.toLinearEquiv : X →ₗ[ZMod 2] X), by
    rintro _ ⟨y, hy, rfl⟩
    exact (g.map_app y).trans (x.2.1 y hy), by
    rw [LinearEquiv.finrank_map_eq]
    exact x.2.2⟩

theorem coe_mapVertex (g : QuadraticMap.IsometryEquiv Q Q) (x : QVertex) :
    (mapVertex g x).1 = x.1.map (g.toLinearEquiv : X →ₗ[ZMod 2] X) := rfl

theorem mapVertex_mapVertex {g h : QuadraticMap.IsometryEquiv Q Q} (hgh : ∀ v, h (g v) = v)
    (x : QVertex) : mapVertex h (mapVertex g x) = x := by
  apply Subtype.ext
  ext v
  simp only [coe_mapVertex, Submodule.mem_map]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have : (h.toLinearEquiv : X →ₗ[ZMod 2] X) ((g.toLinearEquiv : X →ₗ[ZMod 2] X) u) = u := hgh u
    rw [this]
    exact hu
  · intro hv
    exact ⟨g v, ⟨v, hv, rfl⟩, hgh v⟩

@[expose] def inducedPerm (g : QuadraticMap.IsometryEquiv Q Q) : Equiv.Perm QVertex where
  toFun := mapVertex g
  invFun := mapVertex g.symm
  left_inv := mapVertex_mapVertex g.symm_apply_apply
  right_inv := mapVertex_mapVertex g.apply_symm_apply

theorem coe_inducedPerm (g : QuadraticMap.IsometryEquiv Q Q) (x : QVertex) :
    (inducedPerm g x).1 = x.1.map (g.toLinearEquiv : X →ₗ[ZMod 2] X) := rfl

theorem inducedPerm_mem_typeAut (g : QuadraticMap.IsometryEquiv Q Q) :
    inducedPerm g ∈ typeAut := by
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · exact LinearEquiv.finrank_map_eq _ _
  · simp only [QVertex.Incident, coe_inducedPerm]
    rw [Submodule.map_le_map_iff_of_injective g.toLinearEquiv.injective,
      Submodule.map_le_map_iff_of_injective g.toLinearEquiv.injective]

theorem inducedPerm_trans (g h : QuadraticMap.IsometryEquiv Q Q) :
    inducedPerm (g.trans h) = inducedPerm h * inducedPerm g := by
  ext x : 1
  apply Subtype.ext
  simp only [coe_inducedPerm, Equiv.Perm.mul_apply]
  rw [← Submodule.map_comp]
  rfl

theorem inducedPerm_symm (g : QuadraticMap.IsometryEquiv Q Q) :
    inducedPerm g.symm = (inducedPerm g)⁻¹ := rfl

theorem inducedPerm_ptVertex (g : QuadraticMap.IsometryEquiv Q Q) {i i' : Fin 27}
    (h : g (ptVec i) = ptVec i') : inducedPerm g (ptVertex i) = ptVertex i' := by
  apply Subtype.ext
  rw [coe_inducedPerm]
  simp only [ptVertex, ptSub]
  rw [Submodule.map_span, Set.image_singleton]
  exact congrArg (fun v => (ZMod 2) ∙ v) h

theorem inducedPerm_lnVertex (g : QuadraticMap.IsometryEquiv Q Q) {j j' : Fin 45} {p q : Fin 27}
    (hp : g (ptVec (lnA j)) = ptVec p) (hq : g (ptVec (lnB j)) = ptVec q) (hpj : PtOn p j')
    (hqj : PtOn q j') (hpq : p ≠ q) : inducedPerm g (lnVertex j) = lnVertex j' := by
  apply Subtype.ext
  rw [coe_inducedPerm]
  simp only [lnVertex, lnSub]
  rw [Submodule.map_span, Set.image_pair]
  change Submodule.span (ZMod 2) {g (ptVec (lnA j)), g (ptVec (lnB j))} = _
  rw [hp, hq]
  exact span_ptVec_eq_lnSub hpj hqj hpq

@[expose] def tailLin (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) : X →ₗ[ZMod 2] X where
  toFun x := ![x 0, x 1, x 2, x 3, A 0 0 * x 4 + A 0 1 * x 5, A 1 0 * x 4 + A 1 1 * x 5]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp <;> ring

theorem tailLin_apply (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (x : X) :
    tailLin A x = ![x 0, x 1, x 2, x 3, A 0 0 * x 4 + A 0 1 * x 5, A 1 0 * x 4 + A 1 1 * x 5] :=
  rfl

theorem tailLin_mul (A B : Matrix (Fin 2) (Fin 2) (ZMod 2)) (x : X) :
    tailLin (A * B) x = tailLin A (tailLin B x) := by
  funext i
  fin_cases i <;> simp [tailLin_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tailLin_one (x : X) : tailLin 1 x = x := by
  funext i
  fin_cases i <;> simp [tailLin_apply]

@[expose] def tailMap (A : GL (Fin 2) (ZMod 2)) : X ≃ₗ[ZMod 2] X :=
  LinearEquiv.ofLinearMap (tailLin A) (tailLin ↑A⁻¹)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← tailLin_mul, Units.mul_inv, tailLin_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← tailLin_mul, Units.inv_mul, tailLin_one, LinearMap.id_apply])

theorem tailMap_apply (A : GL (Fin 2) (ZMod 2)) (x : X) : tailMap A x = tailLin A x := rfl

theorem tail_norm_invariant : ∀ a b c d t u : ZMod 2, a * d - b * c ≠ 0 →
    (a * t + b * u) ^ 2 + (a * t + b * u) * (c * t + d * u) + (c * t + d * u) ^ 2 =
      t ^ 2 + t * u + u ^ 2 := by
  decide

theorem Q_tailLin {A : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hA : A.det ≠ 0) (x : X) :
    Q (tailLin A x) = Q x := by
  rw [Matrix.det_fin_two] at hA
  have h := tail_norm_invariant (A 0 0) (A 0 1) (A 1 0) (A 1 1) (x 4) (x 5) hA
  have e : Q (tailLin A x) = x 0 * x 2 + x 1 * x 3 +
      ((A 0 0 * x 4 + A 0 1 * x 5) ^ 2 + (A 0 0 * x 4 + A 0 1 * x 5) * (A 1 0 * x 4 + A 1 1 * x 5)
        + (A 1 0 * x 4 + A 1 1 * x 5) ^ 2) := by
    rw [Q_apply, tailLin_apply]
    simp only [Matrix.cons_val]
    ring
  rw [e, h, Q_apply]
  ring

theorem det_ne_zero_of_GL (A : GL (Fin 2) (ZMod 2)) :
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).det ≠ 0 :=
  (Matrix.isUnit_det_of_invertible _).ne_zero

@[expose] def tailIso (A : GL (Fin 2) (ZMod 2)) : QuadraticMap.IsometryEquiv Q Q :=
  ⟨tailMap A, fun x => Q_tailLin (det_ne_zero_of_GL A) x⟩

theorem tailIso_apply (A : GL (Fin 2) (ZMod 2)) (x : X) : tailIso A x = tailLin A x := rfl

end CFSG.LieType.Chevalley.C2E6Overlap
