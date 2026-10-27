module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannOrigData

public section

namespace CFSG.QuasithinUnique.Setup.Lift.Piece

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Lift
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

section Dict

variable {G : Type} [Group G] {V : Subgroup G} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
  (θ : ↥V ≃* Multiplicative W)

theorem modComm_le' (V : Subgroup G) (A : Subgroup (MulAut V)) : modComm V A ≤ V := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, -, v, rfl⟩
  exact V.mul_mem (a v).2 (V.inv_mem v.2)

omit [Module (ZMod 2) W] in
theorem vecOf_mul' (u v : ↥V) : vecOf θ (u * v) = vecOf θ u + vecOf θ v := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_inv' (u : ↥V) : vecOf θ u⁻¹ = - vecOf θ u := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_one' : vecOf θ (1 : ↥V) = 0 := by
  simp [vecOf]

omit [Module (ZMod 2) W] in
theorem vecOf_injective' : Function.Injective (vecOf θ) := by
  intro u v h
  exact θ.injective (Multiplicative.toAdd.injective h)

theorem binPsi_vecOf' (φ : MulAut V) (v : ↥V) : binPsi θ φ (vecOf θ v) = vecOf θ (φ v) := by
  simp [binPsi_apply, vecOf]

theorem binPsi_sub_vecOf' (φ : MulAut V) (v : ↥V) :
    binPsi θ φ (vecOf θ v) - vecOf θ v = vecOf θ (φ v * v⁻¹) := by
  rw [binPsi_vecOf', vecOf_mul', vecOf_inv', sub_eq_add_neg]

theorem mem_modComm_imp' (A : Subgroup (MulAut V)) {g : G} (hg : g ∈ modComm V A) :
    ∃ hgV : g ∈ V, vecOf θ ⟨g, hgV⟩ ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤ := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, v, rfl⟩ := hx
    refine ⟨V.mul_mem (a v).2 (V.inv_mem v.2), ?_⟩
    have h1 : (⟨((a v : V) : G) * (v : G)⁻¹, V.mul_mem (a v).2 (V.inv_mem v.2)⟩ : ↥V) =
        a v * v⁻¹ := rfl
    rw [h1, ← binPsi_sub_vecOf' θ a v]
    exact mem_commSub_of (b := binPsi θ a)
      (Subgroup.mem_map.2 ⟨a, ha, rfl⟩ : binPsi θ a ∈ A.map (binPsi θ).toMonoidHom)
      Submodule.mem_top
  | one =>
    refine ⟨V.one_mem, ?_⟩
    have : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
    rw [this, vecOf_one']
    exact Submodule.zero_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨hxV, hx⟩ := hx
    obtain ⟨hyV, hy⟩ := hy
    refine ⟨V.mul_mem hxV hyV, ?_⟩
    have : (⟨x * y, V.mul_mem hxV hyV⟩ : ↥V) = ⟨x, hxV⟩ * ⟨y, hyV⟩ := rfl
    rw [this, vecOf_mul']
    exact Submodule.add_mem _ hx hy
  | inv x _ hx =>
    obtain ⟨hxV, hx⟩ := hx
    refine ⟨V.inv_mem hxV, ?_⟩
    have : (⟨x⁻¹, V.inv_mem hxV⟩ : ↥V) = ⟨x, hxV⟩⁻¹ := rfl
    rw [this, vecOf_inv']
    exact Submodule.neg_mem _ hx

theorem elOf_mem_modComm' (A : Subgroup (MulAut V)) {w : W}
    (hw : w ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤) :
    ((elOf θ w : ↥V) : G) ∈ modComm V A := by
  refine elOf_mem_of_span θ (modComm V A) ?_ hw
  rintro _ ⟨b, hb, u, -, rfl⟩
  obtain ⟨a, ha, rfl⟩ := hb
  have h1 : elOf θ ((MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((binPsi θ).toMonoidHom a) u - u) =
      a (elOf θ u) * (elOf θ u)⁻¹ := by
    have h3 := binPsi_sub_vecOf' θ a (elOf θ u)
    rw [vecOf_elOf] at h3
    have h4 : (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ((binPsi θ).toMonoidHom a) u - u =
        binPsi θ a u - u := rfl
    rw [h4, h3, elOf_vecOf]
  rw [h1]
  exact Subgroup.subset_closure ⟨a, ha, elOf θ u, rfl⟩

theorem mem_modComm_iff' (A : Subgroup (MulAut V)) (u : ↥V) :
    (u : G) ∈ modComm V A ↔ vecOf θ u ∈ commGL (A.map (binPsi θ).toMonoidHom) ⊤ := by
  constructor
  · intro h
    obtain ⟨hV, hv⟩ := mem_modComm_imp' θ A h
    exact hv
  · intro h
    have := elOf_mem_modComm' θ A h
    rwa [elOf_vecOf] at this

@[expose] def modCommEquiv' (A : Subgroup (MulAut V)) :
    ↥(modComm V A) ≃* Multiplicative ↥(commGL (A.map (binPsi θ).toMonoidHom) ⊤) where
  toFun u := Multiplicative.ofAdd
    ⟨vecOf θ ⟨u.1, modComm_le' V A u.2⟩, (mem_modComm_iff' θ A _).1 u.2⟩
  invFun w := ⟨((elOf θ (Multiplicative.toAdd w).1 : ↥V) : G),
    elOf_mem_modComm' θ A (Multiplicative.toAdd w).2⟩
  left_inv u := by
    apply Subtype.ext
    show ((elOf θ (vecOf θ ⟨u.1, modComm_le' V A u.2⟩) : ↥V) : G) = u.1
    rw [elOf_vecOf]
  right_inv w := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show vecOf θ ⟨((elOf θ (Multiplicative.toAdd w).1 : ↥V) : G), _⟩ = (Multiplicative.toAdd w).1
    exact vecOf_elOf θ _
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    show vecOf θ ⟨u.1 * v.1, _⟩ = vecOf θ ⟨u.1, _⟩ + vecOf θ ⟨v.1, _⟩
    exact vecOf_mul' θ ⟨u.1, _⟩ ⟨v.1, _⟩

end Dict

end CFSG.QuasithinUnique.Setup.Lift.Piece
