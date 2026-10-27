module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.FixedSpace

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

@[expose] def orthJ (W : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ u ∈ W, ∃ w ∈ W, g = eichler Q u w}

variable {Q} {W W' : Submodule K V}

theorem eichler_mem_orthJ {u w : V} (hu : u ∈ W) (hw : w ∈ W) : eichler Q u w ∈ orthJ Q W :=
  Subgroup.subset_closure ⟨u, hu, w, hw, rfl⟩

variable (Q) in
theorem orthJ_le_elementaryGroup (W : Submodule K V) : orthJ Q W ≤ elementaryGroup Q := by
  rw [orthJ, Subgroup.closure_le]
  rintro _ ⟨u, -, w, -, rfl⟩
  exact eichler_mem_elementaryGroup Q u w

theorem orthJ_mono (h : W' ≤ W) : orthJ Q W' ≤ orthJ Q W := by
  rw [orthJ, Subgroup.closure_le]
  rintro _ ⟨u, hu, w, hw, rfl⟩
  exact eichler_mem_orthJ (h hu) (h hw)

theorem conj_mem_orthJ {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgW : ∀ w ∈ W, g w ∈ W) {x : V ≃ₗ[K] V} (hx : x ∈ orthJ Q W) :
    g * x * g⁻¹ ∈ orthJ Q W := by
  have hle : orthJ Q W ≤ (orthJ Q W).comap (MulAut.conj g).toMonoidHom := by
    rw [orthJ, Subgroup.closure_le]
    rintro _ ⟨u, hu, w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      eichler_conj hg]
    exact eichler_mem_orthJ (hgW u hu) (hgW w hw)
  exact hle hx

variable (W) in
@[expose] def stabSub : Subgroup (V ≃ₗ[K] V) where
  carrier := {x | ∀ w, w ∈ W ↔ x w ∈ W}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb w => (hb w).trans (ha (b w))
  inv_mem' := fun {a} ha w => by
    have := ha (a⁻¹ w)
    rw [LinearEquiv.apply_inv_apply'] at this
    exact this.symm

theorem mem_stabSub {x : V ≃ₗ[K] V} : x ∈ stabSub W ↔ ∀ w, w ∈ W ↔ x w ∈ W := Iff.rfl

@[expose] def restrictStab (W : Submodule K V) (x : V ≃ₗ[K] V) (hx : ∀ w, w ∈ W ↔ x w ∈ W) :
    W ≃ₗ[K] W where
  toFun w := ⟨x w, (hx w).1 w.2⟩
  invFun w := ⟨x⁻¹ w, (hx (x⁻¹ w)).2 (by rw [LinearEquiv.apply_inv_apply']; exact w.2)⟩
  map_add' a b := Subtype.ext (map_add x (a : V) (b : V))
  map_smul' c a := Subtype.ext (map_smul x c (a : V))
  left_inv w := Subtype.ext (LinearEquiv.inv_apply_apply' x w)
  right_inv w := Subtype.ext (LinearEquiv.apply_inv_apply' x w)

variable (W) in
@[expose] def restrictHom : stabSub W →* (W ≃ₗ[K] W) where
  toFun x := restrictStab W x x.2
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

theorem orthJ_le_stabSub : orthJ Q W ≤ stabSub W := by
  rw [orthJ, Subgroup.closure_le]
  rintro _ ⟨u, hu, w, hw, rfl⟩ x
  obtain ⟨a, b, hab⟩ := eichler_apply_eq_add (Q := Q) u w x
  constructor
  · intro hx
    rw [hab]
    exact W.add_mem (W.add_mem hx (W.smul_mem _ hw)) (W.smul_mem _ hu)
  · intro hx
    have : x = eichler Q u w x - a • w - b • u := by rw [hab]; abel
    rw [this]
    exact W.sub_mem (W.sub_mem hx (W.smul_mem _ hw)) (W.smul_mem _ hu)

theorem apply_eq_of_mem_orthJ {x : V ≃ₗ[K] V} (hx : x ∈ orthJ Q W) {z : V}
    (hz : z ∈ perpSub Q W) : x z = z := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    exact eichler_apply_of_polar_eq_zero (hz u hu) (hz w hw)
  | one => rfl
  | mul a b _ _ iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
  | inv a _ iha =>
    apply a.injective
    rw [LinearEquiv.apply_inv_apply', iha]

@[expose] def orthJRestrict (W : Submodule K V) : orthJ Q W →* (W ≃ₗ[K] W) :=
  (restrictHom W).comp (Subgroup.inclusion (orthJ_le_stabSub (Q := Q) (W := W)))

theorem coe_orthJRestrict (x : orthJ Q W) (w : W) :
    ((orthJRestrict W x w : W) : V) = (x : V ≃ₗ[K] V) w := rfl

theorem orthJRestrict_eichler {u w : V} (hu : u ∈ W) (hw : w ∈ W) :
    orthJRestrict W ⟨eichler Q u w, eichler_mem_orthJ hu hw⟩ =
      eichler (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ := by
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have h1 : (Q.restrict W) ⟨u, hu⟩ = 0 := h.1
    have h2 : polar (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ = 0 := by rw [polar_restrict]; exact h.2
    refine LinearEquiv.ext fun z => Subtype.ext ?_
    rw [coe_orthJRestrict, eichler_apply h1 h2]
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, polar_restrict,
      restrict_apply']
    exact eichler_apply h.1 h.2 z
  · have h' : ¬((Q.restrict W) ⟨u, hu⟩ = 0 ∧ polar (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩ = 0) := by
      rw [polar_restrict]; exact h
    rw [eichler_of_not h']
    refine LinearEquiv.ext fun z => Subtype.ext ?_
    rw [coe_orthJRestrict]
    simp only [eichler_of_not h]
    rfl

theorem orthJRestrict_mem (x : orthJ Q W) : orthJRestrict W x ∈ elementaryGroup (Q.restrict W) := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    rw [orthJRestrict_eichler hu hw]
    exact eichler_mem_elementaryGroup _ _ _
  | one => exact one_mem _
  | mul a b ha hb iha ihb =>
    have := mul_mem iha ihb
    rwa [← map_mul] at this
  | inv a ha iha =>
    have := inv_mem iha
    rwa [← map_inv] at this

theorem orthJRestrict_surjective (y : elementaryGroup (Q.restrict W)) :
    ∃ x : orthJ Q W, orthJRestrict W x = y := by
  have hle : elementaryGroup (Q.restrict W) ≤ (orthJRestrict (Q := Q) W).range :=
    elementaryGroup_le_of_eichler_mem fun u' w' _ _ =>
      ⟨⟨eichler Q u' w', eichler_mem_orthJ u'.2 w'.2⟩, orthJRestrict_eichler u'.2 w'.2⟩
  exact hle y.2

theorem orthJRestrict_injective [FiniteDimensional K V] (hW : PolarNondegOn Q W) :
    Function.Injective (orthJRestrict (Q := Q) W) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ W ⊔ perpSub Q W := by rw [(isCompl_perpSub hW).sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hxa : (x : V ≃ₗ[K] V) a = a := by
    have := congrArg (fun f : W ≃ₗ[K] W => (f ⟨a, ha⟩ : V)) hx
    exact this
  rw [map_add, hxa, apply_eq_of_mem_orthJ x.2 hb]
  rfl

@[expose] noncomputable def orthJEquiv [FiniteDimensional K V] (hW : PolarNondegOn Q W) :
    orthJ Q W ≃* elementaryGroup (Q.restrict W) :=
  MulEquiv.ofBijective ((orthJRestrict (Q := Q) W).codRestrict _ orthJRestrict_mem)
    ⟨fun a b h => orthJRestrict_injective hW (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := orthJRestrict_surjective y
      exact ⟨x, Subtype.ext hx⟩⟩

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
