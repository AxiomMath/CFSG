module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.CGT6

section PermSet

variable {V : Type} [CommGroup V] {k : ℕ} {w : Fin k → V}

@[expose] def permSet (hw : Function.Injective w) : Subgroup (MulAut V) where
  carrier := {x | ∀ i, ∃ j, x (w i) = w j}
  one_mem' := fun i => ⟨i, rfl⟩
  mul_mem' := fun {x y} hx hy i => by
    obtain ⟨j, hj⟩ := hy i
    obtain ⟨l, hl⟩ := hx j
    exact ⟨l, by rw [MulAut.mul_apply, hj, hl]⟩
  inv_mem' := fun {x} hx j => by
    choose f hf using hx
    have hinj : Function.Injective f := fun i i' h => by
      apply hw
      apply x.injective
      rw [hf i, hf i', h]
    obtain ⟨i, rfl⟩ := Finite.injective_iff_surjective.mp hinj j
    exact ⟨i, by rw [← hf i]; simp⟩

variable (hw : Function.Injective w)

noncomputable def permIdx (x : ↥(permSet hw)) (i : Fin k) : Fin k :=
  Classical.choose (x.2 i)

theorem permIdx_spec (x : ↥(permSet hw)) (i : Fin k) :
    (x : MulAut V) (w i) = w (permIdx hw x i) :=
  Classical.choose_spec (x.2 i)

theorem permIdx_unique (x : ↥(permSet hw)) {i j : Fin k} (h : (x : MulAut V) (w i) = w j) :
    permIdx hw x i = j :=
  hw ((permIdx_spec hw x i).symm.trans h)

theorem permIdx_injective (x : ↥(permSet hw)) : Function.Injective (permIdx hw x) := by
  intro i i' h
  apply hw
  apply (x : MulAut V).injective
  rw [permIdx_spec hw x i, permIdx_spec hw x i', h]

noncomputable def permOfAut (x : ↥(permSet hw)) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective (permIdx hw x)
    ⟨permIdx_injective hw x, Finite.injective_iff_surjective.mp (permIdx_injective hw x)⟩

noncomputable def permSetHom : ↥(permSet hw) →* Equiv.Perm (Fin k) where
  toFun := permOfAut hw
  map_one' := Equiv.ext fun i => permIdx_unique hw 1 rfl
  map_mul' x y := Equiv.ext fun i => by
    refine permIdx_unique hw (x * y) ?_
    show (x : MulAut V) ((y : MulAut V) (w i)) = _
    rw [permIdx_spec hw y i, permIdx_spec hw x (permIdx hw y i)]
    rfl

theorem permSetHom_spec (x : ↥(permSet hw)) (i : Fin k) :
    (x : MulAut V) (w i) = w (permSetHom hw x i) :=
  permIdx_spec hw x i

theorem permSetHom_apply_eq_iff (x : ↥(permSet hw)) {i j : Fin k} :
    permSetHom hw x i = j ↔ (x : MulAut V) (w i) = w j := by
  constructor
  · rintro rfl
    exact permSetHom_spec hw x i
  · intro h
    exact permIdx_unique hw x h

theorem eq_one_of_fix (hspan : Subgroup.closure (Set.range w) = ⊤) {x : MulAut V}
    (h : ∀ i, x (w i) = w i) : x = 1 := by
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ Subgroup.closure (Set.range w) := hspan ▸ Subgroup.mem_top v
  induction hv using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    exact h i
  | one => simp
  | mul a b _ _ ha hb =>
    rw [map_mul, ha, hb]
    rfl
  | inv a _ ha =>
    rw [map_inv, ha]
    rfl

theorem permSetHom_injective (hspan : Subgroup.closure (Set.range w) = ⊤) :
    Function.Injective (permSetHom hw) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  apply eq_one_of_fix hspan
  intro i
  rw [permSetHom_spec hw x i, hx]
  rfl

end PermSet

end CFSG.CGT.PushingUpLit.CGT6
