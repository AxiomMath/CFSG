module

public import CFSG.Fischer.Classification.PartIII.Arf.Vec

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open QuadraticMap F3

namespace Arf

@[expose] def q6 (x : Fin 6 → ZMod 2) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 4 + x 4 * x 5 + x 5 * x 5

@[expose] def b6 (x y : Fin 6 → ZMod 2) : ZMod 2 :=
  x 0 * y 1 + x 1 * y 0 + x 2 * y 3 + x 3 * y 2 + x 4 * y 5 + x 5 * y 4

@[expose] def t6 (u v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun k => v k + b6 v u * u k

@[expose] def f5 (x y : Fin 5 → ZMod 3) : ZMod 3 :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 - x 4 * y 4

@[expose] def r5 (w v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  fun k => v k + f5 v w * w k

@[expose] def vecA : Fin 36 → Fin 6 → ZMod 2 :=
  ![![1, 1, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0], ![1, 1, 0, 1, 0, 0], ![0, 0, 1, 1, 0, 0],
    ![1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 1, 0], ![0, 0, 1, 0, 1, 0], ![1, 0, 1, 0, 1, 0], ![0, 1, 1, 0, 1, 0],
    ![0, 0, 0, 1, 1, 0], ![1, 0, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 0], ![1, 1, 1, 1, 1, 0],
    ![0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1],
    ![1, 0, 1, 0, 0, 1], ![0, 1, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 1], ![1, 0, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1], ![1, 1, 1, 1, 0, 1], ![0, 0, 0, 0, 1, 1], ![1, 0, 0, 0, 1, 1],
    ![0, 1, 0, 0, 1, 1], ![0, 0, 1, 0, 1, 1], ![1, 0, 1, 0, 1, 1], ![0, 1, 1, 0, 1, 1],
    ![0, 0, 0, 1, 1, 1], ![1, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 1], ![1, 1, 1, 1, 1, 1]]

@[expose] def vecB : Fin 36 → Fin 5 → ZMod 3 :=
  ![![1, 2, 0, 0, 2], ![1, 1, 1, 2, 0], ![0, 1, 1, 0, 1], ![1, 0, 0, 2, 2], ![1, 2, 1, 1, 0],
    ![0, 0, 1, 1, 1], ![0, 1, 0, 1, 1], ![0, 0, 1, 2, 2], ![1, 2, 2, 1, 0], ![0, 1, 2, 0, 1],
    ![1, 0, 0, 0, 0], ![1, 1, 0, 0, 1], ![1, 1, 2, 2, 0], ![1, 0, 0, 1, 1], ![0, 1, 0, 1, 2],
    ![0, 0, 1, 0, 0], ![1, 1, 2, 1, 0], ![1, 0, 0, 2, 1], ![0, 1, 0, 2, 2], ![1, 2, 0, 0, 1],
    ![1, 0, 1, 0, 1], ![0, 1, 1, 0, 2], ![0, 1, 0, 2, 1], ![0, 0, 1, 1, 2], ![1, 2, 2, 2, 0],
    ![1, 0, 1, 0, 2], ![1, 0, 2, 0, 2], ![1, 1, 0, 0, 2], ![0, 1, 0, 0, 0], ![1, 0, 0, 1, 2],
    ![1, 2, 1, 2, 0], ![0, 0, 1, 2, 1], ![0, 0, 0, 1, 0], ![0, 1, 2, 0, 2], ![1, 0, 2, 0, 1],
    ![1, 1, 1, 1, 0]]

@[expose] def tableA : List (Fin 36) :=
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 3, 4, 5, 0, 6, 7, 8, 0, 9, 10, 11, 0, 12, 13, 14, 0, 0, 0,
    0, 15, 16, 17, 18, 0, 19, 20, 21, 0, 22, 23, 24, 0, 0, 0, 0, 25, 26, 27, 28, 0, 29, 30, 31, 0,
    32, 33, 34, 0, 0, 0, 0, 35]

@[expose] def tableB : List (Fin 36) :=
  [0, 10, 10, 28, 0, 0, 28, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 24, 0, 4, 12, 0, 0, 0, 0, 16, 30, 0, 8, 1, 32, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 30, 16, 0, 0, 0, 0, 12, 4, 0, 24, 35, 0, 0, 0, 0, 11, 0,
    0, 19, 27, 0, 20, 26, 2, 0, 0, 33, 0, 0, 0, 34, 25, 9, 0, 0, 21, 0, 0, 0, 13, 3, 6, 0, 0, 18,
    0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 29, 22, 0, 0, 14, 0, 0, 31,
    0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27, 19, 0, 0, 11, 0, 25, 34,
    21, 0, 0, 9, 0, 0, 0, 26, 20, 33, 0, 0, 2, 0, 0, 0, 29, 17, 14, 0, 0, 22, 0, 0, 23, 0, 0, 0,
    0, 0, 0, 0, 0, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 13, 18, 0, 0, 6, 0, 0, 7, 0, 0, 0, 0, 0, 0,
    0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def encA (v : Fin 6 → ZMod 2) : ℕ :=
  (v 0).val + 2 * ((v 1).val + 2 * ((v 2).val + 2 * ((v 3).val + 2 * ((v 4).val +
    2 * (v 5).val))))

@[expose] def encB (v : Fin 5 → ZMod 3) : ℕ :=
  (v 0).val + 3 * ((v 1).val + 3 * ((v 2).val + 3 * ((v 3).val + 3 * (v 4).val)))

@[expose] def idxA (v : Fin 6 → ZMod 2) : Fin 36 :=
  tableA.getD (encA v) 0

@[expose] def idxB (u : Fin 5 → ZMod 3) : Fin 36 :=
  tableB.getD (encB u) 0

@[expose] def gamma (v : Fin 6 → ZMod 2) : Fin 5 → ZMod 3 :=
  vecB (idxA v)

theorem q6_vecA : ∀ i, q6 (vecA i) = 1 := by
  decide +kernel

theorem vecA_idxA : ∀ v, q6 v = 1 → vecA (idxA v) = v := by
  decide +kernel

theorem idxA_vecA : ∀ i, idxA (vecA i) = i := by
  decide +kernel

theorem f5_vecB : ∀ i, f5 (vecB i) (vecB i) = 1 := by
  decide +kernel

theorem idxB_vecB : ∀ i, idxB (vecB i) = i ∧ idxB (-vecB i) = i := by
  decide +kernel

theorem vecB_idxB : ∀ u, f5 u u = 1 → vecB (idxB u) = u ∨ vecB (idxB u) = -u := by
  decide +kernel

theorem vecB_idxA_t6 : ∀ i j, vecB (idxA (t6 (vecA i) (vecA j))) = r5 (vecB i) (vecB j) ∨
    vecB (idxA (t6 (vecA i) (vecA j))) = -r5 (vecB i) (vecB j) := by
  decide +kernel

theorem b6_nondeg : ∀ x, b6 x ![0, 1, 0, 0, 0, 0] = 0 → b6 x ![1, 0, 0, 0, 0, 0] = 0 →
    b6 x ![0, 0, 0, 1, 0, 0] = 0 → b6 x ![0, 0, 1, 0, 0, 0] = 0 →
    b6 x ![0, 0, 0, 0, 0, 1] = 0 → b6 x ![0, 0, 0, 0, 1, 0] = 0 → x = 0 := by
  decide +kernel

theorem f5_nondeg : ∀ x, f5 x ![1, 0, 0, 0, 0] = 0 → f5 x ![0, 1, 0, 0, 0] = 0 →
    f5 x ![0, 0, 1, 0, 0] = 0 → f5 x ![0, 0, 0, 1, 0] = 0 → f5 x ![0, 0, 0, 0, 1] = 0 →
    x = 0 := by
  decide +kernel

end Arf

open Arf

noncomputable def quadMinusSix : QuadraticForm (ZMod 2) (Fin 6 → ZMod 2) :=
  proj 0 1 + proj 2 3 + proj 4 4 + proj 4 5 + proj 5 5

theorem quadMinusSix_apply (x : Fin 6 → ZMod 2) : quadMinusSix x = q6 x := by
  simp only [quadMinusSix, add_apply, proj_apply, q6]

theorem polar_quadMinusSix (x y : Fin 6 → ZMod 2) : polar quadMinusSix x y = b6 x y := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [polar, quadMinusSix_apply, q6, b6, Pi.add_apply]
  linear_combination (x 4 * y 4 + x 5 * y 5) * h2

theorem polar_quadMinusSix_nondeg :
    ∀ x, (∀ y, polar quadMinusSix x y = 0) → x = 0 := by
  intro x hx
  simp only [polar_quadMinusSix] at hx
  exact b6_nondeg x (hx _) (hx _) (hx _) (hx _) (hx _) (hx _)

@[expose] def formMinusFive : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3) :=
  LinearMap.mk₂ (ZMod 3) f5 (fun _ _ _ => by simp only [f5, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [f5, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [f5, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [f5, Pi.smul_apply, smul_eq_mul]; ring)

theorem formMinusFive_apply (x y : Fin 5 → ZMod 3) : formMinusFive x y = f5 x y :=
  rfl

theorem isF3Form_formMinusFive : IsF3Form formMinusFive where
  symm x y := by
    simp only [formMinusFive_apply, f5]
    ring
  nondeg x hx := by
    simp only [formMinusFive_apply] at hx
    exact f5_nondeg x (hx _) (hx _) (hx _) (hx _) (hx _)

theorem ncard_quadMinusSix : {v | quadMinusSix v = 1}.ncard = 36 := by
  have : {v | quadMinusSix v = 1} = Set.range vecA := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_range, quadMinusSix_apply]
    exact ⟨fun hv => ⟨_, vecA_idxA v hv⟩, by rintro ⟨i, rfl⟩; exact q6_vecA i⟩
  rw [this, Set.ncard_range_of_injective fun i j h => by rw [← idxA_vecA i, h, idxA_vecA],
    Nat.card_eq_fintype_card, Fintype.card_fin]

namespace Arf

variable {u v w : Fin 6 → ZMod 2}

theorem vecA_idxA_of {v : Fin 6 → ZMod 2} (hv : quadMinusSix v = 1) : vecA (idxA v) = v :=
  vecA_idxA v (by rwa [← quadMinusSix_apply])

theorem gamma_norm (v : Fin 6 → ZMod 2) : formMinusFive (gamma v) (gamma v) = 1 :=
  f5_vecB _

theorem gamma_injective (hv : quadMinusSix v = 1) (hw : quadMinusSix w = 1)
    (h : gamma w = gamma v ∨ gamma w = -gamma v) : w = v := by
  have hi : idxA w = idxA v := by
    rcases h with h | h
    · rw [← (idxB_vecB (idxA w)).1, ← (idxB_vecB (idxA v)).1]
      exact congrArg idxB h
    · rw [← (idxB_vecB (idxA w)).1, ← (idxB_vecB (idxA v)).2]
      exact congrArg idxB h
  rw [← vecA_idxA_of hw, hi, vecA_idxA_of hv]

theorem exists_gamma_eq {x : Fin 5 → ZMod 3} (hx : formMinusFive x x = 1) :
    ∃ v, quadMinusSix v = 1 ∧ (gamma v = x ∨ gamma v = -x) := by
  refine ⟨vecA (idxB x), by rw [quadMinusSix_apply]; exact q6_vecA _, ?_⟩
  rw [gamma, idxA_vecA]
  exact vecB_idxB x hx

theorem gamma_transvection (hu : quadMinusSix u = 1) (hv : quadMinusSix v = 1) :
    gamma (v + polar quadMinusSix v u • u) = act (refl formMinusFive (gamma u)) (gamma v) ∨
      gamma (v + polar quadMinusSix v u • u) =
        -act (refl formMinusFive (gamma u)) (gamma v) := by
  have ht : v + polar quadMinusSix v u • u = t6 (vecA (idxA u)) (vecA (idxA v)) := by
    rw [vecA_idxA_of hu, vecA_idxA_of hv]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, polar_quadMinusSix, t6]
  have hr : act (refl formMinusFive (gamma u)) (gamma v) =
      r5 (vecB (idxA u)) (vecB (idxA v)) := by
    rw [act_refl (gamma_norm u)]
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, formMinusFive_apply, r5, gamma]
  rw [ht, hr]
  exact vecB_idxA_t6 _ _

end Arf

@[expose] noncomputable def minusSixEquiv : {v // quadMinusSix v = 1} ≃ D3 formMinusFive :=
  reflEquivOfVec isF3Form_formMinusFive (by norm_num) (fun v => gamma v) (fun v => gamma_norm v)
    (fun v w h => Subtype.ext (gamma_injective v.2 w.2 h)) fun _ hx =>
      let ⟨v, hv, h⟩ := exists_gamma_eq hx
      ⟨⟨v, hv⟩, h⟩

theorem coe_minusSixEquiv (v : {v // quadMinusSix v = 1}) :
    (minusSixEquiv v : R3 formMinusFive) = reflBar formMinusFive (gamma v) :=
  rfl

theorem minusSixEquiv_transvection (u v : {v // quadMinusSix v = 1})
    (h : quadMinusSix (v + polar quadMinusSix v u • u) = 1) :
    (minusSixEquiv ⟨_, h⟩ : R3 formMinusFive) =
      minusSixEquiv u * minusSixEquiv v * minusSixEquiv u :=
  reflBar_eq_conj_of_eq_or isF3Form_formMinusFive (gamma_transvection u.2 v.2)

end CFSG.Fischer.Classification
