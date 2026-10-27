module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888YPl
import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X]

structure PlaneSys (V : Subgroup X) (W : Fin 4 → Subgroup X) : Prop extends IsPlanes V W where
  perm : ∀ y ∈ normalizer (V : Set X), ∀ i, ∃ j, ∀ w ∈ W i, y * w * y⁻¹ ∈ W j

variable {V : Subgroup X} {W : Fin 4 → Subgroup X}

theorem PlaneSys.eq_of_prod_eq (hS : PlaneSys V W) {w w' : Fin 4 → X} (hw : ∀ i, w i ∈ W i)
    (hw' : ∀ i, w' i ∈ W i) (h : w 0 * w 1 * w 2 * w 3 = w' 0 * w' 1 * w' 2 * w' 3) :
    w = w' := by
  let Φ : (∀ i, ↥(W i)) → ↥V := fun u =>
    ⟨(u 0 : X) * (u 1 : X) * (u 2 : X) * (u 3 : X),
      V.mul_mem (V.mul_mem (V.mul_mem (hS.le 0 (u 0).2) (hS.le 1 (u 1).2))
        (hS.le 2 (u 2).2)) (hS.le 3 (u 3).2)⟩
  have hsurj : Function.Surjective Φ := by
    rintro ⟨v, hv⟩
    obtain ⟨u, hu, hvu⟩ := hS.decomp v hv
    exact ⟨fun i => ⟨u i, hu i⟩, by
      apply Subtype.ext
      exact hvu.symm⟩
  have hcard : Nat.card (∀ i : Fin 4, ↥(W i)) = 2 ^ 8 := by
    calc Nat.card (∀ i : Fin 4, ↥(W i))
        = ∏ i : Fin 4, Nat.card (↥(W i)) := Nat.card_pi
      _ = ∏ _i : Fin 4, (4 : ℕ) := by
            apply Finset.prod_congr rfl
            intro i _
            exact hS.card i
      _ = 4 ^ 4 := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = 2 ^ 8 := by decide
  haveI : Finite (∀ i : Fin 4, ↥(W i)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  have hbij : Function.Bijective Φ :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, hS.card_D])
  have hfun : (fun i => (⟨w i, hw i⟩ : ↥(W i))) =
      (fun i => (⟨w' i, hw' i⟩ : ↥(W i))) := by
    apply hbij.1
    apply Subtype.ext
    exact h
  funext i
  exact congrArg (fun f : ∀ i, ↥(W i) => (f i : X)) hfun

private theorem s888_conj_inv (y w : X) :
    (y : X)⁻¹ * (y * w * y⁻¹) * y = w := by
  calc y⁻¹ * (y * w * y⁻¹) * y
      = y⁻¹ * ((y * w * y⁻¹) * y) := mul_assoc _ _ _
    _ = y⁻¹ * ((y * w) * (y⁻¹ * y)) := by rw [mul_assoc (y * w) y⁻¹ y]
    _ = y⁻¹ * ((y * w) * 1) := by rw [inv_mul_cancel]
    _ = y⁻¹ * (y * w) := by rw [mul_one]
    _ = (y⁻¹ * y) * w := (mul_assoc y⁻¹ y w).symm
    _ = 1 * w := by rw [inv_mul_cancel]
    _ = w := one_mul w

theorem PlaneSys.inf_eq_bot (hS : PlaneSys V W) {i j : Fin 4} (h : i ≠ j) : W i ⊓ W j = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxi, hxj⟩ := hx
  have hx2 : x * x = 1 := hS.sq x (hS.le i hxi)
  have key : (fun k : Fin 4 => if k = i then x else if k = j then x else 1) = fun _ => 1 := by
    apply hS.eq_of_prod_eq
    · intro k
      by_cases hki : k = i
      · subst hki
        rw [if_pos rfl]
        exact hxi
      · by_cases hkj : k = j
        · subst hkj
          rw [if_neg hki, if_pos rfl]
          exact hxj
        · rw [if_neg hki, if_neg hkj]
          exact Subgroup.one_mem _
    · intro k
      exact Subgroup.one_mem _
    · fin_cases i <;> fin_cases j <;> simp_all [hx2]
  have := congrFun key i
  simpa using this

private noncomputable def planeIdx (hS : PlaneSys V W) (y : normalizer (V : Set X)) (i : Fin 4) :
    Fin 4 :=
  Classical.choose (hS.perm (y : X) y.2 i)

private theorem planeIdx_spec (hS : PlaneSys V W) (y : normalizer (V : Set X)) (i : Fin 4) :
    ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W (planeIdx hS y i) :=
  Classical.choose_spec (hS.perm (y : X) y.2 i)

private theorem planeIdx_unique (hS : PlaneSys V W) {i j j' : Fin 4} {y : X}
    (hy : y ∈ normalizer (V : Set X))
    (h : ∀ w ∈ W i, y * w * y⁻¹ ∈ W j)
    (h' : ∀ w ∈ W i, y * w * y⁻¹ ∈ W j') : j = j' := by
  by_contra hne
  have hbot := hS.inf_eq_bot (i := j) (j := j') hne
  rcases Subgroup.bot_or_exists_ne_one (W i) with hWi | ⟨w, hw, hwne⟩
  · have h1 : (4 : ℕ) = 1 := by rw [← hS.card i, hWi, Subgroup.card_bot]
    exact absurd h1 (by decide)
  · have hmem : y * w * y⁻¹ ∈ W j ⊓ W j' := ⟨h w hw, h' w hw⟩
    rw [hbot] at hmem
    have h1 : y * w * y⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have h1y : y * w = y * 1 := by
      have := congrArg (fun t => t * y) h1
      simpa [mul_assoc] using this
    exact hwne (mul_left_cancel h1y)

private theorem planeIdx_eq_of_mem (hS : PlaneSys V W) (y : normalizer (V : Set X))
    {i j : Fin 4} (h : ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W j) :
    planeIdx hS y i = j :=
  planeIdx_unique hS y.2 (planeIdx_spec hS y i) h

private theorem planeIdx_mul (hS : PlaneSys V W) (y y' : normalizer (V : Set X))
    (i : Fin 4) :
    planeIdx hS (y * y') i = planeIdx hS y (planeIdx hS y' i) := by
  apply planeIdx_eq_of_mem
  intro w hw
  have hspec := planeIdx_spec hS y (planeIdx hS y' i)
    ((y' : X) * w * (y' : X)⁻¹) (planeIdx_spec hS y' i w hw)
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using hspec

private theorem planeIdx_one (hS : PlaneSys V W) (i : Fin 4) : planeIdx hS 1 i = i := by
  apply planeIdx_eq_of_mem
  intro w hw
  simpa using hw

private theorem planeIdx_bijective (hS : PlaneSys V W) (y : normalizer (V : Set X)) :
    Function.Bijective (planeIdx hS y) := by
  refine ⟨?_, ?_⟩
  · intro i i' hii
    have h1 : planeIdx hS y⁻¹ (planeIdx hS y i) =
        planeIdx hS y⁻¹ (planeIdx hS y i') := congrArg (planeIdx hS y⁻¹) hii
    rw [← planeIdx_mul hS y⁻¹ y i, inv_mul_cancel, planeIdx_one,
      ← planeIdx_mul hS y⁻¹ y i', inv_mul_cancel, planeIdx_one] at h1
    exact h1
  · intro i
    exact ⟨planeIdx hS y⁻¹ i, by
      rw [← planeIdx_mul hS y y⁻¹ i, mul_inv_cancel, planeIdx_one]⟩

theorem PlaneSys.exists_planeHom (hS : PlaneSys V W) :
    ∃ φ : normalizer (V : Set X) →* Equiv.Perm (Fin 4),
      ∀ (y : normalizer (V : Set X)) (i : Fin 4), ∀ w ∈ W i,
        (y : X) * w * (y : X)⁻¹ ∈ W (φ y i) := by
  refine ⟨MonoidHom.mk' (fun y => Equiv.ofBijective (planeIdx hS y)
    (planeIdx_bijective hS y)) ?_, ?_⟩
  · intro y y'
    apply Equiv.ext
    intro i
    simp only [Equiv.Perm.mul_apply, Equiv.coe_ofBijective]
    exact planeIdx_mul hS y y' i
  · intro y i w hw
    simpa using planeIdx_spec hS y i w hw

noncomputable def planeHom (hS : PlaneSys V W) : normalizer (V : Set X) →* Equiv.Perm (Fin 4) :=
  Classical.choose hS.exists_planeHom

theorem planeHom_spec (hS : PlaneSys V W) (y : normalizer (V : Set X)) (i : Fin 4) :
    ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W (planeHom hS y i) :=
  Classical.choose_spec hS.exists_planeHom y i

theorem planeHom_eq_of_mem (hS : PlaneSys V W) (y : normalizer (V : Set X)) {i j : Fin 4}
    (h : ∀ w ∈ W i, (y : X) * w * (y : X)⁻¹ ∈ W j) : planeHom hS y i = j :=
  planeIdx_unique hS y.2 (planeHom_spec hS y i) h

theorem mem_plane_conj_iff (hS : PlaneSys V W) (y : normalizer (V : Set X)) {i : Fin 4}
    (hi : planeHom hS y i = i) (w : X) : (y : X) * w * (y : X)⁻¹ ∈ W i ↔ w ∈ W i := by
  constructor
  · intro hw
    have h1 : (planeHom hS y)⁻¹ i = i := by
      calc (planeHom hS y)⁻¹ i
          = (planeHom hS y)⁻¹ ((planeHom hS y) i) := by rw [hi]
        _ = i := Equiv.symm_apply_apply _ _
    have hmem := planeHom_spec hS y⁻¹ i ((y : X) * w * (y : X)⁻¹) hw
    have hmem' : (y : X)⁻¹ * ((y : X) * w * (y : X)⁻¹) * ((y : X)⁻¹)⁻¹ ∈ W i := by
      simpa [h1] using hmem
    simpa [s888_conj_inv] using hmem'
  · intro hw
    have := planeHom_spec hS y i w hw
    rwa [hi] at this

theorem centralizes_V_iff (hS : PlaneSys V W) (y : normalizer (V : Set X)) :
    (∀ v ∈ V, (y : X) * v = v * (y : X)) ↔ ∀ i, ∀ w ∈ W i, (y : X) * w = w * (y : X) := by
  constructor
  · intro h i w hw
    exact h w (hS.le i hw)
  · intro h v hv
    obtain ⟨w, hw, hv'⟩ := hS.decomp v hv
    rw [hv']
    have h0 : Commute (y : X) (w 0) := h 0 (w 0) (hw 0)
    have h1 : Commute (y : X) (w 1) := h 1 (w 1) (hw 1)
    have h2 : Commute (y : X) (w 2) := h 2 (w 2) (hw 2)
    have h3 : Commute (y : X) (w 3) := h 3 (w 3) (hw 3)
    exact ((h0.mul_right h1).mul_right h2).mul_right h3

end CFSG.OddStandard.SmallF3.Omega
