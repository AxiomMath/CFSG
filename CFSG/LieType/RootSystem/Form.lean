module

public import CFSG.LieType.RootSystem.Positivity
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.LieType.RootSystem

open Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

def toRat : (I → ℤ) →+ (I → ℚ) := (Int.castAddHom ℚ).compLeft I

omit [Fintype I] [DecidableEq I] in
@[simp] theorem toRat_apply (v : I → ℤ) (k : I) : toRat v k = (v k : ℚ) := (rfl)

omit [Fintype I] [DecidableEq I] in
theorem toRat_injective : Function.Injective (toRat : (I → ℤ) → (I → ℚ)) :=
  fun _ _ h => funext fun k => Int.cast_injective (congrFun h k)

omit [Fintype I] in
theorem toRat_single (i : I) : toRat (Pi.single i 1) = Pi.single i (1 : ℚ) := by
  ext k
  simp [Pi.single_apply]

variable {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

noncomputable def symmetrizer : I → ℚ := hA.exists_symmetrizer.choose

omit [DecidableEq I] in
theorem symmetrizer_pos (i : I) : 0 < symmetrizer hA i :=
  hA.exists_symmetrizer.choose_spec.1 i

noncomputable def symmetrized : Matrix I I ℚ :=
  Matrix.of fun i j ↦ symmetrizer hA i * (A i j : ℚ)

omit [DecidableEq I] in
theorem posDef_symmetrized : (symmetrized hA).PosDef :=
  hA.exists_symmetrizer.choose_spec.2

noncomputable def form : LinearMap.BilinForm ℚ (I → ℚ) := Matrix.toBilin' (symmetrized hA)

theorem form_apply (x y : I → ℚ) : form hA x y = x ⬝ᵥ (symmetrized hA *ᵥ y) :=
  Matrix.toBilin'_apply' _ _ _

theorem form_comm (x y : I → ℚ) : form hA x y = form hA y x := by
  rw [form_apply, form_apply, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    ← Matrix.conjTranspose_eq_transpose_of_trivial, (posDef_symmetrized hA).isHermitian.eq,
    dotProduct_comm]

theorem form_single_left (m : I) (y : I → ℚ) :
    form hA (Pi.single m 1) y = symmetrizer hA m * ∑ l, (A m l : ℚ) * y l := by
  rw [form_apply, single_dotProduct, one_mul]
  simp [Matrix.mulVec, dotProduct, symmetrized, Finset.mul_sum, mul_assoc]

theorem form_single_right (x : I → ℚ) (m : I) :
    form hA x (Pi.single m 1) = symmetrizer hA m * ∑ k, (A m k : ℚ) * x k := by
  rw [form_comm, form_single_left]

theorem form_single_single (i : I) :
    form hA (Pi.single i 1) (Pi.single i 1) = 2 * symmetrizer hA i := by
  rw [form_single_left]
  simp [Pi.single_apply, hA.apply_self, mul_comm]

theorem form_pos {x : I → ℚ} (hx : x ≠ 0) : 0 < form hA x x := by
  have := (posDef_symmetrized hA).dotProduct_mulVec_pos hx
  rwa [star_trivial, ← form_apply] at this

theorem form_self_nonneg (x : I → ℚ) : 0 ≤ form hA x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (form_pos hA hx).le

theorem form_eq_sum (x v : I → ℚ) : form hA x v = ∑ l, v l * form hA x (Pi.single l 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show Pi.single l (v l) = v l • Pi.single l (1 : ℚ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

omit hA in
theorem toRat_reflection (m : I) (v : I → ℤ) :
    toRat (reflection A m v) = toRat v - ((coroot A m v : ℤ) : ℚ) • Pi.single m 1 := by
  rw [reflection_apply_coroot, map_sub, map_zsmul, toRat_single, ← Int.cast_smul_eq_zsmul ℚ]

theorem form_reflection (m : I) (u v : I → ℤ) :
    form hA (toRat (reflection A m u)) (toRat (reflection A m v)) =
      form hA (toRat u) (toRat v) := by
  rw [toRat_reflection, toRat_reflection]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    form_single_left, form_single_right, coroot_apply, toRat_apply, Pi.single_apply]
  simp [Finset.sum_ite_eq']
  rw [hA.apply_self]
  push_cast
  ring

theorem form_weylAction (w : (coxeterMatrix hA).Group) (u v : I → ℤ) :
    form hA (toRat (weylAction hA w u)) (toRat (weylAction hA w v)) =
      form hA (toRat u) (toRat v) := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left generalizing u v with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple, form_reflection, ih]

theorem sq_form_le (x y : I → ℚ) : form hA x y ^ 2 ≤ form hA x x * form hA y y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hyy := form_pos hA hy
  set t := form hA x y / form hA y y
  have h := form_self_nonneg hA (x - t • y)
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [form_comm hA y x] at h
  have ht : t * form hA y y = form hA x y := div_mul_cancel₀ _ hyy.ne'
  have h' : t * form hA x y * form hA y y = form hA x y ^ 2 := by
    rw [mul_right_comm, ht]
    ring
  nlinarith

theorem form_mulVec_inv_single (x : I → ℚ) (k : I) :
    form hA x ((symmetrized hA)⁻¹ *ᵥ Pi.single k 1) = x k := by
  have hdet : IsUnit (symmetrized hA).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (posDef_symmetrized hA).isUnit
  rw [form_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec,
    dotProduct_single, mul_one]

theorem finite_setOf_form_le (C : ℚ) :
    {v : I → ℤ | form hA (toRat v) (toRat v) ≤ C}.Finite := by
  set N : I → ℤ := fun k =>
    ⌈C * form hA ((symmetrized hA)⁻¹ *ᵥ Pi.single k 1) ((symmetrized hA)⁻¹ *ᵥ Pi.single k 1)⌉
  refine (Set.Finite.pi (t := fun k => Set.Icc (-N k) (N k))
    fun k => Set.finite_Icc _ _).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro k
  set y := (symmetrized hA)⁻¹ *ᵥ Pi.single k 1
  have hcs := sq_form_le hA (toRat v) y
  rw [form_mulVec_inv_single, toRat_apply] at hcs
  have hyy := form_self_nonneg hA y
  have hle : ((v k : ℤ) : ℚ) ^ 2 ≤ C * form hA y y := by nlinarith
  have hN : C * form hA y y ≤ (N k : ℚ) := Int.le_ceil _
  have h1 : ((v k : ℤ) : ℚ) ≤ ((v k : ℤ) : ℚ) ^ 2 := by exact_mod_cast Int.le_self_sq (v k)
  have h2 : (-(v k : ℤ) : ℚ) ≤ ((v k : ℤ) : ℚ) ^ 2 := by
    have h := Int.le_self_sq (-(v k))
    rw [neg_sq] at h
    exact_mod_cast h
  constructor
  · have : (-(N k : ℤ) : ℚ) ≤ (v k : ℚ) := by linarith
    exact_mod_cast this
  · have : (v k : ℚ) ≤ (N k : ℚ) := by linarith
    exact_mod_cast this

theorem form_le_of_mem_roots (D : Set I) {γ : I → ℤ} (hγ : γ ∈ roots hA D) :
    form hA (toRat γ) (toRat γ) ≤ 8 * ∑ k, symmetrizer hA k := by
  have hsum : ∀ i, symmetrizer hA i ≤ ∑ k, symmetrizer hA k := fun i =>
    Finset.single_le_sum (fun k _ => (symmetrizer_pos hA k).le) (Finset.mem_univ i)
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, -, rfl⟩
  · rw [form_weylAction, toRat_single, form_single_single]
    linarith [symmetrizer_pos hA i, hsum i]
  · simp only [two_nsmul, map_add, LinearMap.add_apply, form_weylAction, toRat_single,
      form_single_single]
    linarith [symmetrizer_pos hA i, hsum i]

theorem finite_roots (D : Set I) : (roots hA D).Finite :=
  (finite_setOf_form_le hA _).subset fun _ hγ => form_le_of_mem_roots hA D hγ

theorem finite_group : Finite (coxeterMatrix hA).Group := by
  have := (finite_roots hA ∅).to_subtype
  refine Finite.of_injective (fun w (i : I) =>
    (⟨weylAction hA w (Pi.single i 1), Or.inl ⟨w, i, rfl⟩⟩ : roots hA ∅)) fun w w' h => ?_
  refine weylAction_injective hA (LinearMap.pi_ext fun i x => ?_)
  have hi := congrArg Subtype.val (congrFun h i)
  rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul]
  exact congrArg (x • ·) hi

end CFSG.LieType.RootSystem
