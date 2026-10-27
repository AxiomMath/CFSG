module

public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.BilinearForm.Properties

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Module

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

@[expose] def pairMatrixEnd : Matrix (Fin 2) (Fin 2) k →* Module.End k (W × W) where
  toFun M := (M 0 0 • LinearMap.fst k W W + M 0 1 • LinearMap.snd k W W).prod
    (M 1 0 • LinearMap.fst k W W + M 1 1 • LinearMap.snd k W W)
  map_one' := LinearMap.ext fun ⟨x, y⟩ => Prod.ext (by simp) (by simp)
  map_mul' M N := LinearMap.ext fun ⟨x, y⟩ => Prod.ext
    (by simp [Matrix.mul_apply, Fin.sum_univ_two, add_smul, mul_smul]; abel)
    (by simp [Matrix.mul_apply, Fin.sum_univ_two, add_smul, mul_smul]; abel)

@[expose] noncomputable def doubleNaturalSL2 :
    Matrix.SpecialLinearGroup (Fin 2) k →* LinearMap.GeneralLinearGroup k (W × W) :=
  (pairMatrixEnd.comp Matrix.SpecialLinearGroup.coeMonoidHom).toHomUnits

@[simp] theorem doubleNaturalSL2_apply (g : Matrix.SpecialLinearGroup (Fin 2) k) (x y : W) :
    (doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) (x, y) =
      ((g : Matrix (Fin 2) (Fin 2) k) 0 0 • x + (g : Matrix (Fin 2) (Fin 2) k) 0 1 • y,
       (g : Matrix (Fin 2) (Fin 2) k) 1 0 • x + (g : Matrix (Fin 2) (Fin 2) k) 1 1 • y) :=
  rfl

@[expose] def upperShearSL2 (t : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[expose] def lowerShearSL2 (t : k) : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; t, 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem coe_upperShearSL2 (t : k) :
    (upperShearSL2 t : Matrix (Fin 2) (Fin 2) k) = !![1, t; 0, 1] :=
  rfl

theorem coe_lowerShearSL2 (t : k) :
    (lowerShearSL2 t : Matrix (Fin 2) (Fin 2) k) = !![1, 0; t, 1] :=
  rfl

theorem doubleNaturalSL2_upperShearSL2 (t : k) (v : W × W) :
    (doubleNaturalSL2 (W := W) (upperShearSL2 t) : W × W →ₗ[k] W × W) v =
      (v.1 + t • v.2, v.2) := by
  obtain ⟨x, y⟩ := v
  simp [coe_upperShearSL2]

theorem doubleNaturalSL2_lowerShearSL2 (t : k) (v : W × W) :
    (doubleNaturalSL2 (W := W) (lowerShearSL2 t) : W × W →ₗ[k] W × W) v =
      (v.1, t • v.1 + v.2) := by
  obtain ⟨x, y⟩ := v
  simp [coe_lowerShearSL2]

@[expose] def fstInlBlock (H : Module.End k (W × W)) : Module.End k W :=
  LinearMap.fst k W W ∘ₗ H ∘ₗ LinearMap.inl k W W

@[simp] theorem fstInlBlock_apply (H : Module.End k (W × W)) (x : W) :
    fstInlBlock H x = (H (x, 0)).1 :=
  rfl

theorem fstInlBlock_one : fstInlBlock (1 : Module.End k (W × W)) = 1 :=
  rfl

theorem fstInlBlock_mul {H H' : Module.End k (W × W)} (hH' : ∀ x, (H' (x, 0)).2 = 0) :
    fstInlBlock (H * H') = fstInlBlock H * fstInlBlock H' :=
  LinearMap.ext fun x => by
    change (H (H' (x, 0))).1 = (H ((H' (x, 0)).1, 0)).1
    rw [show H' (x, 0) = ((H' (x, 0)).1, 0) from Prod.ext rfl (hH' x)]

theorem apply_eq_fstInlBlock_of_commute_shears {H : Module.End k (W × W)}
    (hu : ∀ x y, H (x + y, y) = ((H (x, y)).1 + (H (x, y)).2, (H (x, y)).2))
    (hl : ∀ x y, H (x, x + y) = ((H (x, y)).1, (H (x, y)).1 + (H (x, y)).2)) (x y : W) :
    H (x, y) = (fstInlBlock H x, fstInlBlock H y) := by
  have split : ∀ x y : W, H (x, y) = H (x, 0) + H (0, y) := fun x y => by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have h1 : ∀ y : W, (H (y, 0)).2 = 0 ∧ (H (y, 0)).1 = (H (0, y)).2 := fun y => by
    have a := hu 0 y
    rw [zero_add, split y y, Prod.ext_iff] at a
    simp only [Prod.fst_add, Prod.snd_add] at a
    exact ⟨by simpa using a.2, add_right_cancel (a.1.trans (add_comm _ _))⟩
  have h2 : ∀ x : W, (H (0, x)).1 = 0 := fun x => by
    have b := hl x 0
    rw [add_zero, split x x, Prod.ext_iff] at b
    simp only [Prod.fst_add, Prod.snd_add] at b
    simpa using b.1
  rw [split x y]
  exact Prod.ext (by simp [h2 y]) (by simp [(h1 x).1, (h1 y).2])

theorem commute_doubleNaturalSL2_of_mem_centralizer {B : LinearMap.BilinForm k (W × W)}
    (hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) k) (u v : W × W),
      B ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) u)
        ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) v) = B u v)
    {h : bilinIsometryGroup B}
    (hh : h ∈ Subgroup.centralizer
      (((doubleNaturalSL2 (k := k) (W := W)).range.subgroupOf (bilinIsometryGroup B) :
        Set (bilinIsometryGroup B))))
    (g : Matrix.SpecialLinearGroup (Fin 2) k) (v : W × W) :
    ((h : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W)
        ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) v) =
      (doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W)
        (((h : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W) v) := by
  have hc := Subgroup.mem_centralizer_iff.mp hh
    ⟨doubleNaturalSL2 g, mem_bilinIsometryGroup.mpr (hinv g)⟩
    (Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩)
  exact (congrArg (fun s : bilinIsometryGroup B =>
    ((s : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W) v) hc).symm

theorem apply_eq_fstInlBlock_of_mem_centralizer {B : LinearMap.BilinForm k (W × W)}
    (hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) k) (u v : W × W),
      B ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) u)
        ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) v) = B u v)
    {h : bilinIsometryGroup B}
    (hh : h ∈ Subgroup.centralizer
      (((doubleNaturalSL2 (k := k) (W := W)).range.subgroupOf (bilinIsometryGroup B) :
        Set (bilinIsometryGroup B))))
    (x y : W) :
    ((h : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W) (x, y) =
      (fstInlBlock ((h : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W) x,
        fstInlBlock ((h : LinearMap.GeneralLinearGroup k (W × W)) : W × W →ₗ[k] W × W) y) := by
  refine apply_eq_fstInlBlock_of_commute_shears (fun x y => ?_) (fun x y => ?_) x y
  · have e := commute_doubleNaturalSL2_of_mem_centralizer hinv hh (upperShearSL2 1) (x, y)
    rw [doubleNaturalSL2_upperShearSL2, doubleNaturalSL2_upperShearSL2] at e
    simpa using e
  · have e := commute_doubleNaturalSL2_of_mem_centralizer hinv hh (lowerShearSL2 1) (x, y)
    rw [doubleNaturalSL2_lowerShearSL2, doubleNaturalSL2_lowerShearSL2] at e
    simpa using e

theorem doubleNaturalSL2_invariant_form_pieces (hk : ringChar k ≠ 2)
    {B : LinearMap.BilinForm k (W × W)} (hBalt : B.IsAlt)
    (hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) k) (u v : W × W),
      B ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) u)
        ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) v) = B u v) :
    (∀ x x' : W, B (x, 0) (x', 0) = 0) ∧ (∀ y y' : W, B (0, y) (0, y') = 0) ∧
      ∀ x y : W, B (x, 0) (0, y) = B (y, 0) (0, x) := by
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hup : ∀ (t : k) (y y' : W),
      t * t * B (y, 0) (y', 0) + t * (B (y, 0) (0, y') + B (0, y) (y', 0)) = 0 := by
    intro t y y'
    have e := hinv (upperShearSL2 t) (0, y) (0, y')
    rw [doubleNaturalSL2_upperShearSL2, doubleNaturalSL2_upperShearSL2] at e
    simp only [zero_add] at e
    have hv : ∀ z : W, ((t • z, z) : W × W) =
        t • LinearMap.inl k W W z + LinearMap.inr k W W z := fun z => by simp
    rw [hv, hv] at e
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.inl_apply, LinearMap.inr_apply] at e
    linear_combination e
  have hlo : ∀ (t : k) (x x' : W),
      t * (B (x, 0) (0, x') + B (0, x) (x', 0)) + t * t * B (0, x) (0, x') = 0 := by
    intro t x x'
    have e := hinv (lowerShearSL2 t) (x, 0) (x', 0)
    rw [doubleNaturalSL2_lowerShearSL2, doubleNaturalSL2_lowerShearSL2] at e
    simp only [add_zero] at e
    have hv : ∀ z : W, ((z, t • z) : W × W) =
        LinearMap.inl k W W z + t • LinearMap.inr k W W z := fun z => by simp
    rw [hv, hv] at e
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.inl_apply, LinearMap.inr_apply] at e
    linear_combination e
  refine ⟨fun x x' => ?_, fun y y' => ?_, fun x y => ?_⟩
  · have h : (2 : k) * B (x, 0) (x', 0) = 0 := by
      linear_combination hup 1 x x' + hup (-1) x x'
    exact (mul_eq_zero.mp h).resolve_left h2
  · have h : (2 : k) * B (0, y) (0, y') = 0 := by
      linear_combination hlo 1 y y' + hlo (-1) y y'
    exact (mul_eq_zero.mp h).resolve_left h2
  · have h : (2 : k) * (B (x, 0) (0, y) + B (0, x) (y, 0)) = 0 := by
      linear_combination hup 1 x y - hup (-1) x y
    have h' := (mul_eq_zero.mp h).resolve_left h2
    have hneg := hBalt.neg_eq (y, 0) (0, x)
    linear_combination h' + hneg

theorem commute_smul_one_add_smul {A : Type*} [Ring A] [Algebra k A] (J : A) (x y x' y' : k) :
    Commute (x • 1 + y • J) (x' • 1 + y' • J) :=
  ((Commute.one_left _).smul_left x).add_left
    ((((Commute.one_right J).smul_right x').add_right ((Commute.refl J).smul_right y')).smul_left y)

theorem isSolvable_bilinIsometryGroup_of_finrank_eq_two (hk : ringChar k ≠ 2)
    (hW : Module.finrank k W = 2) {β : LinearMap.BilinForm k W} (hβ : β.Nondegenerate)
    (hsymm : β.IsSymm) : Group.IsSolvable (bilinIsometryGroup β) := by
  have : Module.Finite k W := Module.finite_of_finrank_eq_succ hW
  have : Invertible (2 : k) := invertibleOfNonzero (Ring.two_ne_zero hk)
  obtain ⟨e, he⟩ : ∃ e : Basis (Fin 2) k W, LinearMap.IsOrthoᵢ β e := by
    rw [← hW]
    exact LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hsymm)
  have h01 : β (e 0) (e 1) = 0 := he (by decide : (0 : Fin 2) ≠ 1)
  have h10 : β (e 1) (e 0) = 0 := he (by decide : (1 : Fin 2) ≠ 0)
  have hb : β (e 0) (e 0) ≠ 0 := he.not_isOrtho_basis_self_of_separatingLeft hβ.1 0
  set b := β (e 0) (e 0) with hbdef
  set c := β (e 1) (e 1) with hcdef
  set J : W →ₗ[k] W := e.constr k ![e 1, -(c / b) • e 0]
  have hJ0 : J (e 0) = e 1 := by simp [J]
  have hJ1 : J (e 1) = -(c / b) • e 0 := by simp [J]
  have key : ∀ T : W →ₗ[k] W, (∀ x y, β (T x) (T y) = β x y) → LinearMap.det T = 1 →
      ∃ x y : k, T = x • 1 + y • J := by
    intro T hT hdet
    have hT0 : T (e 0) = e.repr (T (e 0)) 0 • e 0 + e.repr (T (e 0)) 1 • e 1 := by
      have h := e.sum_repr (T (e 0))
      rw [Fin.sum_univ_two] at h
      exact h.symm
    have hT1 : T (e 1) = e.repr (T (e 1)) 0 • e 0 + e.repr (T (e 1)) 1 • e 1 := by
      have h := e.sum_repr (T (e 1))
      rw [Fin.sum_univ_two] at h
      exact h.symm
    have E3 : e.repr (T (e 0)) 0 * e.repr (T (e 1)) 1 -
        e.repr (T (e 1)) 0 * e.repr (T (e 0)) 1 = 1 := by
      rw [← hdet, ← LinearMap.det_toMatrix e, Matrix.det_fin_two]
      simp only [LinearMap.toMatrix_apply]
    have E1 := hT (e 0) (e 0)
    have E2 := hT (e 0) (e 1)
    rw [hT0] at E1
    rw [hT0, hT1, h01] at E2
    generalize e.repr (T (e 0)) 0 = x at hT0 E1 E2 E3
    generalize e.repr (T (e 0)) 1 = y at hT0 E1 E2 E3
    generalize e.repr (T (e 1)) 0 = z at hT1 E1 E2 E3
    generalize e.repr (T (e 1)) 1 = w at hT1 E1 E2 E3
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h01,
      h10, ← hbdef, ← hcdef] at E1 E2
    have hwx : w = x := by
      have h : b * (w - x) = 0 := by linear_combination y * E2 - w * E1 + b * x * E3
      exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hb)
    subst w
    have hz : b * z + c * y = 0 := by
      linear_combination x * E2 - z * E1 + (z * b - (b * z + c * y)) * E3
    have hz' : z = -(c / b) * y := by
      field_simp
      linear_combination hz
    refine ⟨x, y, e.ext fun i => ?_⟩
    fin_cases i
    · simp [hT0, hJ0]
    · simp only [Fin.mk_one, Fin.isValue, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, hT1, hJ1, hz']
      module
  let det : bilinIsometryGroup β →* kˣ :=
    (Units.map (LinearMap.det : (W →ₗ[k] W) →* k)).comp (bilinIsometryGroup β).subtype
  have hdet : ∀ g : det.ker, LinearMap.det
      (((g : bilinIsometryGroup β) : LinearMap.GeneralLinearGroup k W) : W →ₗ[k] W) = 1 := by
    intro g
    have h := congrArg Units.val (MonoidHom.mem_ker.mp g.2)
    simpa [det] using h
  have : Group.IsSolvable det.ker := Group.isSolvable_of_comm fun g g' => by
    obtain ⟨x, y, hxy⟩ := key _ (mem_bilinIsometryGroup.mp (g : bilinIsometryGroup β).2) (hdet g)
    obtain ⟨x', y', hxy'⟩ :=
      key _ (mem_bilinIsometryGroup.mp (g' : bilinIsometryGroup β).2) (hdet g')
    refine Subtype.ext (Subtype.ext (Units.ext ?_))
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hxy, hxy']
    exact commute_smul_one_add_smul J x y x' y'
  exact Group.isSolvable_of_ker_le_range det.ker.subtype det (by rw [Subgroup.range_subtype])

theorem double_natural_SL2_symplectic_centralizer_solvable (hk : ringChar k ≠ 2)
    (hW : Module.finrank k W = 2) (B : LinearMap.BilinForm k (W × W)) (hB : B.Nondegenerate)
    (hBalt : B.IsAlt)
    (hinv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) k) (u v : W × W),
      B ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) u)
        ((doubleNaturalSL2 (W := W) g : W × W →ₗ[k] W × W) v) = B u v) :
    Group.IsSolvable (Subgroup.centralizer
      (((doubleNaturalSL2 (k := k) (W := W)).range.subgroupOf (bilinIsometryGroup B) :
        Set (bilinIsometryGroup B)))) := by
  obtain ⟨hA, hD, hS⟩ := doubleNaturalSL2_invariant_form_pieces hk hBalt hinv
  set β : LinearMap.BilinForm k W := B.compl₁₂ (LinearMap.inl k W W) (LinearMap.inr k W W)
  have hβapply : ∀ x y, β x y = B (x, 0) (0, y) := fun x y => rfl
  have hβsymm : β.IsSymm := ⟨fun x y => by rw [hβapply, hβapply, hS]⟩
  have hβnd : β.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h0 : ((x, 0) : W × W) = 0 := hB.1 _ fun v => by
        obtain ⟨x', y'⟩ := v
        rw [show ((x', y') : W × W) = (x', 0) + (0, y') by simp, map_add, hA, zero_add,
          ← hβapply]
        exact hx y'
      exact congrArg Prod.fst h0
    · have h0 : ((0, y) : W × W) = 0 := hB.2 _ fun u => by
        obtain ⟨x', y'⟩ := u
        rw [show ((x', y') : W × W) = (x', 0) + (0, y') by simp, map_add, LinearMap.add_apply,
          hD, add_zero, ← hβapply]
        exact hy x'
      exact congrArg Prod.snd h0
  have := isSolvable_bilinIsometryGroup_of_finrank_eq_two hk hW hβnd hβsymm
  set C := Subgroup.centralizer
    (((doubleNaturalSL2 (k := k) (W := W)).range.subgroupOf (bilinIsometryGroup B) :
      Set (bilinIsometryGroup B)))
  have hinl : ∀ (h : C) (x : W),
      (((h : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup k (W × W)) :
        W × W →ₗ[k] W × W) (x, 0) =
      (fstInlBlock (((h : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup k (W × W)) :
        W × W →ₗ[k] W × W) x, 0) := fun h x => by
    rw [apply_eq_fstInlBlock_of_mem_centralizer hinv h.2, map_zero]
  have hinr : ∀ (h : C) (y : W),
      (((h : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup k (W × W)) :
        W × W →ₗ[k] W × W) (0, y) =
      (0, fstInlBlock (((h : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup k (W × W)) :
        W × W →ₗ[k] W × W) y) := fun h y => by
    rw [apply_eq_fstInlBlock_of_mem_centralizer hinv h.2, map_zero]
  let Φ : C →* Module.End k W :=
    { toFun := fun h => fstInlBlock
        (((h : bilinIsometryGroup B) : LinearMap.GeneralLinearGroup k (W × W)) :
          W × W →ₗ[k] W × W)
      map_one' := fstInlBlock_one
      map_mul' := fun h h' => fstInlBlock_mul fun x => by rw [hinl h' x] }
  have hmem : ∀ h : C, Φ.toHomUnits h ∈ bilinIsometryGroup β := fun h => by
    rw [mem_bilinIsometryGroup]
    intro x y
    rw [MonoidHom.coe_toHomUnits, hβapply, hβapply]
    change B (fstInlBlock _ x, 0) (0, fstInlBlock _ y) = B (x, 0) (0, y)
    rw [← hinl h x, ← hinr h y]
    exact mem_bilinIsometryGroup.mp (h : bilinIsometryGroup B).2 _ _
  refine Group.isSolvable_of_isSolvable_injective
    (f := Φ.toHomUnits.codRestrict (bilinIsometryGroup β) hmem) ?_
  rw [injective_iff_map_eq_one]
  intro h h1
  have hT : Φ h = 1 := congrArg (fun u : bilinIsometryGroup β =>
    ((u : LinearMap.GeneralLinearGroup k W) : W →ₗ[k] W)) h1
  refine Subtype.ext (Subtype.ext (Units.ext (LinearMap.ext fun ⟨x, y⟩ => ?_)))
  rw [apply_eq_fstInlBlock_of_mem_centralizer hinv h.2]
  change (Φ h x, Φ h y) = (x, y)
  rw [hT]
  rfl

end CFSG.LocalAnalysis.ComponentInitial
