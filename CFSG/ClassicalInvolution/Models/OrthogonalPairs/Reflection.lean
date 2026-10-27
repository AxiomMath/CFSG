module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups

section Algebra

variable {K : Type*} [Field K]

@[expose] def polarDet (X Y : Matrix (Fin 2) (Fin 2) K) : K :=
  X 0 0 * Y 1 1 + X 1 1 * Y 0 0 - X 0 1 * Y 1 0 - X 1 0 * Y 0 1

@[expose] def reflM (v X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  X - (polarDet v X / v.det) • v

theorem reflM_reflM {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    reflM v (reflM v X) = X := by
  ext i j
  simp only [reflM, polarDet, Matrix.det_fin_two] at hv ⊢
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

omit [Field K] in
theorem exists_eq_of_fin_two (M : Matrix (Fin 2) (Fin 2) K) :
    ∃ a b c d : K, M = !![a, b; c, d] :=
  ⟨M 0 0, M 0 1, M 1 0, M 1 1, Matrix.eta_fin_two M⟩

theorem reflM_mul_reflM {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0)
    (A X : Matrix (Fin 2) (Fin 2) K) :
    reflM v (A * reflM v X) = X * ((v.det)⁻¹ • (adjugate v * adjugate A * v)) := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_eq_of_fin_two v
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two A
  obtain ⟨x, y, z, w, rfl⟩ := exists_eq_of_fin_two X
  simp only [Matrix.det_fin_two_of] at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, polarDet, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of] <;> field_simp <;>
      ring

theorem reflM_mulRight_reflM {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0)
    (B X : Matrix (Fin 2) (Fin 2) K) :
    reflM v (reflM v X * B) = ((v.det)⁻¹ • (v * adjugate B * adjugate v)) * X := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_eq_of_fin_two v
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two B
  obtain ⟨x, y, z, w, rfl⟩ := exists_eq_of_fin_two X
  simp only [Matrix.det_fin_two_of] at hv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, polarDet, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of] <;> field_simp <;>
      ring

@[expose] def reflMLin (v : Matrix (Fin 2) (Fin 2) K) :
    Module.End K (Matrix (Fin 2) (Fin 2) K) where
  toFun := reflM v
  map_add' X Y := by
    ext i j
    simp only [reflM, polarDet, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  map_smul' c X := by
    ext i j
    simp only [reflM, polarDet, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem reflMLin_apply (v X : Matrix (Fin 2) (Fin 2) K) : reflMLin v X = reflM v X :=
  rfl

@[expose] def rightMult (v A : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  (v.det)⁻¹ • (adjugate v * adjugate A * v)

@[expose] def leftMult (v B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  (v.det)⁻¹ • (v * adjugate B * adjugate v)

theorem det_rightMult {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A.det = 1) : (rightMult v A).det = 1 := by
  rw [rightMult, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate,
    Matrix.det_adjugate, hA]
  simp only [Fintype.card_fin]
  field_simp
  ring

theorem det_leftMult {v : Matrix (Fin 2) (Fin 2) K} (hv : v.det ≠ 0) {B : Matrix (Fin 2) (Fin 2) K}
    (hB : B.det = 1) : (leftMult v B).det = 1 := by
  rw [leftMult, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate,
    Matrix.det_adjugate, hB]
  simp only [Fintype.card_fin]
  field_simp
  ring

@[expose] noncomputable def bilinDet : LinearMap.BilinForm K (Matrix (Fin 2) (Fin 2) K) :=
  LinearMap.mk₂ K (fun X Y => X 0 0 * Y 1 1 - X 0 1 * Y 1 0)
    (fun X₁ X₂ Y => by simp only [Matrix.add_apply]; ring)
    (fun c X Y => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)
    (fun X Y₁ Y₂ => by simp only [Matrix.add_apply]; ring)
    (fun c X Y => by simp only [Matrix.smul_apply, smul_eq_mul]; ring)

@[expose] noncomputable def detQ : QuadraticForm K (Matrix (Fin 2) (Fin 2) K) :=
  (bilinDet (K := K)).toQuadraticMap

theorem detQ_apply (X : Matrix (Fin 2) (Fin 2) K) : detQ X = X.det := by
  simp [detQ, bilinDet, Matrix.det_fin_two]

theorem polar_detQ (X Y : Matrix (Fin 2) (Fin 2) K) :
    QuadraticMap.polar (detQ (K := K)) X Y = polarDet X Y := by
  rw [detQ, LinearMap.BilinMap.polar_toQuadraticMap]
  simp only [bilinDet, LinearMap.mk₂_apply, polarDet]
  ring

theorem nondegenerate_detQ : (detQ (K := K)).Nondegenerate := by
  have hker : LinearMap.ker (QuadraticMap.polarBilin (detQ (K := K))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro X hX
    have h : ∀ Y, polarDet X Y = 0 := fun Y => by
      have := LinearMap.congr_fun hX Y
      simpa [polar_detQ] using this
    have h00 : X 0 0 = 0 := by simpa [polarDet] using h !![0, 0; 0, 1]
    have h11 : X 1 1 = 0 := by simpa [polarDet] using h !![1, 0; 0, 0]
    have h01 : X 0 1 = 0 := by simpa [polarDet] using h !![0, 0; 1, 0]
    have h10 : X 1 0 = 0 := by simpa [polarDet] using h !![0, 1; 0, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, h01, h10]
  have hrad : (detQ (K := K)).radical = ⊥ :=
    eq_bot_iff.mpr ((QuadraticMap.radical_le_ker_polarBilin (Q := (detQ (K := K)))).trans hker.le)
  refine ⟨hrad, ?_⟩
  rw [hker, rank_bot]
  exact zero_le_one

section Conj

variable {G : Type*} [Group G]

@[expose] def conjSubgroup (g : G) (N : Subgroup G) : Subgroup G where
  carrier := {x | g⁻¹ * x * g ∈ N}
  mul_mem' {x y} hx hy := by
    have : g⁻¹ * (x * y) * g = (g⁻¹ * x * g) * (g⁻¹ * y * g) := by group
    show g⁻¹ * (x * y) * g ∈ N
    rw [this]
    exact N.mul_mem hx hy
  one_mem' := by
    show g⁻¹ * 1 * g ∈ N
    rw [mul_one, inv_mul_cancel]
    exact N.one_mem
  inv_mem' {x} hx := by
    have : g⁻¹ * x⁻¹ * g = (g⁻¹ * x * g)⁻¹ := by group
    show g⁻¹ * x⁻¹ * g ∈ N
    rw [this]
    exact N.inv_mem hx

theorem mem_conjSubgroup {g x : G} {N : Subgroup G} : x ∈ conjSubgroup g N ↔ g⁻¹ * x * g ∈ N :=
  Iff.rfl

theorem conjSubgroup_one (N : Subgroup G) : conjSubgroup 1 N = N := by
  ext x
  simp [mem_conjSubgroup]

theorem conjSubgroup_mul (g h : G) (N : Subgroup G) :
    conjSubgroup (g * h) N = conjSubgroup g (conjSubgroup h N) := by
  ext x
  simp only [mem_conjSubgroup, _root_.mul_inv_rev]
  simp [mul_assoc]

theorem conjSubgroup_eq_map (g : G) (N : Subgroup G) :
    conjSubgroup g N = N.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_conjSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy

end Conj

section Groups

@[expose] def leftGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | ∃ A : SL(2, K), ∀ X, g X = (A : Matrix (Fin 2) (Fin 2) K) * X}
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A * B, fun X => ?_⟩
    rw [LinearEquiv.mul_apply, hB, hA, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, fun X => by simp⟩
  inv_mem' := by
    rintro g ⟨A, hA⟩
    refine ⟨A⁻¹, fun X => ?_⟩
    have h1 : g ((A⁻¹ : SL(2, K)) * X : Matrix (Fin 2) (Fin 2) K) = X := by
      rw [hA, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp
    exact (g.symm_apply_eq.mpr h1.symm)

@[expose] def rightGrp : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) where
  carrier := {g | ∃ B : SL(2, K), ∀ X, g X = X * (B : Matrix (Fin 2) (Fin 2) K)}
  mul_mem' := by
    rintro g h ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨B * A, fun X => ?_⟩
    rw [LinearEquiv.mul_apply, hB, hA, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]
  one_mem' := ⟨1, fun X => by simp⟩
  inv_mem' := by
    rintro g ⟨B, hB⟩
    refine ⟨B⁻¹, fun X => ?_⟩
    have h1 : g (X * (B⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = X := by
      rw [hB, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
      simp
    exact (g.symm_apply_eq.mpr h1.symm)

theorem mem_leftGrp {g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} :
    g ∈ leftGrp ↔ ∃ A : SL(2, K), ∀ X, g X = (A : Matrix (Fin 2) (Fin 2) K) * X :=
  Iff.rfl

theorem mem_rightGrp {g : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K} :
    g ∈ rightGrp ↔ ∃ B : SL(2, K), ∀ X, g X = X * (B : Matrix (Fin 2) (Fin 2) K) :=
  Iff.rfl

end Groups

section Reflections

theorem reflection_detQ_apply (v : Matrix (Fin 2) (Fin 2) K) [Invertible (detQ v)]
    (X : Matrix (Fin 2) (Fin 2) K) :
    TauCeti.QuadraticMap.reflection (detQ (K := K)) v X = reflM v X := by
  rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div, polar_detQ, detQ_apply]
  rfl

theorem det_ne_zero_of_invertible {v : Matrix (Fin 2) (Fin 2) K} (h : Invertible (detQ v)) :
    v.det ≠ 0 := by
  have := (isUnit_of_invertible (detQ v)).ne_zero
  rwa [detQ_apply] at this

theorem reflection_detQ_inv_apply (v : Matrix (Fin 2) (Fin 2) K) [Invertible (detQ v)]
    (X : Matrix (Fin 2) (Fin 2) K) :
    ((TauCeti.QuadraticMap.reflection (detQ (K := K)) v)⁻¹ :
      Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) X = reflM v X := by
  rw [show (TauCeti.QuadraticMap.reflection (detQ (K := K)) v)⁻¹ =
    (TauCeti.QuadraticMap.reflection (detQ (K := K)) v).symm from rfl,
    TauCeti.QuadraticMap.reflection_symm, reflection_detQ_apply]

theorem conjSubgroup_reflection_leftGrp (v : Matrix (Fin 2) (Fin 2) K)
    [inst : Invertible (detQ v)] :
    conjSubgroup (TauCeti.QuadraticMap.reflection (detQ (K := K)) v) leftGrp = rightGrp := by
  have hv := det_ne_zero_of_invertible inst
  ext x
  rw [mem_conjSubgroup, mem_leftGrp, mem_rightGrp]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨⟨rightMult v A, det_rightMult hv A.2⟩, fun Y => ?_⟩
    have h1 := hA (reflM v Y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_detQ_apply,
      reflection_detQ_inv_apply] at h1
    have h2 := congrArg (reflM v) h1
    rw [reflM_reflM hv, reflM_mul_reflM hv] at h2
    rw [reflM_reflM hv] at h2
    exact h2
  · rintro ⟨B, hB⟩
    refine ⟨⟨leftMult v B, det_leftMult hv B.2⟩, fun X => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_detQ_apply,
      reflection_detQ_inv_apply, hB]
    exact reflM_mulRight_reflM hv B X

theorem conjSubgroup_reflection_rightGrp (v : Matrix (Fin 2) (Fin 2) K)
    [inst : Invertible (detQ v)] :
    conjSubgroup (TauCeti.QuadraticMap.reflection (detQ (K := K)) v) rightGrp = leftGrp := by
  have hv := det_ne_zero_of_invertible inst
  ext x
  rw [mem_conjSubgroup, mem_leftGrp, mem_rightGrp]
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨⟨leftMult v B, det_leftMult hv B.2⟩, fun Y => ?_⟩
    have h1 := hB (reflM v Y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_detQ_apply,
      reflection_detQ_inv_apply] at h1
    have h2 := congrArg (reflM v) h1
    rw [reflM_reflM hv, reflM_mulRight_reflM hv] at h2
    rw [reflM_reflM hv] at h2
    exact h2
  · rintro ⟨A, hA⟩
    refine ⟨⟨rightMult v A, det_rightMult hv A.2⟩, fun X => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, reflection_detQ_apply,
      reflection_detQ_inv_apply, hA]
    exact reflM_mul_reflM hv A X

end Reflections

section Trichotomy

theorem conjSubgroup_list_prod
    (l : List (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K))
    (hl : ∀ r ∈ l, LinearEquiv.det r = -1 ∧ conjSubgroup r leftGrp = rightGrp ∧
      conjSubgroup r rightGrp = leftGrp) :
    (LinearEquiv.det l.prod = 1 ∧ conjSubgroup l.prod leftGrp = leftGrp ∧
        conjSubgroup l.prod rightGrp = rightGrp) ∨
      (LinearEquiv.det l.prod = -1 ∧ conjSubgroup l.prod leftGrp = rightGrp ∧
        conjSubgroup l.prod rightGrp = leftGrp) := by
  induction l with
  | nil =>
    left
    exact ⟨by simp, by simp [conjSubgroup_one], by simp [conjSubgroup_one]⟩
  | cons r l ih =>
    obtain ⟨hr1, hr2, hr3⟩ := hl r List.mem_cons_self
    rcases ih fun r' hr' => hl r' (List.mem_cons_of_mem r hr') with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · right
      rw [List.prod_cons, map_mul, conjSubgroup_mul, conjSubgroup_mul, h2, h3, hr1, h1, hr2, hr3]
      exact ⟨by simp, rfl, rfl⟩
    · left
      rw [List.prod_cons, map_mul, conjSubgroup_mul, conjSubgroup_mul, h2, h3, hr1, h1, hr2, hr3]
      exact ⟨by simp, rfl, rfl⟩

theorem isometry_trichotomy (h2 : (2 : K) ≠ 0)
    {S : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hS : S ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) :
    (LinearEquiv.det S = 1 ∧ conjSubgroup S leftGrp = leftGrp ∧
        conjSubgroup S rightGrp = rightGrp) ∨
      (LinearEquiv.det S = -1 ∧ conjSubgroup S leftGrp = rightGrp ∧
        conjSubgroup S rightGrp = leftGrp) := by
  have : NeZero (2 : K) := ⟨h2⟩
  obtain ⟨l, hl, -, hprod⟩ := TauCeti.QuadraticMap.exists_reflectionOrthogonal_list_prod_eq
    (detQ (K := K)) nondegenerate_detQ ⟨S, hS⟩
  have hS' : (l.map Subtype.val).prod = S := by
    have h1 : ((l.prod : TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) :
        Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) = S := by
      rw [hprod]
    rw [← h1]
    exact (map_list_prod (Subgroup.subtype _) l).symm
  rw [← hS']
  refine conjSubgroup_list_prod _ fun r hr => ?_
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  obtain ⟨v, hv, rfl⟩ := hl r' hr'
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simpa using conjSubgroup_reflection_leftGrp v
  · simpa using conjSubgroup_reflection_rightGrp v

end Trichotomy

end Algebra

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
