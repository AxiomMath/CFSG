module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFFrame

public noncomputable section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped MatrixGroups commutatorElement

namespace GenLocL3Blk

variable {K : Type} [Field K]

@[expose] def blkMat (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  if i = 0 then !![g 0 0, g 0 1, 0; g 1 0, g 1 1, 0; 0, 0, 1]
  else !![1, 0, 0; 0, g 0 0, g 0 1; 0, g 1 0, g 1 1]

theorem blkMat_mul (i : Fin 2) (g h : Matrix (Fin 2) (Fin 2) K) :
    blkMat i (g * h) = blkMat i g * blkMat i h := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;>
    simp [blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three])

theorem blkMat_one (i : Fin 2) : blkMat i (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [blkMat])

theorem det_blkMat (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) : (blkMat i g).det = g.det := by
  fin_cases i <;> simp [blkMat, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def pos (i a : Fin 2) : Fin 3 := ⟨i.1 + a.1, by omega⟩

theorem blkMat_apply_pos (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) (a b : Fin 2) :
    blkMat i g (pos i a) (pos i b) = g a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [blkMat, pos]

theorem blkMat_injective (i : Fin 2) : Function.Injective (blkMat (K := K) i) := by
  intro g h hgh
  ext a b
  have := congrFun (congrFun hgh (pos i a)) (pos i b)
  rwa [blkMat_apply_pos, blkMat_apply_pos] at this

@[expose] def blkHom (i : Fin 2) : SL(2, K) →* SL(3, K) where
  toFun g := ⟨blkMat i (g : Matrix (Fin 2) (Fin 2) K), by rw [det_blkMat]; exact g.2⟩
  map_one' := Subtype.ext (by simp [blkMat_one])
  map_mul' g h := Subtype.ext (by
    change blkMat i ((g * h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      blkMat i (g : Matrix (Fin 2) (Fin 2) K) * blkMat i (h : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul, blkMat_mul])

theorem coe_blkHom (i : Fin 2) (g : SL(2, K)) :
    ((blkHom i g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      blkMat i (g : Matrix (Fin 2) (Fin 2) K) :=
  rfl

@[expose] def phi (i : Fin 2) : SL(2, K) →* LinearFlag.projectiveSL 3 K :=
  (LinearFlag.proj 3 K).comp (blkHom i)

@[expose] def corner (i : Fin 2) : Fin 3 := if i = 0 then 2 else 0

theorem blkMat_corner (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) :
    blkMat i g (corner i) (corner i) = 1 := by
  fin_cases i <;> simp [blkMat, corner]

theorem phi_injective (i : Fin 2) : Function.Injective (phi (K := K) i) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h1 : blkHom i g ∈ LinearFlag.scalars 3 K := LinearFlag.proj_eq_one_iff.1 hg
  obtain ⟨c, -, hc⟩ := h1
  have h2 := congrFun (congrFun hc (corner i)) (corner i)
  rw [coe_blkHom, blkMat_corner] at h2
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h2
  have hc1 : (c : K) = 1 := h2.symm
  have h3 : ((blkHom i g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hc, hc1]; simp
  rw [coe_blkHom, ← blkMat_one i] at h3
  exact Subtype.ext (blkMat_injective i h3)

theorem blkMat_map (σ : K ≃+* K) (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) :
    (blkMat i g).map σ = blkMat i (g.map σ) := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [blkMat])

theorem blkMat_transpose (i : Fin 2) (g : Matrix (Fin 2) (Fin 2) K) :
    (blkMat i g)ᵀ = blkMat i gᵀ := by
  fin_cases i <;> (ext a b; fin_cases a <;> fin_cases b <;> simp [blkMat])

theorem fieldAut_phi (σ : K ≃+* K) (i : Fin 2) (g : SL(2, K)) :
    LinearFlag.fieldAut 3 K σ (phi i g) = phi i (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  unfold phi
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.fieldAut_proj]
  congr 1
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.map σ.toRingHom (blkHom i g) : SL(3, K)) :
      Matrix (Fin 3) (Fin 3) K) =
    blkMat i ((Matrix.SpecialLinearGroup.map σ.toRingHom g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  exact blkMat_map σ i _

theorem dualAut_phi (i : Fin 2) (g : SL(2, K)) :
    LinearFlag.dualAut 3 K (phi i g) = phi i ((g⁻¹).transpose) := by
  unfold phi
  simp only [MonoidHom.comp_apply]
  rw [LinearFlag.dualAut_proj]
  congr 1
  apply Subtype.ext
  rw [← map_inv]
  change (((blkHom i g⁻¹ : SL(3, K)).transpose : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
    blkMat i (((g⁻¹).transpose : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose, coe_blkHom,
    blkMat_transpose]

theorem pos_00 : pos 0 0 = 0 := rfl
theorem pos_01 : pos 0 1 = 1 := rfl
theorem pos_10 : pos 1 0 = 1 := rfl
theorem pos_11 : pos 1 1 = 2 := rfl

theorem diag_ne_zero {x : GL (Fin 3) K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) (a : Fin 3) :
    (x : Matrix (Fin 3) (Fin 3) K) a a ≠ 0 := by
  have h := GeneralLinearGroup.det_ne_zero x
  rw [← hx.diagonal_diag, Matrix.det_diagonal] at h
  exact Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)

theorem conjAut_phi_mem {x : GL (Fin 3) K}
    (hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) (i : Fin 2) (g : SL(2, K)) :
    LinearFlag.conjAut 3 K x (phi i g) ∈ (phi i).range := by
  set d : Fin 3 → K := fun a => (x : Matrix (Fin 3) (Fin 3) K) a a with hd
  have hd0 : ∀ a, d a ≠ 0 := diag_ne_zero hx
  have hxd : (x : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal d := hx.diagonal_diag.symm
  set u : K := d (pos i 0) / d (pos i 1) with hu
  set v : K := d (pos i 1) / d (pos i 0) with hv
  have huv : u * v = 1 := by
    rw [hu, hv]; field_simp [hd0 (pos i 0), hd0 (pos i 1)]
  let g'' : SL(2, K) := ⟨!![g 0 0, u * g 0 1; v * g 1 0, g 1 1], by
    rw [Matrix.det_fin_two_of]
    have h1 := g.2
    rw [Matrix.det_fin_two] at h1
    linear_combination h1 - (g 0 1 * g 1 0) * huv⟩
  refine ⟨g'', ?_⟩
  show LinearFlag.proj 3 K (blkHom i g'') =
    LinearFlag.conjAut 3 K x (LinearFlag.proj 3 K (blkHom i g))
  rw [LinearFlag.conjAut_proj]
  congr 1
  apply Subtype.ext
  have key : (x : Matrix (Fin 3) (Fin 3) K) * blkMat i (g : Matrix (Fin 2) (Fin 2) K) =
      blkMat i (g'' : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 3) (Fin 3) K) := by
    rw [hxd]
    have h0 := hd0 0
    have h1 := hd0 1
    have h2 := hd0 2
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    fin_cases i <;> fin_cases a <;> fin_cases b <;>
      simp [blkMat, g'', u, v, pos_00, pos_01, pos_10, pos_11] <;> field_simp
  rw [LinearFlag.coe_slConjugation, coe_blkHom, coe_blkHom, eq_comm,
    Units.mul_inv_eq_iff_eq_mul]
  exact key

theorem stable_phi {y : MulAut (LinearFlag.projectiveSL 3 K)} (hy : y ∈ frameStab 3 K)
    (i : Fin 2) (g : SL(2, K)) : y (phi i g) ∈ (phi i).range := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := GenLocL3NFFrame.mem_frameStab_iff.1 hy
  have hδ : ∀ z ∈ (phi i).range, LinearFlag.dualAut 3 K z ∈ (phi i).range := by
    rintro _ ⟨g, rfl⟩
    rw [dualAut_phi]
    exact ⟨_, rfl⟩
  have hf : ∀ z ∈ (phi i).range, LinearFlag.fieldAut 3 K σ z ∈ (phi i).range := by
    rintro _ ⟨g, rfl⟩
    rw [fieldAut_phi]
    exact ⟨_, rfl⟩
  have hc : ∀ z ∈ (phi i).range, LinearFlag.conjAut 3 K x z ∈ (phi i).range := by
    rintro _ ⟨g, rfl⟩
    exact conjAut_phi_mem hx i g
  have h1 : (LinearFlag.dualAut 3 K ^ ε) (phi i g) ∈ (phi i).range := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · simp
    · simpa using hδ _ ⟨g, rfl⟩
  simp only [MulAut.mul_apply]
  exact hc _ (hf _ h1)

theorem exists_restrict_action {H J A : Type} [Group H] [Group J] [Group A] (φ : H →* J)
    (hφ : Function.Injective φ) (α : A →* MulAut J)
    (hst : ∀ (a : A) (h : H), α a (φ h) ∈ φ.range) :
    ∃ β : A →* MulAut H, ∀ (a : A) (h : H), α a (φ h) = φ (β a h) := by
  choose f hf using hst
  have hmul : ∀ a h k, f a (h * k) = f a h * f a k := fun a h k =>
    hφ (by rw [hf, map_mul, map_mul, map_mul, hf, hf])
  have hone : ∀ h, f 1 h = h := fun h => hφ (by rw [hf, map_one, MulAut.one_apply])
  have hcomp : ∀ a b h, f (a * b) h = f a (f b h) := fun a b h =>
    hφ (by rw [hf, map_mul, MulAut.mul_apply, hf, hf])
  let β : A →* MulAut H :=
    { toFun := fun a =>
        { toFun := f a
          invFun := f a⁻¹
          left_inv := fun h => by rw [← hcomp, inv_mul_cancel, hone]
          right_inv := fun h => by rw [← hcomp, mul_inv_cancel, hone]
          map_mul' := hmul a }
      map_one' := MulEquiv.ext hone
      map_mul' := fun a b => MulEquiv.ext (hcomp a b) }
  exact ⟨β, fun a h => (hf a h).symm⟩

theorem pos_ne (i : Fin 2) {a b : Fin 2} (hab : a ≠ b) : pos i a ≠ pos i b := by
  intro h
  apply hab
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [pos] at this
  omega

theorem blkHom_transvection (i : Fin 2) {a b : Fin 2} (hab : a ≠ b) (t : K) :
    blkHom i (Matrix.SpecialLinearGroup.transvection hab t) =
      Matrix.SpecialLinearGroup.transvection (pos_ne i hab) t := by
  apply Subtype.ext
  rw [coe_blkHom, CFSG.LinearGroups.coe_transvection, CFSG.LinearGroups.coe_transvection]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    first
    | exact absurd rfl hab
    | (ext p q; fin_cases p <;> fin_cases q <;> simp [blkMat, pos, Matrix.add_apply])

abbrev tv {i j : Fin 3} (h : i ≠ j) (c : K) : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection h c

theorem sup_blkHom_range : (blkHom (K := K) 0).range ⊔ (blkHom (K := K) 1).range = ⊤ := by
  set S : Subgroup SL(3, K) := (blkHom (K := K) 0).range ⊔ (blkHom (K := K) 1).range with hS
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have n01 : (0 : Fin 3) ≠ 1 := by decide
  have n10 : (1 : Fin 3) ≠ 0 := by decide
  have n12 : (1 : Fin 3) ≠ 2 := by decide
  have n21 : (2 : Fin 3) ≠ 1 := by decide
  have n02 : (0 : Fin 3) ≠ 2 := by decide
  have n20 : (2 : Fin 3) ≠ 0 := by decide
  have m0 : ∀ {a b : Fin 2} (hab : a ≠ b) (t : K),
      Matrix.SpecialLinearGroup.transvection (pos_ne 0 hab) t ∈ S := fun hab t => by
    rw [← blkHom_transvection 0 hab t]
    exact Subgroup.mem_sup_left ⟨_, rfl⟩
  have m1 : ∀ {a b : Fin 2} (hab : a ≠ b) (t : K),
      Matrix.SpecialLinearGroup.transvection (pos_ne 1 hab) t ∈ S := fun hab t => by
    rw [← blkHom_transvection 1 hab t]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have t01 : ∀ t : K, tv n01 t ∈ S := fun t => m0 h01 t
  have t10 : ∀ t : K, tv n10 t ∈ S := fun t => m0 h10 t
  have t12 : ∀ t : K, tv n12 t ∈ S := fun t => m1 h01 t
  have t21 : ∀ t : K, tv n21 t ∈ S := fun t => m1 h10 t
  have comm : ∀ {a b : SL(3, K)}, a ∈ S → b ∈ S → ⁅a, b⁆ ∈ S := fun {a b} ha hb => by
    rw [commutatorElement_def]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have t02 : ∀ t : K, tv n02 t ∈ S := by
    intro t
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection n01 n12 n02 t 1
    rw [mul_one] at h
    change Matrix.SpecialLinearGroup.transvection n02 t ∈ S
    rw [← h]
    exact comm (t01 t) (t12 1)
  have t20 : ∀ t : K, tv n20 t ∈ S := by
    intro t
    have h := Matrix.SpecialLinearGroup.commutatorElement_transvection n21 n10 n20 t 1
    rw [mul_one] at h
    change Matrix.SpecialLinearGroup.transvection n20 t ∈ S
    rw [← h]
    exact comm (t21 t) (t10 1)
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (K := K) (n := 3),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact t01 c
    | exact t02 c
    | exact t10 c
    | exact t12 c
    | exact t20 c
    | exact t21 c

theorem range_phi_sup : (phi (K := K) 0).range ⊔ (phi (K := K) 1).range = ⊤ := by
  have h : ∀ i : Fin 2,
      (phi (K := K) i).range = (blkHom i).range.map (LinearFlag.proj 3 K) := fun i => by
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨blkHom i g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, rfl⟩
  rw [h, h, ← Subgroup.map_sup, sup_blkHom_range,
    Subgroup.map_top_of_surjective _ (LinearFlag.proj_surjective 3 K)]

end GenLocL3Blk

end CFSG.GH74.Generic.BProg.B2
