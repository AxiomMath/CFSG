module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

open Matrix CFSG.RankThree.PartTwo
open scoped MatrixGroups

section Unitary

variable {L : Type} [Field L]

@[expose] def frobGL (σ : L →+* L) : GL (Fin 3) L →* GL (Fin 3) L :=
  Units.map (RingHom.mapMatrix σ).toMonoidHom

theorem coe_frobGL (σ : L →+* L) (g : GL (Fin 3) L) :
    ((frobGL σ g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (g : Matrix (Fin 3) (Fin 3) L).map σ :=
  rfl

@[expose] def invTr : GL (Fin 3) L →* GL (Fin 3) L where
  toFun g := ⟨((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ,
    (g : Matrix (Fin 3) (Fin 3) L)ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' A B := Units.ext (by
    change (((A * B)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ =
      ((A⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ *
        ((B⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])

theorem coe_invTr (g : GL (Fin 3) L) :
    ((invTr g : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      ((g⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ :=
  rfl

theorem coe_invTr_inv (g : GL (Fin 3) L) :
    (((invTr g)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      (g : Matrix (Fin 3) (Fin 3) L)ᵀ :=
  rfl

@[expose] def diagU : (Fin 3 → Lˣ) →* GL (Fin 3) L where
  toFun x := ⟨diagonal fun i => (x i : L), diagonal fun i => (((x i)⁻¹ : Lˣ) : L),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.mul_inv (x i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; exact Units.inv_mul (x i)⟩
  map_one' := Units.ext (by
    change (diagonal fun i => ((1 : Lˣ) : L)) = 1
    rw [Units.val_one, diagonal_one])
  map_mul' x y := Units.ext (by
    change (diagonal fun i => ((x i * y i : Lˣ) : L)) =
      diagonal (fun i => (x i : L)) * diagonal fun i => (y i : L)
    rw [diagonal_mul_diagonal]
    simp only [Units.val_mul])

theorem coe_diagU (x : Fin 3 → Lˣ) :
    ((diagU x : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = diagonal fun i => (x i : L) :=
  rfl

theorem coe_diagU_inv (x : Fin 3 → Lˣ) :
    (((diagU x)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      diagonal fun i => (((x i)⁻¹ : Lˣ) : L) :=
  rfl

theorem frobGL_diagU (σ : L →+* L) (x : Fin 3 → Lˣ) :
    frobGL σ (diagU x) = diagU fun i => Units.map σ.toMonoidHom (x i) :=
  Units.ext (by rw [coe_frobGL, coe_diagU, coe_diagU, diagonal_map (map_zero σ)]; rfl)

theorem invTr_diagU (x : Fin 3 → Lˣ) : invTr (diagU x) = diagU x⁻¹ :=
  Units.ext (by rw [coe_invTr, coe_diagU_inv, diagonal_transpose, coe_diagU]; rfl)

theorem invTr_diagU' (x : Fin 3 → Lˣ) : invTr (diagU x) = (diagU x)⁻¹ := by
  rw [invTr_diagU, map_inv]

theorem scalar_eq_diagU (w : Lˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) w = diagU fun _ => w :=
  Units.ext (by rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagU, Matrix.scalar_apply])

@[expose] def thetaD (σ : L →+* L) (d : Fin 3 → Lˣ) : GL (Fin 3) L →* GL (Fin 3) L :=
  (MulAut.conj (diagU d)).toMonoidHom.comp (invTr.comp (frobGL σ))

theorem thetaD_apply (σ : L →+* L) (d : Fin 3 → Lˣ) (g : GL (Fin 3) L) :
    thetaD σ d g = diagU d * invTr (frobGL σ g) * (diagU d)⁻¹ :=
  rfl

theorem toGL_transvection_inv {i j : Fin 3} (hij : i ≠ j) (c : L) :
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (-c)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul]
  have h : Matrix.SpecialLinearGroup.transvection hij c *
      Matrix.SpecialLinearGroup.transvection hij (-c) = 1 := by
    apply Subtype.ext
    change Matrix.transvection i j c * Matrix.transvection i j (-c) = 1
    rw [Matrix.transvection_mul_transvection_same i j hij, add_neg_cancel,
      Matrix.transvection_zero]
  rw [h, map_one]

theorem thetaD_transvection (σ : L →+* L) (d : Fin 3 → Lˣ) {i j : Fin 3} (hij : i ≠ j)
    (c : L) :
    thetaD σ d (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)) =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij.symm
        (-((d j : L) * σ c * (((d i)⁻¹ : Lˣ) : L)))) := by
  apply Units.ext
  rw [thetaD_apply, Units.val_mul, Units.val_mul, coe_invTr, ← map_inv, coe_frobGL,
    toGL_transvection_inv, coe_diagU, coe_diagU_inv]
  change diagonal (fun k => (d k : L)) * ((Matrix.transvection i j (-c)).map σ)ᵀ *
      diagonal (fun k => (((d k)⁻¹ : Lˣ) : L)) = Matrix.transvection j i _
  ext k l
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
      Matrix.one_apply, diagonal] <;> ring

theorem thetaD_diagA (σ : L →+* L) (d : Fin 3 → Lˣ) (a : Lˣ) :
    thetaD σ d (diagA a) = diagA (Units.map σ.toMonoidHom a)⁻¹ := by
  apply Units.ext
  rw [thetaD_apply, Units.val_mul, Units.val_mul, coe_invTr, ← map_inv, coe_frobGL,
    coe_diagA_inv, coe_diagU, coe_diagU_inv, coe_diagA]
  ext k l
  fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, diagonal, Units.val_inv_eq_inv_val] <;>
    rw [mul_right_comm, mul_inv_cancel₀ (Units.ne_zero _), one_mul]


theorem invTr_frobGL_scalar (σ : L →+* L) (w : Lˣ) :
    invTr (frobGL σ (Matrix.GeneralLinearGroup.scalar (Fin 3) w)) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom w)⁻¹ := by
  rw [scalar_eq_diagU, scalar_eq_diagU, frobGL_diagU, invTr_diagU]
  rfl

theorem invTr_frobGL_invTr_frobGL {σ : L →+* L} (hσ2 : ∀ c, σ (σ c) = c) (g : GL (Fin 3) L) :
    invTr (frobGL σ (invTr (frobGL σ g))) = g := by
  apply Units.ext
  rw [coe_invTr, ← map_inv, coe_frobGL, coe_invTr_inv, coe_frobGL]
  ext i j
  simp [hσ2]

theorem mem_glPi_false_iff {p f : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f L)
    {σ : L →+* L} (hσ : ∀ c, σ c = c ^ p ^ f) (u : GL (Fin 3) L) :
    u ∈ Sec4.glPi false 3 (p ^ f) L ↔ invTr (frobGL σ u) = u := by
  rw [Sec4.mem_glPi_false h]
  have hb : (u : Matrix (Fin 3) (Fin 3) L).map h.bar =
      ((frobGL σ u : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    rw [coe_frobGL]
    ext i j
    simp [h.bar_apply, hσ]
  rw [hb, ← coe_invTr_inv, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem invTr_frobGL_mul_inv_mem_center_iff {p f : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f L) {σ : L →+* L}
    (hσ : ∀ c, σ c = c ^ p ^ f) (hσ2 : ∀ c, σ (σ c) = c)
    (hnorm : ∀ w : Lˣ, Units.map σ.toMonoidHom w = w →
      ∃ ν : Lˣ, ν * Units.map σ.toMonoidHom ν = w)
    (u : GL (Fin 3) L) :
    invTr (frobGL σ u) * u⁻¹ ∈ Subgroup.center (GL (Fin 3) L) ↔
      Matrix.ProjGenLinGroup.mk u ∈ CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) L) := by
  constructor
  · intro hc
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
    obtain ⟨w, hw⟩ := hc
    have hu : invTr (frobGL σ u) = Matrix.GeneralLinearGroup.scalar (Fin 3) w * u := by
      rw [hw, inv_mul_cancel_right]
    have hσw : Units.map σ.toMonoidHom w = w := by
      have h1 := invTr_frobGL_invTr_frobGL hσ2 u
      rw [hu, map_mul, map_mul, invTr_frobGL_scalar, hu, ← mul_assoc, ← map_mul] at h1
      have h2 : Matrix.GeneralLinearGroup.scalar (Fin 3) ((Units.map σ.toMonoidHom w)⁻¹ * w) = 1 :=
        mul_eq_right.1 h1
      have h3 : (Units.map σ.toMonoidHom w)⁻¹ * w = 1 := by
        have h4 := congrArg (fun A : GL (Fin 3) L => (A : Matrix (Fin 3) (Fin 3) L) 0 0) h2
        simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one,
          Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at h4
        exact Units.ext h4
      exact (inv_mul_eq_one.1 h3)
    obtain ⟨ν, hν⟩ := hnorm w hσw
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) ν * u, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_glPi_false_iff h hσ, map_mul, map_mul, invTr_frobGL_scalar, hu,
        ← mul_assoc, ← map_mul]
      congr 2
      rw [← hν, mul_comm ν, inv_mul_cancel_left]
    · rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]
  · rintro ⟨v, hv, hvu⟩
    rw [SetLike.mem_coe, mem_glPi_false_iff h hσ] at hv
    obtain ⟨w, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.1 hvu
    have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom w)⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 3) w)⁻¹ ∈ Subgroup.center (GL (Fin 3) L) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨(Units.map σ.toMonoidHom w)⁻¹ * w⁻¹, by
        rw [map_mul, map_inv (Matrix.GeneralLinearGroup.scalar (Fin 3)) w]⟩
    have e : invTr (frobGL σ (v * Matrix.GeneralLinearGroup.scalar (Fin 3) w)) *
        (v * Matrix.GeneralLinearGroup.scalar (Fin 3) w)⁻¹ =
        v * (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toMonoidHom w)⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 3) w)⁻¹) * v⁻¹ := by
      rw [map_mul, map_mul, invTr_frobGL_scalar, hv, _root_.mul_inv_rev]
      group
    rw [e]
    exact (Subgroup.normal_of_characteristic (Subgroup.center _)).conj_mem _ hz v

theorem thetaD_eq_conj {σ : L →+* L} {d x : Fin 3 → Lˣ}
    (hx : ∀ i, x i * Units.map σ.toMonoidHom (x i) = (d i)⁻¹) (g : GL (Fin 3) L) :
    thetaD σ d g = (diagU x)⁻¹ * invTr (frobGL σ (diagU x * g * (diagU x)⁻¹)) * diagU x := by
  have hd : diagU d = (diagU x)⁻¹ * (diagU fun i => Units.map σ.toMonoidHom (x i))⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul]
    congr 1
    funext i
    rw [Pi.mul_apply, Pi.inv_apply, Pi.inv_apply, ← _root_.mul_inv_rev, mul_comm, hx, inv_inv]
  rw [thetaD_apply, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, frobGL_diagU,
    invTr_diagU', hd]
  group

theorem thetaD_mul_inv_mem_center_iff {p f : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f L) {σ : L →+* L}
    (hσ : ∀ c, σ c = c ^ p ^ f) (hσ2 : ∀ c, σ (σ c) = c)
    (hnorm : ∀ w : Lˣ, Units.map σ.toMonoidHom w = w →
      ∃ ν : Lˣ, ν * Units.map σ.toMonoidHom ν = w)
    {d x : Fin 3 → Lˣ} (hx : ∀ i, x i * Units.map σ.toMonoidHom (x i) = (d i)⁻¹)
    (g : GL (Fin 3) L) :
    thetaD σ d g * g⁻¹ ∈ Subgroup.center (GL (Fin 3) L) ↔
      Matrix.ProjGenLinGroup.mk (diagU x * g * (diagU x)⁻¹) ∈
        CFSG.PGLModel.projImage (Sec4.glPi false 3 (p ^ f) L) := by
  rw [← invTr_frobGL_mul_inv_mem_center_iff h hσ hσ2 hnorm, thetaD_eq_conj hx]
  set u := diagU x * g * (diagU x)⁻¹ with hu
  have e : (diagU x)⁻¹ * invTr (frobGL σ u) * diagU x * g⁻¹ =
      (diagU x)⁻¹ * (invTr (frobGL σ u) * u⁻¹) * ((diagU x)⁻¹)⁻¹ := by
    rw [hu]
    group
  rw [e]
  constructor
  · intro h1
    have h2 := (Subgroup.normal_of_characteristic (Subgroup.center (GL (Fin 3) L))).conj_mem _
      h1 (diagU x)
    rwa [show diagU x * ((diagU x)⁻¹ * (invTr (frobGL σ u) * u⁻¹) * ((diagU x)⁻¹)⁻¹) *
      (diagU x)⁻¹ = invTr (frobGL σ u) * u⁻¹ by group] at h2
  · intro h1
    exact (Subgroup.normal_of_characteristic (Subgroup.center (GL (Fin 3) L))).conj_mem _ h1 _


theorem exists_mul_frob_eq [Finite L] {q : ℕ} (hL : Nat.card L = q ^ 2) (hq1 : 1 ≤ q)
    {σ : L →+* L} (hσ : ∀ c, σ c = c ^ q) {w : Lˣ} (hw : Units.map σ.toMonoidHom w = w) :
    ∃ ν : Lˣ, ν * Units.map σ.toMonoidHom ν = w := by
  have hwq : w ^ q = w := by
    rw [← CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.units_frob hσ]
    exact hw
  obtain ⟨t, ht⟩ :=
    CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.exists_pow_succ_eq hL
      hq1 hwq
  refine ⟨t, ?_⟩
  rw [CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.units_frob hσ,
    ← pow_succ', ht]

theorem sl_hom_ext {F : Type} [Field F] {G : Type*} [Group G] {ψ₁ ψ₂ : SL(3, F) →* G}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      ψ₁ (Matrix.SpecialLinearGroup.transvection hij c) =
        ψ₂ (Matrix.SpecialLinearGroup.transvection hij c)) : ψ₁ = ψ₂ := by
  have hle : Subgroup.closure (Set.range (Matrix.TransvectionStruct.toSpecialLinearGroup :
      Matrix.TransvectionStruct (Fin 3) F → SL(3, F))) ≤ ψ₁.eqLocus ψ₂ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
    show ψ₁ (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩) =
      ψ₂ (Matrix.TransvectionStruct.toSpecialLinearGroup ⟨i, j, hij, c⟩)
    rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact h i j hij c
  rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field] at hle
  exact MonoidHom.ext fun x => hle (Subgroup.mem_top x)

theorem gl_hom_ext {F : Type} [Field F] {G : Type*} [Group G] {ψ₁ ψ₂ : GL (Fin 3) F →* G}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (c : F),
      ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)) =
        ψ₂ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c)))
    (hD : ∀ a, ψ₁ (diagA a) = ψ₂ (diagA a)) : ψ₁ = ψ₂ := by
  have hSL := sl_hom_ext (ψ₁ := ψ₁.comp Matrix.SpecialLinearGroup.toGL)
    (ψ₂ := ψ₂.comp Matrix.SpecialLinearGroup.toGL) h
  refine MonoidHom.ext fun g => ?_
  set a := Matrix.GeneralLinearGroup.det g with ha
  have hdet : ((g * (diagA a)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, coe_diagA_inv, det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, mul_one]
    rw [ha, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply]
    exact mul_inv_cancel₀ (by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _)
  set h' : SL(3, F) := ⟨_, hdet⟩ with hh'
  have hgl : Matrix.SpecialLinearGroup.toGL h' = g * (diagA a)⁻¹ := Units.ext rfl
  have hg : g = Matrix.SpecialLinearGroup.toGL h' * diagA a := by rw [hgl, inv_mul_cancel_right]
  have h1 := congrArg (fun φ : SL(3, F) →* G => φ h') hSL
  simp only [MonoidHom.coe_comp, Function.comp_apply] at h1
  rw [hg, map_mul, map_mul, h1, hD]

theorem mk_pow_three_mem_projImage_slPi {p f : ℕ}
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f L) {σ : L →+* L}
    (hσ : ∀ c, σ c = c ^ p ^ f) {u : GL (Fin 3) L} (hu : u ∈ Sec4.glPi false 3 (p ^ f) L) :
    Matrix.ProjGenLinGroup.mk u ^ 3 ∈ CFSG.PGLModel.projImage (Sec4.slPi false 3 (p ^ f) L) := by
  set δ := Matrix.GeneralLinearGroup.det u with hδ
  have hδval : (δ : L) = (u : Matrix (Fin 3) (Fin 3) L).det :=
    Matrix.GeneralLinearGroup.val_det_apply u
  have hδσ : Units.map σ.toMonoidHom δ * δ = 1 := by
    have h1 := (Sec4.mem_glPi_false h).1 hu
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
    have h3 : ((u : Matrix (Fin 3) (Fin 3) L).map h.bar).det =
        σ (u : Matrix (Fin 3) (Fin 3) L).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [h.bar_apply, hσ]
    rw [h3] at h2
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    show σ (δ : L) * (δ : L) = 1
    rw [hδval]
    exact h2
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ ∈ Sec4.glPi false 3 (p ^ f) L := by
    rw [mem_glPi_false_iff h hσ, invTr_frobGL_scalar]
    congr 1
    rw [map_inv, inv_inv]
    exact eq_inv_of_mul_eq_one_left hδσ
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 3) δ⁻¹ * u ^ 3 ∈ Sec4.slPi false 3 (p ^ f) L := by
    rw [Sec4.mem_slPi_false h]
    refine ⟨?_, (Sec4.mem_glPi_false h).1 (mul_mem hz (pow_mem hu 3))⟩
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.det_mul, Matrix.det_pow,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Fin.prod_univ_three, ← hδval]
    have hδ0 : (δ : L) ≠ 0 := Units.ne_zero δ
    rw [Units.val_inv_eq_inv_val]
    field_simp
  refine ⟨_, hs, ?_⟩
  rw [map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul, map_pow]

theorem gl_hom_ext₆ {F : Type} [Field F] {G : Type*} [Group G] {ψ₁ ψ₂ : GL (Fin 3) F →* G}
    (h01 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c)))
    (h12 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 2 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) c)))
    (h02 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 2 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) c)))
    (h10 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (1 : Fin 3) ≠ 0 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c)))
    (h21 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 1 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) c)))
    (h20 : ∀ c, ψ₁ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection
      (show (2 : Fin 3) ≠ 0 by decide) c)) = ψ₂ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) c)))
    (hD : ∀ a, ψ₁ (diagA a) = ψ₂ (diagA a)) : ψ₁ = ψ₂ := by
  refine gl_hom_ext (fun i j hij c => ?_) hD
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01 c
  · exact h02 c
  · exact h10 c
  · exact absurd rfl hij
  · exact h12 c
  · exact h20 c
  · exact h21 c
  · exact absurd rfl hij

end Unitary

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd

end
