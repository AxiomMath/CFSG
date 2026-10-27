module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.LocalAnalysis.ComponentInitial
open LinearFlag

open Matrix

private abbrev SL3 := SpecialLinearGroup (Fin 3) F4

private abbrev GL3 := GL (Fin 3) F4

private abbrev G3 := LinearFlag.projectiveSL 3 F4

private abbrev U3 : Subgroup G3 := LinearFlag.projUnitriangular 3 F4

private theorem proj_mem_U3 {g : SL3} (hg : g ∈ LinearFlag.unitriangular 3 F4) :
    LinearFlag.proj 3 F4 g ∈ U3 :=
  Subgroup.mem_map_of_mem _ hg

private theorem exists_smul_of_proj_eq {X Y : SL3}
    (h : LinearFlag.proj 3 F4 X = LinearFlag.proj 3 F4 Y) :
    ∃ c : F4ˣ, c ^ 3 = 1 ∧
      (X : Matrix (Fin 3) (Fin 3) F4) = (c : F4) • (Y : Matrix (Fin 3) (Fin 3) F4) := by
  have h' : Y⁻¹ * X ∈ LinearFlag.scalars 3 F4 :=
    LinearFlag.proj_eq_proj_iff.mp h.symm
  obtain ⟨c, hc, hYX⟩ := LinearFlag.mem_scalars.mp h'
  have hYX' : Y⁻¹ * X = LinearFlag.scalarElement c hc := Subtype.ext hYX
  refine ⟨c, hc, ?_⟩
  calc
    (X : Matrix (Fin 3) (Fin 3) F4)
        = ((Y * (Y⁻¹ * X) : SL3) : Matrix (Fin 3) (Fin 3) F4) := by
          rw [show Y * (Y⁻¹ * X) = X by group]
    _ = ((Y * LinearFlag.scalarElement c hc : SL3) : Matrix (Fin 3) (Fin 3) F4) := by
          rw [hYX']
    _ = (Y : Matrix (Fin 3) (Fin 3) F4) * Matrix.scalar (Fin 3) (c : F4) := by
          rw [Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_scalarElement]
    _ = (c : F4) • (Y : Matrix (Fin 3) (Fin 3) F4) := by
          ext i j
          rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.scalar_apply, Finset.sum_eq_single j]
          · simp [mul_comm]
          · intro k _ hk
            simp [hk]
          · intro h
            exact absurd (Finset.mem_univ j) h

private def t01 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) 1

private def t12 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) 1

private def t02 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) 1

private def t10 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) 1

private def t21 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) 1

private def t20 : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) 1

private def t01ω : SL3 := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) F4.ω

private theorem coe_t01 : (t01 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 0 1 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t12 : (t12 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 1 2 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t02 : (t02 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 0 2 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t10 : (t10 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 1 0 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t21 : (t21 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 2 1 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t20 : (t20 : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 2 0 1 :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) 1

private theorem coe_t01ω : (t01ω : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single 0 1 F4.ω :=
  Matrix.SpecialLinearGroup.transvection_coe (by decide) F4.ω

private theorem t01_inv : t01⁻¹ = t01 := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := Matrix.SpecialLinearGroup.transvection_mul_neg
    (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide) (1 : F4)
  rw [show (-1 : F4) = 1 from rfl] at h
  simpa [t01] using h

private theorem t12_inv : t12⁻¹ = t12 := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := Matrix.SpecialLinearGroup.transvection_mul_neg
    (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide) (1 : F4)
  rw [show (-1 : F4) = 1 from rfl] at h
  simpa [t12] using h

private theorem t02_inv : t02⁻¹ = t02 := by
  refine inv_eq_of_mul_eq_one_right ?_
  have h := Matrix.SpecialLinearGroup.transvection_mul_neg
    (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide) (1 : F4)
  rw [show (-1 : F4) = 1 from rfl] at h
  simpa [t02] using h

private theorem t01_inv_transpose : (t01⁻¹).transpose = t10 := by
  rw [t01_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_t01, coe_t10, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

private theorem t12_inv_transpose : (t12⁻¹).transpose = t21 := by
  rw [t12_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_t12, coe_t21, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

private theorem t02_inv_transpose : (t02⁻¹).transpose = t20 := by
  rw [t02_inv]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, coe_t02, coe_t20, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

private theorem graph_fix_matrix {A : GL3} {g : SL3}
    (h : (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4)
        (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g) :
    ∃ c : F4ˣ, c ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F4) * ((g⁻¹).transpose : Matrix (Fin 3) (Fin 3) F4) *
        ((A⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4) =
      (c : F4) • (g : Matrix (Fin 3) (Fin 3) F4) := by
  have h' : LinearFlag.proj 3 F4
      (CatalogueBHigherLinearAction.slConjugation 3 F4 A (g⁻¹).transpose) =
        LinearFlag.proj 3 F4 g := by
    simpa only [MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.conjAut_proj] using h
  obtain ⟨c, hc, hceq⟩ := exists_smul_of_proj_eq h'
  exact ⟨c, hc, by rwa [CatalogueBHigherLinearAction.slConjugation_matrix] at hceq⟩

private theorem field_fix_matrix {A : GL3} {g : SL3}
    (h : (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob)
        (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g) :
    ∃ c : F4ˣ, c ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F4) *
        (SpecialLinearGroup.map frob.toRingHom g : Matrix (Fin 3) (Fin 3) F4) *
        ((A⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4) =
      (c : F4) • (g : Matrix (Fin 3) (Fin 3) F4) := by
  have h' : LinearFlag.proj 3 F4
      (CatalogueBHigherLinearAction.slConjugation 3 F4 A
        (SpecialLinearGroup.map frob.toRingHom g)) = LinearFlag.proj 3 F4 g := by
    simpa only [MulAut.mul_apply, LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj] using h
  obtain ⟨c, hc, hceq⟩ := exists_smul_of_proj_eq h'
  exact ⟨c, hc, by rwa [CatalogueBHigherLinearAction.slConjugation_matrix] at hceq⟩

private theorem mul_single_eq_single_mul {A : GL3} {i j k l : Fin 3} {a b : F4}
    (h : (A : Matrix (Fin 3) (Fin 3) F4) * (1 + Matrix.single i j a) *
        ((A⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4) =
      (1 + Matrix.single k l b : Matrix (Fin 3) (Fin 3) F4)) :
    (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single i j a =
      Matrix.single k l b * (A : Matrix (Fin 3) (Fin 3) F4) := by
  have hA' : ((A⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) F4) *
      (A : Matrix (Fin 3) (Fin 3) F4) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : (A : Matrix (Fin 3) (Fin 3) F4) * (1 + Matrix.single i j a) =
      (1 + Matrix.single k l b : Matrix (Fin 3) (Fin 3) F4) *
        (A : Matrix (Fin 3) (Fin 3) F4) := by
    have h' := congrArg (fun M : Matrix (Fin 3) (Fin 3) F4 => M * (A : Matrix (Fin 3) (Fin 3) F4)) h
    simpa only [Matrix.mul_assoc, hA', Matrix.mul_one] using h'
  have h2 : (A : Matrix (Fin 3) (Fin 3) F4) +
      (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single i j a =
      (A : Matrix (Fin 3) (Fin 3) F4) +
        Matrix.single k l b * (A : Matrix (Fin 3) (Fin 3) F4) := by
    simpa only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] using h1
  exact add_left_cancel h2

private theorem trace_one_add_single {i j : Fin 3} {a : F4} (hij : i ≠ j) :
    ((1 + Matrix.single i j a : Matrix (Fin 3) (Fin 3) F4)).trace = 1 := by
  rw [Matrix.trace_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp_all [Matrix.add_apply]
  all_goals
    apply F4.codeEquiv.injective
    decide

private theorem graph_single_eq {A : GL3} {g h : SL3} {i j k l : Fin 3} {a b : F4}
    (hij : i ≠ j) (hkl : k ≠ l)
    (hfixg : (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4)
      (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g)
    (hgh : (g⁻¹).transpose = h)
    (hg : (g : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single k l b)
    (hh : (h : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single i j a) :
    (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single i j a =
      Matrix.single k l b * (A : Matrix (Fin 3) (Fin 3) F4) := by
  obtain ⟨c, hc, hmat⟩ := graph_fix_matrix hfixg
  rw [hgh, hh, hg] at hmat
  have hc1 : (c : F4) = 1 := by
    have ht := congrArg Matrix.trace hmat
    rw [Matrix.trace_units_conj A, Matrix.trace_smul, trace_one_add_single hij,
      trace_one_add_single hkl] at ht
    simpa using ht.symm
  rw [show (c : F4) = 1 from hc1, one_smul] at hmat
  exact mul_single_eq_single_mul hmat

private theorem t01_mem : t01 ∈ LinearFlag.unitriangular 3 F4 :=
  LinearFlag.transvection_mem_unitriangular (by decide : (0 : Fin 3) < 1) 1

private theorem t12_mem : t12 ∈ LinearFlag.unitriangular 3 F4 :=
  LinearFlag.transvection_mem_unitriangular (by decide : (1 : Fin 3) < 2) 1

private theorem t02_mem : t02 ∈ LinearFlag.unitriangular 3 F4 :=
  LinearFlag.transvection_mem_unitriangular (by decide : (0 : Fin 3) < 2) 1

private theorem t01ω_mem : t01ω ∈ LinearFlag.unitriangular 3 F4 :=
  LinearFlag.transvection_mem_unitriangular (by decide : (0 : Fin 3) < 1) F4.ω

private theorem mul_single_entry_zero {A : GL3} {i j k l : Fin 3} {a b : F4}
    (h : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single i j a =
      Matrix.single k l b * (A : Matrix (Fin 3) (Fin 3) F4))
    (p : Fin 3) (hp : p ≠ k) : (A : Matrix (Fin 3) (Fin 3) F4) p i * a = 0 := by
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) F4 => M p j) h
  rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne (h := hp)] at hh
  simpa using hh

private theorem not_graph_fixes_U3 (A : GL3) :
    ¬ (∀ x ∈ U3, (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4) x = x) := by
  intro hfix
  have hfixg (g : SL3) (hg : g ∈ LinearFlag.unitriangular 3 F4) :
      (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4)
        (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g :=
    hfix (LinearFlag.proj 3 F4 g) (proj_mem_U3 hg)
  have hs1 : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 1 0 1 =
      Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4) :=
    graph_single_eq (A := A) (g := t01) (h := t10) (i := 1) (j := 0) (k := 0) (l := 1)
      (a := 1) (b := 1) (by decide) (by decide) (hfixg t01 t01_mem)
      t01_inv_transpose coe_t01 coe_t10
  have hs2 : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 2 1 1 =
      Matrix.single 1 2 1 * (A : Matrix (Fin 3) (Fin 3) F4) :=
    graph_single_eq (A := A) (g := t12) (h := t21) (i := 2) (j := 1) (k := 1) (l := 2)
      (a := 1) (b := 1) (by decide) (by decide) (hfixg t12 t12_mem)
      t12_inv_transpose coe_t12 coe_t21
  have hs3 : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 2 0 1 =
      Matrix.single 0 2 1 * (A : Matrix (Fin 3) (Fin 3) F4) :=
    graph_single_eq (A := A) (g := t02) (h := t20) (i := 2) (j := 0) (k := 0) (l := 2)
      (a := 1) (b := 1) (by decide) (by decide) (hfixg t02 t02_mem)
      t02_inv_transpose coe_t02 coe_t20
  have hA02 : (A : Matrix (Fin 3) (Fin 3) F4) 0 2 = 0 := by
    have h := mul_single_entry_zero hs2 0 (by decide : (0 : Fin 3) ≠ 1)
    simpa using h
  have hA12 : (A : Matrix (Fin 3) (Fin 3) F4) 1 2 = 0 := by
    have h := mul_single_entry_zero hs3 1 (by decide : (1 : Fin 3) ≠ 0)
    simpa using h
  have hA22 : (A : Matrix (Fin 3) (Fin 3) F4) 2 2 = 0 := by
    have h := mul_single_entry_zero hs2 2 (by decide : (2 : Fin 3) ≠ 1)
    simpa using h
  have hcol : (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ (Pi.single (2 : Fin 3) (1 : F4) : Vec) = 0 := by
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [hA02, hA12, hA22]
  have hne : (Pi.single (2 : Fin 3) (1 : F4) : Vec) ≠ 0 := by
    intro h
    have := congrFun h 2
    simp at this
  exact mulVec_ne_zero A hne hcol

private theorem coe_map_frob_t01 :
    (SpecialLinearGroup.map frob.toRingHom t01 : Matrix (Fin 3) (Fin 3) F4) =
      1 + Matrix.single 0 1 1 := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_t01, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.add_apply, frob_apply]

private theorem coe_map_frob_t01ω :
    (SpecialLinearGroup.map frob.toRingHom t01ω : Matrix (Fin 3) (Fin 3) F4) =
      1 + Matrix.single 0 1 (frob F4.ω) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_t01ω, RingHom.mapMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Matrix.add_apply, frob_apply]

private theorem frob_omega_add_omega : frob F4.ω + F4.ω = 1 := by
  rw [frob_apply, pow_two]
  apply F4.codeEquiv.injective
  decide

private theorem omega_add_self : F4.ω + F4.ω = 0 := by
  apply F4.codeEquiv.injective
  decide

private theorem single_scalar (a : F4) :
    (Matrix.single 0 1 a : Matrix (Fin 3) (Fin 3) F4) =
      a • Matrix.single 0 1 1 := by
  rw [Matrix.smul_single]
  simp

private theorem field_single_eq {A : GL3} {g : SL3} {i j : Fin 3} {a b : F4}
    (hij : i ≠ j)
    (hfixg : (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob)
      (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g)
    (hg : (g : Matrix (Fin 3) (Fin 3) F4) = 1 + Matrix.single i j b)
    (hG : (SpecialLinearGroup.map frob.toRingHom g : Matrix (Fin 3) (Fin 3) F4) =
      1 + Matrix.single i j a) :
    (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single i j a =
      Matrix.single i j b * (A : Matrix (Fin 3) (Fin 3) F4) := by
  obtain ⟨c, hc, hmat⟩ := field_fix_matrix hfixg
  rw [hG, hg] at hmat
  have hc1 : (c : F4) = 1 := by
    have ht := congrArg Matrix.trace hmat
    rw [Matrix.trace_units_conj A, Matrix.trace_smul, trace_one_add_single hij,
      trace_one_add_single hij] at ht
    simpa using ht.symm
  rw [show (c : F4) = 1 from hc1, one_smul] at hmat
  exact mul_single_eq_single_mul hmat

private theorem not_field_fixes_U3 (A : GL3) :
    ¬ (∀ x ∈ U3, (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob) x = x) := by
  intro hfix
  have hfixg (g : SL3) (hg : g ∈ LinearFlag.unitriangular 3 F4) :
      (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob)
        (LinearFlag.proj 3 F4 g) = LinearFlag.proj 3 F4 g :=
    hfix (LinearFlag.proj 3 F4 g) (proj_mem_U3 hg)
  have hs1 : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 0 1 1 =
      Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4) :=
    field_single_eq (A := A) (g := t01) (i := 0) (j := 1) (a := 1) (b := 1) (by decide)
      (hfixg t01 t01_mem) coe_t01 coe_map_frob_t01
  have hs2 : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 0 1 (frob F4.ω) =
      Matrix.single 0 1 F4.ω * (A : Matrix (Fin 3) (Fin 3) F4) :=
    field_single_eq (A := A) (g := t01ω) (i := 0) (j := 1) (a := frob F4.ω) (b := F4.ω)
      (by decide) (hfixg t01ω t01ω_mem) coe_t01ω coe_map_frob_t01ω
  have h2 : frob F4.ω • ((A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 0 1 1) =
      F4.ω • (Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4)) := by
    rw [single_scalar (frob F4.ω), single_scalar F4.ω] at hs2
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hs2
  have h3 : frob F4.ω • (Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4)) =
      F4.ω • (Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4)) := by
    simpa only [hs1] using h2
  have hX : (Matrix.single 0 1 1 : Matrix (Fin 3) (Fin 3) F4) *
      (A : Matrix (Fin 3) (Fin 3) F4) = 0 := by
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F4 =>
      M + F4.ω • (Matrix.single 0 1 1 * (A : Matrix (Fin 3) (Fin 3) F4))) h3
    rw [← add_smul, frob_omega_add_omega, one_smul, ← add_smul, omega_add_self,
      zero_smul] at h
    exact h
  have hAE : (A : Matrix (Fin 3) (Fin 3) F4) * Matrix.single 0 1 1 = 0 := by
    rw [hs1, hX]
  have hcol : (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ (Pi.single (0 : Fin 3) (1 : F4) : Vec) = 0 := by
    rw [Matrix.mulVec_single_one]
    ext i
    have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) F4 => M i 1) hAE
    rw [Matrix.mul_single_apply_same, Matrix.zero_apply] at h
    simpa using h
  have hne : (Pi.single (0 : Fin 3) (1 : F4) : Vec) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  exact mulVec_ne_zero A hne hcol

private theorem toGL_slFieldAut (g : SL3) :
    Matrix.SpecialLinearGroup.toGL (CatalogueBHigherLinearField.slFieldAut (Fin 3) F4 frob g) =
      CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob (Matrix.SpecialLinearGroup.toGL g) :=
  CatalogueBHigherLinearField.toGL_slFieldEquiv (Fin 3) frob g

private theorem slGraphAut_slConjugation (B : GL3) :
    CatalogueBGraphForm.slGraphAut 3 F4 * CatalogueBHigherLinearAction.slConjugation 3 F4 B =
      CatalogueBHigherLinearAction.slConjugation 3 F4
        (CatalogueBGraphForm.glGraphAut 3 F4 B) * CatalogueBGraphForm.slGraphAut 3 F4 := by
  apply MulEquiv.ext
  intro g
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
    CatalogueBGraphForm.toGL_slGraphAut]
  rw [map_mul, map_mul, map_inv]

private theorem slFieldAut_slConjugation (B : GL3) :
    CatalogueBHigherLinearField.slFieldAut (Fin 3) F4 frob *
        CatalogueBHigherLinearAction.slConjugation 3 F4 B =
      CatalogueBHigherLinearAction.slConjugation 3 F4
        (CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) *
        CatalogueBHigherLinearField.slFieldAut (Fin 3) F4 frob := by
  apply MulEquiv.ext
  intro g
  apply Matrix.SpecialLinearGroup.toGL_injective
  simp only [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation, toGL_slFieldAut]
  rw [map_mul, map_mul, map_inv]

private theorem conjAut_graph_conjAut (B A : GL3) :
    LinearFlag.conjAut 3 F4 B⁻¹ *
        (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4) *
        LinearFlag.conjAut 3 F4 B =
      LinearFlag.conjAut 3 F4 (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B) *
        LinearFlag.dualAut 3 F4 := by
  let D := LinearFlag.descendAut 3 F4
  let sc := CatalogueBHigherLinearAction.slConjugation 3 F4
  let gr := CatalogueBGraphForm.slGraphAut 3 F4
  have hSL : sc B⁻¹ * (sc A * gr) * sc B =
      sc (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B) * gr := by
    calc
      sc B⁻¹ * (sc A * gr) * sc B = sc B⁻¹ * sc A * (gr * sc B) := by group
      _ = sc B⁻¹ * sc A * (sc (CatalogueBGraphForm.glGraphAut 3 F4 B) * gr) := by
            rw [slGraphAut_slConjugation]
      _ = sc (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B) * gr := by
            rw [map_mul, map_mul, map_inv]
            group
  change D (sc B⁻¹) * (D (sc A) * D gr) * D (sc B) =
    D (sc (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B)) * D gr
  calc
    D (sc B⁻¹) * (D (sc A) * D gr) * D (sc B)
        = D (sc B⁻¹ * (sc A * gr) * sc B) := by simp [map_mul]
    _ = D (sc (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B) * gr) := by rw [hSL]
    _ = D (sc (B⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B)) * D gr := by simp [map_mul]

private theorem conjAut_field_conjAut (B A : GL3) :
    LinearFlag.conjAut 3 F4 B⁻¹ *
        (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob) *
        LinearFlag.conjAut 3 F4 B =
      LinearFlag.conjAut 3 F4
          (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) *
        LinearFlag.fieldAut 3 F4 frob := by
  let D := LinearFlag.descendAut 3 F4
  let sc := CatalogueBHigherLinearAction.slConjugation 3 F4
  let fa := CatalogueBHigherLinearField.slFieldAut (Fin 3) F4 frob
  have hSL : sc B⁻¹ * (sc A * fa) * sc B =
      sc (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) * fa := by
    calc
      sc B⁻¹ * (sc A * fa) * sc B = sc B⁻¹ * sc A * (fa * sc B) := by group
      _ = sc B⁻¹ * sc A *
            (sc (CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) * fa) := by
            rw [slFieldAut_slConjugation]
      _ = sc (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) * fa := by
            rw [map_mul, map_mul, map_inv]
            group
  change D (sc B⁻¹) * (D (sc A) * D fa) * D (sc B) =
    D (sc (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B)) * D fa
  calc
    D (sc B⁻¹) * (D (sc A) * D fa) * D (sc B)
        = D (sc B⁻¹ * (sc A * fa) * sc B) := by simp [map_mul]
    _ = D (sc (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B) * fa) := by
          rw [hSL]
    _ = D (sc (B⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B)) * D fa := by
          simp [map_mul]

private theorem mulAut_conj_proj (B : SL3) :
    MulAut.conj (LinearFlag.proj 3 F4 B) = LinearFlag.conjAut 3 F4 (B : GL3) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := LinearFlag.proj_surjective 3 F4 x
  rw [MulAut.conj_apply, LinearFlag.conjAut_proj, ← map_inv]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  simp [map_mul, map_inv]

private theorem conj_fixes_of_fixes {U V : Subgroup G3} {φ : MulAut G3} {g : G3}
    (hUV : U = V.map (MulAut.conj g).toMonoidHom)
    (hfix : ∀ x ∈ U, φ x = x) :
    ∀ x ∈ V, ((MulAut.conj g)⁻¹ * φ * MulAut.conj g) x = x := by
  intro x hx
  have hxU : MulAut.conj g x ∈ U := by
    rw [hUV]
    exact Subgroup.mem_map_of_mem _ hx
  have h := hfix _ hxU
  rw [MulAut.mul_apply, MulAut.mul_apply]
  rw [h]
  exact MulEquiv.symm_apply_apply (MulAut.conj g) x

theorem false_of_graph_or_field_fixes_sylow (U : Sylow 2 (LinearFlag.projectiveSL 3 F4))
    (A : GL (Fin 3) F4)
    (h : (∀ x ∈ (U : Subgroup (LinearFlag.projectiveSL 3 F4)),
          (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4) x = x) ∨
        (∀ x ∈ (U : Subgroup (LinearFlag.projectiveSL 3 F4)),
          (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob) x = x)) :
    False := by
  obtain ⟨P, hP⟩ := LinearFlag.exists_sylow_projUnitriangular (K := F4) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G3 P U
  have hU0 : (U : Subgroup G3) = U3.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, hP]
    ext y
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    exact ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h⟩⟩
  obtain ⟨B, rfl⟩ := LinearFlag.proj_surjective 3 F4 g
  let B' : GL3 := (B : GL3)
  have hconj : MulAut.conj (LinearFlag.proj 3 F4 B) = LinearFlag.conjAut 3 F4 B' :=
    mulAut_conj_proj B
  rcases h with hgraph | hfield
  · let A' : GL3 := B'⁻¹ * A * CatalogueBGraphForm.glGraphAut 3 F4 B'
    have hfixψ : ∀ x ∈ U3,
        ((MulAut.conj (LinearFlag.proj 3 F4 B))⁻¹ *
          (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4) *
          MulAut.conj (LinearFlag.proj 3 F4 B)) x = x :=
      conj_fixes_of_fixes hU0 hgraph
    have hshape : (MulAut.conj (LinearFlag.proj 3 F4 B))⁻¹ *
        (LinearFlag.conjAut 3 F4 A * LinearFlag.dualAut 3 F4) *
        MulAut.conj (LinearFlag.proj 3 F4 B) =
        LinearFlag.conjAut 3 F4 A' * LinearFlag.dualAut 3 F4 := by
      rw [hconj, ← map_inv, conjAut_graph_conjAut B' A]
    have hfix : ∀ x ∈ U3,
        (LinearFlag.conjAut 3 F4 A' * LinearFlag.dualAut 3 F4) x = x := by
      intro x hx
      have hx' := hfixψ x hx
      rwa [hshape] at hx'
    exact not_graph_fixes_U3 A' hfix
  · let A' : GL3 := B'⁻¹ * A * CatalogueBHigherLinearField.glFieldAut (Fin 3) F4 frob B'
    have hfixψ : ∀ x ∈ U3,
        ((MulAut.conj (LinearFlag.proj 3 F4 B))⁻¹ *
          (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob) *
          MulAut.conj (LinearFlag.proj 3 F4 B)) x = x :=
      conj_fixes_of_fixes hU0 hfield
    have hshape : (MulAut.conj (LinearFlag.proj 3 F4 B))⁻¹ *
        (LinearFlag.conjAut 3 F4 A * LinearFlag.fieldAut 3 F4 frob) *
        MulAut.conj (LinearFlag.proj 3 F4 B) =
        LinearFlag.conjAut 3 F4 A' * LinearFlag.fieldAut 3 F4 frob := by
      rw [hconj, ← map_inv, conjAut_field_conjAut B' A]
    have hfix : ∀ x ∈ U3,
        (LinearFlag.conjAut 3 F4 A' * LinearFlag.fieldAut 3 F4 frob) x = x := by
      intro x hx
      have hx' := hfixψ x hx
      rwa [hshape] at hx'
    exact not_field_fixes_U3 A' hfix

end CFSG.ComponentClassification.PSL3Four
