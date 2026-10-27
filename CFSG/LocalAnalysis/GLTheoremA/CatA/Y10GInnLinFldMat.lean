module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

open CFSG.Open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.HeldLang
open CFSG.HardMathSupport.Foote.ModuleExclusions

variable {K : Type} [Field K]

def fin0 {d : ℕ} (hd : 3 ≤ d) : Fin d := ⟨0, by omega⟩

def fin1 {d : ℕ} (hd : 3 ≤ d) : Fin d := ⟨1, by omega⟩

theorem fin0_ne_fin1 {d : ℕ} (hd : 3 ≤ d) : fin0 hd ≠ fin1 hd := by
  intro h
  have := congrArg Fin.val h
  simp [fin0, fin1] at this

noncomputable def transvGL {d : ℕ} (hd : 3 ≤ d) (b : K) : GL (Fin d) K :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection (fin0_ne_fin1 hd) b)

theorem transvGL_mem {d : ℕ} (hd : 3 ≤ d) (b : K) : transvGL hd b ∈ slGL (Fin d) K := by
  rw [mem_slGL]
  exact (Matrix.SpecialLinearGroup.transvection (fin0_ne_fin1 hd) b).2

theorem transvGL_entry {d : ℕ} (hd : 3 ≤ d) (b : K) (i j : Fin d) :
    ((transvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j =
      (1 : Matrix (Fin d) (Fin d) K) i j + Matrix.single (fin0 hd) (fin1 hd) b i j := by
  rw [transvGL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_apply]

theorem conj_data {d : ℕ} (u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) :
    ∃ A : GL (Fin d) K, ∀ x : ↥(slGL (Fin d) K), ∃ y : ↥(slGL (Fin d) K),
      (y : GL (Fin d) K) = A * (x : GL (Fin d) K) * A⁻¹ ∧
        u (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) = LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y := by
  obtain ⟨A, -, huA⟩ := hu
  exact ⟨A, fun x => ⟨⟨A * (x : GL (Fin d) K) * A⁻¹, conj_mem_slGL A x.2⟩, rfl, huA x _ rfl⟩⟩

theorem field_data {d : ℕ} (f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :
    ∃ σ : K ≃+* K, ∀ x : ↥(slGL (Fin d) K), ∃ y : ↥(slGL (Fin d) K),
      (y : GL (Fin d) K) = glMap σ (x : GL (Fin d) K) ∧
        f (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) = LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y := by
  obtain ⟨σ, hfσ⟩ := hf
  refine ⟨σ, fun x => ?_⟩
  have hmem : glMap σ (x : GL (Fin d) K) ∈ slGL (Fin d) K := by
    rw [mem_slGL, det_glMap, (mem_slGL.1 x.2), map_one]
  exact ⟨⟨glMap σ (x : GL (Fin d) K), hmem⟩, rfl, hfσ x _ rfl⟩

theorem fieldAct_iter {d : ℕ} (σ : K ≃+* K)
    (f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hf1 : ∀ x : ↥(slGL (Fin d) K), ∃ y : ↥(slGL (Fin d) K),
      (y : GL (Fin d) K) = glMap σ (x : GL (Fin d) K) ∧
        f (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) = LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y)
    (k : ℕ) (x : ↥(slGL (Fin d) K)) :
    ∃ y : ↥(slGL (Fin d) K), (y : GL (Fin d) K) = glMap (σ ^ k) (x : GL (Fin d) K) ∧
      (f ^ k) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) y := by
  induction k generalizing x with
  | zero => exact ⟨x, by rw [pow_zero, glMap_one], by rw [pow_zero, MulAut.one_apply]⟩
  | succ k ih =>
    obtain ⟨y, hy1, hy2⟩ := ih x
    obtain ⟨z, hz1, hz2⟩ := hf1 y
    refine ⟨z, ?_, ?_⟩
    · rw [hz1, hy1, glMap_pow_succ]
    · rw [pow_succ', MulAut.mul_apply, hy2, hz2]

theorem uf_structure {d : ℕ} (hd : 3 ≤ d)
    (u f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K)))
    (hu : u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)))
    (hf3 : f ^ 3 = 1) (huf3 : (u * f) ^ 3 = 1) (hfne : f ≠ 1) :
    ∃ (A : GL (Fin d) K) (σ : K ≃+* K) (c : K), orderOf σ = 3 ∧
      Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K) ∧
      ∀ x : ↥(slGL (Fin d) K),
        (u * f) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
          LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x) := by
  obtain ⟨A, hu1⟩ := conj_data u hu
  obtain ⟨σ, hf1⟩ := field_data f hf
  have hσ3 : σ ^ 3 = 1 := by
    have hent : ∀ b : K, (σ ^ 3) b = b := by
      intro b
      have htm : transvGL hd b ∈ slGL (Fin d) K := transvGL_mem hd b
      obtain ⟨y, hy1, hy2⟩ := fieldAct_iter σ f hf1 3 ⟨transvGL hd b, htm⟩
      rw [hf3, MulAut.one_apply] at hy2
      obtain ⟨c, hc⟩ := mk_eq_scalar _ _ hy2
      have hy1' : (y : GL (Fin d) K) = glMap (σ ^ 3) (transvGL hd b) := hy1
      have hyc : glMap (σ ^ 3) (transvGL hd b) =
          Matrix.GeneralLinearGroup.scalar (Fin d) c * transvGL hd b := by
        rw [← hy1']
        exact hc
      have hmat : ∀ i j, (σ ^ 3) (((transvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j) =
          (c : K) * ((transvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j := by
        intro i j
        have h := congrArg (fun z : GL (Fin d) K => ((z : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j) hyc
        simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_mul,
          coe_glMap] using h
      have ht00 : ((transvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (fin0 hd) (fin0 hd) = 1 := by
        rw [transvGL_entry]
        simp [Matrix.single_apply, fin0_ne_fin1 hd, (fin0_ne_fin1 hd).symm]
      have ht01 : ((transvGL hd b : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (fin0 hd) (fin1 hd) = b := by
        rw [transvGL_entry]
        simp [Matrix.single_apply, fin0_ne_fin1 hd, (fin0_ne_fin1 hd).symm]
      have hc1 : (c : K) = 1 := by
        have h := hmat (fin0 hd) (fin0 hd)
        rw [ht00, map_one, mul_one] at h
        exact h.symm
      have h01 := hmat (fin0 hd) (fin1 hd)
      rw [ht01, hc1, one_mul] at h01
      exact h01
    exact RingEquiv.ext hent
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hfne
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨z, hz1, hz2⟩ := hf1 x
    have hzx : z = x := Subtype.ext (by rw [hz1, h1, glMap_one])
    rw [hz2, hzx, MulAut.one_apply]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hstep : ∀ x : ↥(slGL (Fin d) K),
      (u * f) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) (slTwist σ A x) := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hf1 x
    obtain ⟨z, hz1, hz2⟩ := hu1 y
    rw [MulAut.mul_apply, hy2, hz2]
    exact congrArg (fun w => LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) w)
      (Subtype.ext (by rw [hz1, hy1, coe_slTwist]))
  have hiter : ∀ (k : ℕ) (x : ↥(slGL (Fin d) K)),
      ((u * f) ^ k) (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) x) =
        LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) ((slTwist σ A)^[k] x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, ih x, hstep, Function.iterate_succ_apply']
  have hN : ∀ x ∈ slGL (Fin d) K, ∃ c : Kˣ,
      normProd σ A 3 * x * (normProd σ A 3)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) c * x := by
    intro x hx
    have h3 := hiter 3 ⟨x, hx⟩
    rw [huf3, MulAut.one_apply] at h3
    obtain ⟨c, hc⟩ := mk_eq_scalar ((slTwist σ A)^[3] ⟨x, hx⟩) ⟨x, hx⟩ h3.symm
    refine ⟨c⁻¹, ?_⟩
    have hc' : (x : GL (Fin d) K) = Matrix.GeneralLinearGroup.scalar (Fin d) c *
        (normProd σ A 3 * glMap (σ ^ 3) (x : GL (Fin d) K) * (normProd σ A 3)⁻¹) := by
      have h := hc
      rw [coe_iterate_slTwist] at h
      exact h
    rw [hσ3, glMap_one] at hc'
    calc normProd σ A 3 * x * (normProd σ A 3)⁻¹
        = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ *
            (Matrix.GeneralLinearGroup.scalar (Fin d) c * (normProd σ A 3 * x * (normProd σ A 3)⁻¹)) := by
          group
      _ = (Matrix.GeneralLinearGroup.scalar (Fin d) c)⁻¹ * x := by rw [← hc']
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) c⁻¹ * x := by rw [map_inv]
  obtain ⟨c, hc⟩ := exists_scalar_of_conj_mod_scalar hd (normProd σ A 3) hN
  have hAi : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = ((c : Kˣ) : K) • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hσord, ← coe_normProd, hc, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  exact ⟨A, σ, (c : K), hσord, hAi, hstep⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld

end
