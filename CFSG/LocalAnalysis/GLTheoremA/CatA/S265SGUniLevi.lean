module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {d : ℕ}

private def cT {m l : Type} (σ : K ≃+* K) (A : Matrix m l K) : Matrix l m K := (A.map σ)ᵀ

private theorem cT_mul {m l o : Type} [Fintype l] (A : Matrix m l K) (B : Matrix l o K) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

private theorem cT_cT (hσ : ∀ c, σ (σ c) = c) {m l : Type} (A : Matrix m l K) :
    cT σ (cT σ A) = A := by
  ext i j
  simp [cT, hσ]

private theorem cT_smul {m l : Type} (c : K) (A : Matrix m l K) :
    cT σ (c • A) = σ c • cT σ A := by
  ext i j
  simp [cT]

private theorem cT_one {m : Type} [DecidableEq m] : cT σ (1 : Matrix m m K) = 1 := by
  simp [cT]

private theorem det_cT {m : ℕ} (A : Matrix (Fin m) (Fin m) K) : (cT σ A).det = σ A.det :=
  (Matrix.det_transpose _).trans (RingHom.map_det (σ : K →+* K) A).symm

private structure LeviData (σ : K ≃+* K) (U W : Matrix (Fin d) (Fin 2) K) : Prop where
  wu : cT σ W * U = 1
  uw : cT σ U * W = 1
  uu : cT σ U * U = 0
  ww : cT σ W * W = 0

private theorem sand {A B : Matrix (Fin d) (Fin 2) K} {C : Matrix (Fin 2) (Fin 2) K}
    (h : cT σ A * B = C) {l : Type} (X : Matrix (Fin 2) l K) : cT σ A * (B * X) = C * X := by
  rw [← Matrix.mul_assoc, h]

private def lv (σ : K ≃+* K) (U W : Matrix (Fin d) (Fin 2) K) (M N : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin d) (Fin d) K :=
  1 - U * cT σ W - W * cT σ U + U * M * cT σ W + W * N * cT σ U

private theorem lv_mul {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M N M' N' : Matrix (Fin 2) (Fin 2) K) :
    lv σ U W M N * lv σ U W M' N' = lv σ U W (M * M') (N * N') := by
  simp only [lv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, sand h.wu, sand h.uw, sand h.uu, sand h.ww,
    Matrix.mul_zero, Matrix.zero_mul]
  abel

private theorem cT_lv {U W : Matrix (Fin d) (Fin 2) K} (hσ : ∀ c, σ (σ c) = c)
    (M N : Matrix (Fin 2) (Fin 2) K) : cT σ (lv σ U W M N) = lv σ U W (cT σ N) (cT σ M) := by
  have e : ∀ A B : Matrix (Fin d) (Fin d) K, cT σ (A + B) = cT σ A + cT σ B := fun A B => by
    ext; simp [cT]
  have e' : ∀ A B : Matrix (Fin d) (Fin d) K, cT σ (A - B) = cT σ A - cT σ B := fun A B => by
    ext; simp [cT]
  simp only [lv, e, e', cT_one, cT_mul, cT_cT hσ, Matrix.mul_assoc]
  abel

private theorem det_lv {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M N : Matrix (Fin 2) (Fin 2) K) : (lv σ U W M N).det = M.det * N.det := by
  have e : lv σ U W M N = (1 + U * ((M - 1) * cT σ W)) * (1 + W * ((N - 1) * cT σ U)) := by
    simp only [lv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, sand h.ww, Matrix.zero_mul]
    abel
  rw [e, Matrix.det_mul, Matrix.det_one_add_mul_comm U ((M - 1) * cT σ W),
    Matrix.det_one_add_mul_comm W ((N - 1) * cT σ U)]
  simp [Matrix.mul_assoc, h.wu, h.uw]

private theorem lv_mul_U {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M N : Matrix (Fin 2) (Fin 2) K) : lv σ U W M N * U = U * M := by
  simp only [lv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h.wu, h.uu, Matrix.mul_zero, Matrix.zero_mul]
  abel

private theorem lv_mulVec {U W : Matrix (Fin d) (Fin 2) K} (M N : Matrix (Fin 2) (Fin 2) K)
    {z : Fin d → K} (hU : cT σ U *ᵥ z = 0) (hW : cT σ W *ᵥ z = 0) : lv σ U W M N *ᵥ z = z := by
  simp only [lv, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    hU, hW, Matrix.mulVec_zero, Matrix.one_mulVec, sub_zero, add_zero]

private theorem lv_comm {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (hσ : ∀ c, σ (σ c) = c) {G : Matrix (Fin d) (Fin d) K} {a : K} (hG : cT σ G * G = 1)
    (hU : G * U = a • U) (hW : G * W = a⁻¹ • W) (M N : Matrix (Fin 2) (Fin 2) K) :
    G * lv σ U W M N = lv σ U W M N * G := by
  have hs : ∀ {l : Type} (X : Matrix (Fin d) l K), cT σ G * (G * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hG, Matrix.one_mul]
  have h1 : (σ a⁻¹ * a) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have e : cT σ (G * W) * (G * U) = cT σ W * U := by rw [cT_mul, Matrix.mul_assoc, hs]
    rwa [hU, hW, cT_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.wu] at e
  have h2 : σ a⁻¹ * a = 1 := by simpa using congrFun (congrFun h1 0) 0
  have ha : a ≠ 0 := fun h0 => by simp [h0] at h2
  have hsa : σ a = a := by
    rw [map_inv₀] at h2
    exact (inv_mul_eq_one₀ ((map_ne_zero σ).2 ha)).1 h2
  have hA : cT σ G * U = a⁻¹ • U := by
    have e := hs U
    rw [hU, Matrix.mul_smul] at e
    exact (eq_inv_smul_iff₀ ha).2 e
  have hB : cT σ G * W = a • W := by
    have e := hs W
    rw [hW, Matrix.mul_smul] at e
    simpa using (eq_inv_smul_iff₀ (inv_ne_zero ha)).2 e
  have hWG : cT σ W * G = a • cT σ W :=
    calc cT σ W * G = cT σ (cT σ G * W) := by rw [cT_mul, cT_cT hσ]
      _ = cT σ (a • W) := by rw [hB]
      _ = a • cT σ W := by rw [cT_smul, hsa]
  have hUG : cT σ U * G = a⁻¹ • cT σ U :=
    calc cT σ U * G = cT σ (cT σ G * U) := by rw [cT_mul, cT_cT hσ]
      _ = cT σ (a⁻¹ • U) := by rw [hA]
      _ = a⁻¹ • cT σ U := by rw [cT_smul, map_inv₀, hsa]
  have hGU : ∀ {l : Type} (X : Matrix (Fin 2) l K), G * (U * X) = a • (U * X) := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.smul_mul]
  have hGW : ∀ {l : Type} (X : Matrix (Fin 2) l K), G * (W * X) = a⁻¹ • (W * X) := fun X => by
    rw [← Matrix.mul_assoc, hW, Matrix.smul_mul]
  simp only [lv, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, hGU, hGW, hWG, hUG, Matrix.mul_smul]

private def levi (σ : K ≃+* K) (U W : Matrix (Fin d) (Fin 2) K)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin d) (Fin d) K :=
  lv σ U W (M : Matrix (Fin 2) (Fin 2) K)
    (cT σ ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))

private theorem levi_one {U W : Matrix (Fin d) (Fin 2) K} : levi σ U W 1 = 1 := by
  simp only [levi, lv, _root_.inv_one, Matrix.SpecialLinearGroup.coe_one, cT_one, Matrix.mul_one]
  abel

private theorem levi_mul {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M M' : Matrix.SpecialLinearGroup (Fin 2) K) :
    levi σ U W M * levi σ U W M' = levi σ U W (M * M') := by
  simp only [levi, lv_mul h, _root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, cT_mul]

private theorem det_levi {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : (levi σ U W M).det = 1 := by
  rw [levi, det_lv h, det_cT, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
    map_one, one_mul]

private theorem levi_mul_U {U W : Matrix (Fin d) (Fin 2) K} (h : LeviData σ U W)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    levi σ U W M * U = U * (M : Matrix (Fin 2) (Fin 2) K) :=
  lv_mul_U h _ _

private theorem conjTr_levi_mul {U W : Matrix (Fin d) (Fin 2) K} (hσ : ∀ c, σ (σ c) = c)
    (h : LeviData σ U W) (M : Matrix.SpecialLinearGroup (Fin 2) K) :
    conjTr σ (levi σ U W M) * levi σ U W M = 1 := by
  have e : cT σ (levi σ U W M) = levi σ U W M⁻¹ := by
    simp only [levi, cT_lv hσ, cT_cT hσ, inv_inv]
  change cT σ (levi σ U W M) * levi σ U W M = 1
  rw [e, levi_mul h, inv_mul_cancel, levi_one]

private noncomputable def leviSU {U W : Matrix (Fin d) (Fin 2) K} (hσ : ∀ c, σ (σ c) = c)
    (h : LeviData σ U W) (M : Matrix.SpecialLinearGroup (Fin 2) K) : SUid σ d :=
  mkSU σ (levi σ U W M) (det_levi h M) fun v w => by
    rw [herm_mulVec, conjTr_levi_mul hσ h M, Matrix.one_mulVec]

private theorem leviSU_mul {U W : Matrix (Fin d) (Fin 2) K} (hσ : ∀ c, σ (σ c) = c)
    (h : LeviData σ U W) (M M' : Matrix.SpecialLinearGroup (Fin 2) K) :
    leviSU hσ h (M * M') = leviSU hσ h M * leviSU hσ h M' :=
  ext_smul σ fun v => by
    rw [mul_smul]
    change levi σ U W (M * M') *ᵥ v = levi σ U W M *ᵥ (levi σ U W M' *ᵥ v)
    rw [Matrix.mulVec_mulVec, levi_mul h]

private theorem leviSU_injective {U W : Matrix (Fin d) (Fin 2) K} (hσ : ∀ c, σ (σ c) = c)
    (h : LeviData σ U W) : Function.Injective (leviSU hσ h) := by
  intro M M' hMM'
  have h1 : levi σ U W M = levi σ U W M' :=
    congrArg (fun g : SUid σ d => (g : GL (Fin d) K).val) hMM'
  have h2 := levi_mul_U h M
  rw [h1, levi_mul_U h M'] at h2
  refine Subtype.ext ?_
  have h3 := congrArg (fun A => cT σ W * A) h2
  simpa only [← Matrix.mul_assoc, h.wu, Matrix.one_mul] using h3.symm

private theorem cT_mul_of (a b : Fin 2 → Fin d → K) (i j : Fin 2) :
    (cT σ (Matrix.of fun r i => a i r) * Matrix.of fun r i => b i r) i j =
      herm σ (a i) (b j) := by
  simp [cT, Matrix.mul_apply, herm]

private theorem cT_mulVec_of (a : Fin 2 → Fin d → K) (z : Fin d → K) (i : Fin 2) :
    (cT σ (Matrix.of fun r i => a i r) *ᵥ z) i = herm σ (a i) z := by
  simp [cT, Matrix.mulVec, dotProduct, herm]

private theorem mul_of_eq_smul (G : Matrix (Fin d) (Fin d) K) (a : K) (x : Fin 2 → Fin d → K)
    (hx : ∀ i, G *ᵥ x i = a • x i) :
    G * (Matrix.of fun r i => x i r) = a • Matrix.of fun r i => x i r := by
  ext r i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun (hx i) r

private theorem leviData_of (hσ : ∀ c, σ (σ c) = c) {x y : Fin 2 → Fin d → K}
    (hxx : ∀ i j, herm σ (x i) (x j) = 0) (hyy : ∀ i j, herm σ (y i) (y j) = 0)
    (hxy : ∀ i j, herm σ (x i) (y j) = if i = j then 1 else 0) :
    LeviData σ (Matrix.of fun r i => x i r) (Matrix.of fun r i => y i r) where
  wu := Matrix.ext fun i j => by
    rw [cT_mul_of, herm_conj σ hσ, hxy j i]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply, hij, Ne.symm hij]
  uw := Matrix.ext fun i j => (cT_mul_of x y i j).trans ((hxy i j).trans (by simp [one_apply]))
  uu := Matrix.ext fun i j => (cT_mul_of x x i j).trans (hxx i j)
  ww := Matrix.ext fun i j => (cT_mul_of y y i j).trans (hyy i j)

theorem SG.exists_sl2_leviHom_suid (hσ : ∀ c, σ (σ c) = c) (x y : Fin 2 → Fin d → K)
    (hxx : ∀ i j, herm σ (x i) (x j) = 0) (hyy : ∀ i j, herm σ (y i) (y j) = 0)
    (hxy : ∀ i j, herm σ (x i) (y j) = if i = j then 1 else 0) {z : Fin d → K}
    (hzx : ∀ i, herm σ (x i) z = 0) (hzy : ∀ i, herm σ (y i) z = 0) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 2) K →* SUid σ d, Function.Injective ρ ∧
      (∀ M, ((ρ M : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ z = z) ∧
      ∀ (g : GL (Fin d) K) (a : K),
        conjTr σ (g : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) = 1 →
        (∀ i, (g : Matrix (Fin d) (Fin d) K) *ᵥ x i = a • x i) →
        (∀ i, (g : Matrix (Fin d) (Fin d) K) *ᵥ y i = a⁻¹ • y i) →
        ∀ M, g * (ρ M : GL (Fin d) K) = (ρ M : GL (Fin d) K) * g := by
  have hd := leviData_of hσ hxx hyy hxy
  refine ⟨MonoidHom.mk' (leviSU hσ hd) (leviSU_mul hσ hd), leviSU_injective hσ hd,
    fun M => ?_, fun g a hg hx hy M => ?_⟩
  · exact lv_mulVec _ _ (funext fun i => (cT_mulVec_of x z i).trans (hzx i))
      (funext fun i => (cT_mulVec_of y z i).trans (hzy i))
  · exact Units.ext (lv_comm hd hσ hg (mul_of_eq_smul _ a x hx) (mul_of_eq_smul _ a⁻¹ y hy) _ _)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
