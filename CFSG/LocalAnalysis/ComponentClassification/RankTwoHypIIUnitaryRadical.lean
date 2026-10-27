module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIILinearRadical
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAllInvolutions

public section

namespace CFSG.ComponentClassification.RankTwoHypIIUnitary

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
  UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical
  CFSG.ComponentClassification.RankTwoHypIIY CFSG.ComponentClassification.RankTwoHypIIClassical
  CFSG.ComponentClassification.RankTwoHypIILinear
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Linear

variable {k : Type} [Field k] [Finite k] [CharP k 2] {n : ℕ}

theorem exists_root_of_normal {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hev : Even n)
    (hn : 4 ≤ n) (hq : 4 ≤ Nat.card k ∨ 5 ≤ n) {E₀ : Subgroup (MulAut (projectiveSL n k))}
    (hE₀N : E₀ ≤ (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)).map (conjAut n k))
    (hnorm : ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k), ∀ x ∈ E₀,
      conjAut n k g * x * (conjAut n k g)⁻¹ ∈ E₀)
    (hne : E₀ ≠ ⊥) :
    ∃ μ : k, μ ≠ 0 ∧ ∃ g₀ : GL (Fin n) k,
      (g₀ : Matrix (Fin n) (Fin n) k) = radicalMatrix 0 μ ∧ conjAut n k g₀ ∈ E₀ := by
  have : Finite (MulAut (projectiveSL n k)) := finite_mulAut_projectiveSL
  obtain ⟨r, hr⟩ := hev
  have hev : Even n := ⟨r, hr⟩
  set i : Fin n := ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hRinn, hRC, hRn, hCR, -, -⟩ :=
    even_linear_nonalternating_graph_radical (K := k) hf hk (r := r) (by omega) hn i
  set R := (radicalGroup (K := k) i).map (conjAut n k) with hRdef
  have hδX : dualAut n k ∉ (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range :=
    dualAut_not_mem_range (by omega)
  have hNδ : (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)).map (conjAut n k) ≤
      centralizer {dualAut n k} := by
    rintro _ ⟨g, hg, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (commute_dualAut_of_mem (by omega) hg).eq.symm
  have hNX : (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k)).map (conjAut n k) ≤
      (MulAut.conj : projectiveSL n k →* MulAut (projectiveSL n k)).range := by
    rintro _ ⟨g, hg, rfl⟩
    exact conjAut_mem_inner_of_det (det_eq_one_of_mem_matrixIsometryGroup (C := 1) hg)
  have hRnorm : ∀ x ∈ centralizer {dualAut n k}, ∀ y ∈ R, x * y * x⁻¹ ∈ R := by
    intro x hx y hy
    have := hRn.conj_mem ⟨y, hRC hy⟩ (mem_subgroupOf.mpr hy) ⟨x, hx⟩
    rwa [mem_subgroupOf] at this
  obtain ⟨x, hxER, hx1⟩ : ∃ x ∈ E₀ ⊓ R, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    apply he1
    have heδ : (e : MulAut (projectiveSL n k)) ∈ centralizer {dualAut n k} := hNδ (hE₀N e.2)
    have heC : (e : MulAut (projectiveSL n k)) ∈ centralizer {dualAut n k} ⊓
        centralizer (R : Set (MulAut (projectiveSL n k))) := by
      refine mem_inf.mpr ⟨heδ, ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨g, hg, rfl⟩ := hy
      have hgO := radicalGroup_le hev i hg
      have h1 : (e : MulAut (projectiveSL n k)) * conjAut n k g * (e : MulAut _)⁻¹ *
          (conjAut n k g)⁻¹ ∈ E₀ ⊓ R := by
        refine mem_inf.mpr ⟨?_, R.mul_mem (hRnorm _ heδ _ (mem_map_of_mem _ hg))
          (R.inv_mem (mem_map_of_mem _ hg))⟩
        have h2 := hnorm g hgO _ (E₀.inv_mem e.2)
        have := E₀.mul_mem e.2 h2
        simpa [mul_assoc] using this
      have h3 := hcon _ h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
      exact h3.symm
    obtain ⟨g, hg, ε, hε, hge⟩ := exists_of_mem_centralizer_radicalImage hev (by omega) i heC
    rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · rw [pow_zero, mul_one] at hge
      exact Subtype.ext (hcon _ (mem_inf.mpr ⟨e.2, hge ▸ mem_map_of_mem _ hg⟩))
    · exfalso
      apply hδX
      rw [pow_one] at hge
      have : dualAut n k = (conjAut n k g)⁻¹ * e := by rw [hge]; group
      rw [this]
      exact mul_mem (inv_mem (hRinn (mem_map_of_mem _ hg))) (hNX (hE₀N e.2))
  obtain ⟨hxE, hxR⟩ := mem_inf.mp hxER
  obtain ⟨g, hg, rfl⟩ := mem_map.mp hxR
  obtain ⟨v, hv, c, hgv⟩ := (mem_radicalGroup hev).mp hg
  have hv0 : onesVec ⬝ᵥ v = 0 := (mem_radicalW.mp hv).1
  have hNnorm : ∀ h' ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) k),
      ∀ y ∈ E₀ ⊓ R, conjAut n k h' * y * (conjAut n k h')⁻¹ ∈ E₀ ⊓ R := by
    intro h' hh' y hy
    obtain ⟨hyE, hyR⟩ := mem_inf.mp hy
    exact mem_inf.mpr ⟨hnorm h' hh' y hyE, hRnorm _ (hNδ (mem_map_of_mem _ hh')) y hyR⟩
  have hmemN : RadMem k (E₀ ⊓ R) v c := ⟨g, hgv, mem_inf.mpr ⟨hxE, hxR⟩⟩
  have hne' : (¬ ∃ a : k, v = a • onesVec) ∨ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨a, rfl⟩, rfl⟩ := hcon
    apply hx1
    have : g = 1 := Units.ext (by
      rw [hgv, Units.val_one, ← zero_add (a • onesVec), radicalMatrix_add_smul_onesVec,
        radicalMatrix_zero])
    rw [this, map_one]
  obtain ⟨μ, hμ, g₀, hg₀, hg₀N⟩ := hmemN.exists_root hev hNnorm hn hq hv0 hne'
  exact ⟨μ, hμ, g₀, hg₀, (mem_inf.mp hg₀N).1⟩

end Linear

section Reflection

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def barVec (y : Fin n → K) : Fin n → K := fun i => h.bar (y i)

@[expose] noncomputable def reflMat (lam : K) (y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + lam • vecMulVec (barVec h y) y

theorem dotProduct_barVec_comm (y z : Fin n → K) :
    h.bar (y ⬝ᵥ z) = barVec h y ⬝ᵥ barVec h z := by
  simp only [dotProduct, map_sum, map_mul, barVec]

theorem reflMat_mulVec (lam : K) (y x : Fin n → K) :
    reflMat h lam y *ᵥ x = x + (lam * (y ⬝ᵥ x)) • barVec h y := by
  simp only [reflMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

theorem reflMat_transpose (lam : K) (y : Fin n → K) :
    (reflMat h lam y)ᵀ = 1 + lam • vecMulVec y (barVec h y) := by
  rw [reflMat, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]

theorem reflMat_map_bar (lam : K) (y : Fin n → K) :
    (reflMat h lam y).map h.bar = 1 + h.bar lam • vecMulVec y (barVec h y) := by
  ext i j
  simp only [reflMat, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul, barVec, map_add, map_mul, h.bar_bar]
  split_ifs <;> simp

theorem reflMat_unitary {lam : K} {y : Fin n → K}
    (hl : lam + h.bar lam + h.bar lam * lam * (y ⬝ᵥ barVec h y) = 0) :
    ((reflMat h lam y).map h.bar)ᵀ * reflMat h lam y = 1 := by
  rw [reflMat_map_bar, transpose_add, transpose_one, transpose_smul, transpose_vecMulVec, reflMat,
    add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec, smul_smul]
  have : lam • vecMulVec (barVec h y) y + (h.bar lam • vecMulVec (barVec h y) y +
      (h.bar lam * lam) • vecMulVec (barVec h y) ((y ⬝ᵥ barVec h y) • y)) = 0 := by
    rw [vecMulVec_smul, smul_smul, ← add_smul, ← add_smul]
    rw [show lam + (h.bar lam + h.bar lam * lam * y ⬝ᵥ barVec h y) = 0 by
      rw [← hl]; ring, zero_smul]
  rw [add_assoc, this, add_zero]

theorem det_reflMat (lam : K) (y : Fin n → K) :
    (reflMat h lam y).det = 1 + lam * (y ⬝ᵥ barVec h y) :=
  det_one_add_smul_vecMulVec lam _ _

theorem reflMat_transpose_mulVec (lam : K) (y x : Fin n → K) :
    (reflMat h lam y)ᵀ *ᵥ x = x + (lam * (barVec h y ⬝ᵥ x)) • y := by
  rw [reflMat_transpose, one_add_smul_vecMulVec_mulVec]

theorem barVec_dotProduct_self {y : Fin n → K} (hyy : y ⬝ᵥ y = 0) :
    barVec h y ⬝ᵥ barVec h y = 0 := by
  rw [← dotProduct_barVec_comm, hyy, map_zero]

theorem reflSq_mulVec_apply [CharP K 2] {lam : K} {y : Fin n → K} (hyy : y ⬝ᵥ y = 0)
    (x : Fin n → K) (i : Fin n) :
    ((reflMat h lam y * (reflMat h lam y)ᵀ * (reflMat h lam y * (reflMat h lam y)ᵀ)) *ᵥ x) i =
      x i + lam ^ 2 * (y ⬝ᵥ barVec h y) *
        ((y ⬝ᵥ x) * barVec h y i + (barVec h y ⬝ᵥ x) * y i) := by
  have hbb := barVec_dotProduct_self h hyy
  have hby : barVec h y ⬝ᵥ y = y ⬝ᵥ barVec h y := dotProduct_comm _ _
  simp only [← mulVec_mulVec, reflMat_mulVec, reflMat_transpose_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, hyy, hbb, hby, Pi.add_apply, Pi.smul_apply, mul_zero,
    add_zero]
  linear_combination (lam * (barVec h y ⬝ᵥ x) * y i + lam * (y ⬝ᵥ x) * barVec h y i) *
    (CharTwo.two_eq_zero : (2 : K) = 0)

variable (K) in
@[expose] def reflVec (a : K) (i j l : Fin n) : Fin n → K :=
  a • ev K i + ev K j + (a + 1) • ev K l

theorem reflVec_dotProduct (a : K) (i j l : Fin n) (v : Fin n → K) :
    reflVec K a i j l ⬝ᵥ v = a * v i + v j + (a + 1) * v l := by
  simp [reflVec, ev, add_dotProduct, smul_dotProduct, single_dotProduct]

theorem barVec_reflVec (a : K) (i j l : Fin n) :
    barVec h (reflVec K a i j l) = reflVec K (h.bar a) i j l := by
  ext m
  simp only [barVec, reflVec, ev, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp

theorem reflVec_apply_left (a : K) {i j l : Fin n} (hij : i ≠ j) (hil : i ≠ l) :
    reflVec K a i j l i = a := by
  simp [reflVec, ev, hij, hil]

theorem reflVec_apply_mid (a : K) {i j l : Fin n} (hij : i ≠ j) (hjl : j ≠ l) :
    reflVec K a i j l j = 1 := by
  simp [reflVec, ev, hij.symm, hjl]

theorem reflVec_apply_right (a : K) {i j l : Fin n} (hil : i ≠ l) (hjl : j ≠ l) :
    reflVec K a i j l l = a + 1 := by
  simp [reflVec, ev, hil.symm, hjl.symm]

theorem reflVec_apply_of_ne (a : K) {i j l m : Fin n} (hi : m ≠ i) (hj : m ≠ j) (hl : m ≠ l) :
    reflVec K a i j l m = 0 := by
  simp [reflVec, ev, hi, hj, hl]

theorem reflVec_props [CharP K 2] {a : K} (ha : h.bar a ≠ a) {i j l : Fin n} (hij : i ≠ j)
    (hil : i ≠ l) (hjl : j ≠ l) :
    reflVec K a i j l ⬝ᵥ reflVec K a i j l = 0 ∧
    reflVec K a i j l ⬝ᵥ barVec h (reflVec K a i j l) = a + h.bar a ∧
    ((reflMat h a⁻¹ (reflVec K a i j l)).map h.bar)ᵀ * reflMat h a⁻¹ (reflVec K a i j l) = 1 ∧
    reflMat h a⁻¹ (reflVec K a i j l) *ᵥ onesVec = onesVec ∧
    (reflMat h a⁻¹ (reflVec K a i j l))ᵀ *ᵥ onesVec = onesVec ∧
    (reflMat h a⁻¹ (reflVec K a i j l)).det = h.bar a * a⁻¹ := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero _)
  have hb0 : h.bar a ≠ 0 := by
    intro h0
    apply ha0
    have := congrArg h.bar h0
    rwa [h.bar_bar, map_zero] at this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hyy : reflVec K a i j l ⬝ᵥ reflVec K a i j l = 0 := by
    rw [reflVec_dotProduct, reflVec_apply_left a hij hil, reflVec_apply_mid a hij hjl,
      reflVec_apply_right a hil hjl]
    linear_combination (a ^ 2 + a + 1) * h2
  have hyb : reflVec K a i j l ⬝ᵥ barVec h (reflVec K a i j l) = a + h.bar a := by
    rw [barVec_reflVec, reflVec_dotProduct, reflVec_apply_left _ hij hil,
      reflVec_apply_mid _ hij hjl, reflVec_apply_right _ hil hjl]
    linear_combination (a * h.bar a + 1) * h2
  have hyd : reflVec K a i j l ⬝ᵥ onesVec = 0 := by
    rw [reflVec_dotProduct]
    simp only [onesVec_apply, mul_one]
    linear_combination (a + 1) * h2
  have hbd : barVec h (reflVec K a i j l) ⬝ᵥ onesVec = 0 := by
    rw [barVec_reflVec, reflVec_dotProduct]
    simp only [onesVec_apply, mul_one]
    linear_combination (h.bar a + 1) * h2
  refine ⟨hyy, hyb, reflMat_unitary h ?_, ?_, ?_, ?_⟩
  · rw [hyb, map_inv₀]
    have : a⁻¹ + (h.bar a)⁻¹ + (h.bar a)⁻¹ * a⁻¹ * (a + h.bar a) =
        2 * (a⁻¹ + (h.bar a)⁻¹) := by
      field_simp
      ring
    rw [this, h2, zero_mul]
  · rw [reflMat_mulVec, hyd, mul_zero, zero_smul, add_zero]
  · rw [reflMat_transpose_mulVec, hbd, mul_zero, zero_smul, add_zero]
  · rw [det_reflMat, hyb]
    field_simp
    linear_combination a * h2

theorem reflVec_dotProduct_eq_zero (a : K) {i j l : Fin n} {v : Fin n → K} (hi : v i = 0)
    (hj : v j = 0) (hl : v l = 0) : reflVec K a i j l ⬝ᵥ v = 0 := by
  rw [reflVec_dotProduct, hi, hj, hl]
  ring

theorem commute_radical {A : Matrix (Fin n) (Fin n) K} {c : K} (μ : K)
    (h1 : A *ᵥ onesVec = c • onesVec) (h2 : Aᵀ *ᵥ onesVec = c • onesVec) :
    A * (1 + μ • vecMulVec onesVec onesVec) = (1 + μ • vecMulVec onesVec onesVec) * A := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
    Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, h1, ← mulVec_transpose, h2, smul_vecMulVec,
    vecMulVec_smul]

theorem scalar_mulVec_ev_apply {c : K} {i j : Fin n} (hij : i ≠ j) :
    (scalar (Fin n) c *ᵥ ev K j) i = 0 := by
  simp [ev, scalar_apply, hij]

end Reflection

section Model

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem conj_commutator_fieldHom (σ : K ≃+* K)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A * primeFormFieldHom h isPrimeFormGram_one σ *
        (primeFormConjHom h _ A)⁻¹ * (primeFormFieldHom h isPrimeFormGram_one σ)⁻¹ =
      primeFormConjHom h _ (A * (primeFormFieldU h isPrimeFormGram_one σ A)⁻¹) := by
  have e := primeFormField_conj_eq h isPrimeFormGram_one σ A⁻¹
  rw [map_inv (primeFormFieldU h isPrimeFormGram_one σ),
    map_inv (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
    map_inv (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))] at e
  rw [map_mul, map_inv (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)), ← e]
  group

theorem coe_mul_fieldU_inv (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    (((A * (primeFormFieldU h isPrimeFormGram_one σ A)⁻¹ : primeFormUnitary h _) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ := by
  have hA : (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    simpa using mem_primeFormUnitary.mp A.2
  have hAt : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar = 1 := by
    have := congrArg transpose hA
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  have hval : (((primeFormFieldU h isPrimeFormGram_one σ A : primeFormUnitary h _) :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map h.bar := by
    rw [coe_primeFormFieldU, coe_glAut]
    exact congrArg (Matrix.map _) (funext hσ)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  congr 1
  have key : ∀ (u : GL (Fin n) K) (M : Matrix (Fin n) (Fin n) K),
      M * (u : Matrix (Fin n) (Fin n) K) = 1 →
        ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = M := by
    intro u M hM
    calc ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        M * (u : Matrix (Fin n) (Fin n) K) * ((u⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
          by rw [hM, Matrix.one_mul]
      _ = M := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  exact key _ _ (by rw [hval]; exact hAt)

theorem exists_sq_eq_scalar_of_mem (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : CFSG.Open.IsElemAbelian 2 E)
    {B : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hB : primeFormConjHom h _ B ∈ E) :
    ∃ c : Kˣ, ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = scalar (Fin n) (c : K) := by
  have h2 := hE.2 _ hB
  rw [← map_pow] at h2
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h isPrimeFormGram_one hn
    ⟨B ^ 2, RingEquiv.refl K⟩).mp (by
      rw [primeFormPsi_apply]
      rw [show (RingEquiv.refl K) = (1 : K ≃+* K) from rfl, map_one, mul_one]
      exact h2)
  refine ⟨c, ?_⟩
  have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
  simpa [sq, GeneralLinearGroup.coe_scalar] using this

theorem primeFormConj_mem_inner
    {A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1) :
    primeFormConjHom h _ A ∈
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
  (mem_inner_primeFormP h _ _).mpr ⟨⟨A, (mem_gramSU_iff_unitary h).mpr ⟨A.2, hdet⟩⟩, rfl⟩

theorem primeFormConj_mem_centralizer
    {A R : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hAR : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    primeFormConjHom h _ A ∈ centralizer {primeFormConjHom h _ R} := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
    Units.val_mul, hAR]))

theorem exists_sq_scalar (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : CFSG.Open.IsElemAbelian 2 E) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hγ : primeFormFieldHom h isPrimeFormGram_one σ ∈ E)
    {R : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hC : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormConjHom h _ R} ≤ normalizer (E : Set (MulAut (primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))))
    {A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)}
    (hdet : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1)
    (hAR : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ c : Kˣ, (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) *
      (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ) = scalar (Fin n) (c : K) := by
  have hN := hC (mem_inf.mpr ⟨primeFormConj_mem_inner h hdet,
    primeFormConj_mem_centralizer h hAR⟩)
  have h1 := (mem_normalizer_iff.mp hN _).mp hγ
  have h2 : primeFormConjHom h _ (A * (primeFormFieldU h isPrimeFormGram_one σ A)⁻¹) ∈ E := by
    rw [← conj_commutator_fieldHom]
    exact mul_mem h1 (inv_mem hγ)
  obtain ⟨c, hc⟩ := exists_sq_eq_scalar_of_mem h hn hE h2
  rw [coe_mul_fieldU_inv h σ hσ] at hc
  exact ⟨c, hc⟩

end Model

section Final

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem false_of_root_four_bar
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)))}
    (hE : CFSG.Open.IsElemAbelian 2 E) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hγ : primeFormFieldHom h isPrimeFormGram_one σ ∈ E)
    {R : primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)} {μ : K}
    (hR : ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 + μ • vecMulVec onesVec onesVec)
    (hC : inner (primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) ⊓
      centralizer {primeFormConjHom h _ R} ≤ normalizer (E : Set (MulAut (primeFormP h
        ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))))) :
    False := by
  have := h.charP
  have := h.finite
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, ha⟩ := h.exists_bar_ne
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero _)
  have hb0 : h.bar a ≠ 0 := by
    intro h0
    apply ha0
    have := congrArg h.bar h0
    rwa [h.bar_bar, map_zero] at this
  obtain ⟨w, hw⟩ := isSquare_of_charTwo' (a * (h.bar a)⁻¹)
  obtain ⟨z, hz⟩ := isSquare_of_charTwo' w
  have hz4 : z ^ 4 = a * (h.bar a)⁻¹ := by
    rw [hw, hz]
    ring
  have hNz : h.bar z * z = 1 := by
    apply eq_one_of_pow_four_eq_one
    rw [mul_pow, ← map_pow, hz4, map_mul, map_inv₀, h.bar_bar]
    field_simp
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hNz
  obtain ⟨hyy, hyb, hU, hd1, hd2, hdet⟩ := reflVec_props h ha (i := (0 : Fin 4)) (j := 1) (l := 2)
    (by decide) (by decide) (by decide)
  set y := reflVec K a (0 : Fin 4) 1 2 with hy
  set X := reflMat h a⁻¹ y with hX
  have hAdet : (z • X).det = 1 := by
    rw [det_smul, Fintype.card_fin, hdet, hz4]
    field_simp
  set g : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero (z • X)
    (by rw [hAdet]; exact one_ne_zero) with hg
  have hgA : (g : Matrix (Fin 4) (Fin 4) K) = z • X := rfl
  have hgU : g ∈ primeFormUnitary h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [mem_primeFormUnitary, hgA, Units.val_one, Matrix.mul_one]
    have hmap : (z • X).map h.bar = h.bar z • X.map h.bar := by
      ext i j
      simp
    rw [hmap, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU, hNz, one_smul]
  have hcomm : (g : Matrix (Fin 4) (Fin 4) K) * ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      ((R : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) := by
    rw [hgA, hR]
    refine commute_radical μ (c := z) ?_ ?_
    · rw [smul_mulVec, hd1]
    · rw [transpose_smul, smul_mulVec, hd2]
  obtain ⟨c, hc⟩ := exists_sq_scalar h (by norm_num) hE σ hσ hγ hC (A := ⟨g, hgU⟩) hAdet hcomm
  have hval := congrFun (congrArg (fun N => N *ᵥ ev K 1) hc) 0
  simp only at hval
  rw [scalar_mulVec_ev_apply (by decide)] at hval
  change (((g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K)ᵀ *
    ((g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K)ᵀ)) *ᵥ ev K 1) 0 = 0 at hval
  rw [hgA, transpose_smul, smul_mul_smul_comm, smul_mul_smul_comm, smul_mulVec, Pi.smul_apply,
    smul_eq_mul, reflSq_mulVec_apply h hyy, hyb] at hval
  simp only [ev, dotProduct_single, mul_one] at hval
  rw [hy, barVec_reflVec, reflVec_apply_mid _ (by decide) (by decide),
    reflVec_apply_mid _ (by decide) (by decide), reflVec_apply_left _ (by decide) (by decide),
    reflVec_apply_left _ (by decide) (by decide),
    Pi.single_eq_of_ne (show (0 : Fin 4) ≠ 1 by decide), zero_add, one_mul, one_mul] at hval
  have hτ : a + h.bar a ≠ 0 := fun h0 => ha (CharTwo.add_eq_zero.mp h0).symm
  have : z * z * (z * z) * ((a⁻¹) ^ 2 * (a + h.bar a) * (h.bar a + a)) ≠ 0 := by
    rw [add_comm (h.bar a) a]
    exact mul_ne_zero (by simp [hz0]) (mul_ne_zero (mul_ne_zero (by simp [ha0]) hτ) hτ)
  exact this hval

theorem false_of_root_six_bar (hn : 6 ≤ n)
    {E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hE : CFSG.Open.IsElemAbelian 2 E) (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hγ : primeFormFieldHom h isPrimeFormGram_one σ ∈ E)
    {R : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)} {μ : K}
    (hR : ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + μ • vecMulVec onesVec onesVec)
    (hC : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormConjHom h _ R} ≤ normalizer (E : Set (MulAut (primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))))) :
    False := by
  have := h.charP
  have := h.finite
  obtain ⟨a, ha⟩ := h.exists_bar_ne
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero _)
  have hb0 : h.bar a ≠ 0 := by
    intro h0
    apply ha0
    have := congrArg h.bar h0
    rwa [h.bar_bar, map_zero] at this
  have hb : h.bar (h.bar a) ≠ h.bar a := by
    rw [h.bar_bar]
    exact ha.symm
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  set i₂ : Fin n := ⟨2, by omega⟩
  set i₃ : Fin n := ⟨3, by omega⟩
  set i₄ : Fin n := ⟨4, by omega⟩
  set i₅ : Fin n := ⟨5, by omega⟩
  have hne : ∀ {s t : ℕ} (hs : s < n) (ht : t < n), s ≠ t →
      (⟨s, hs⟩ : Fin n) ≠ ⟨t, ht⟩ := fun _ _ hst h' => hst (Fin.mk.inj h')
  obtain ⟨hyy₁, hyb₁, hU₁, hd₁, hd₁', hdet₁⟩ := reflVec_props h ha (i := i₀) (j := i₁) (l := i₂)
    (hne _ _ (by norm_num)) (hne _ _ (by norm_num)) (hne _ _ (by norm_num))
  obtain ⟨-, -, hU₂, hd₂, hd₂', hdet₂⟩ := reflVec_props h hb (i := i₃) (j := i₄) (l := i₅)
    (hne _ _ (by norm_num)) (hne _ _ (by norm_num)) (hne _ _ (by norm_num))
  set y₁ := reflVec K a i₀ i₁ i₂ with hy₁
  set y₂ := reflVec K (h.bar a) i₃ i₄ i₅ with hy₂
  set X₁ := reflMat h a⁻¹ y₁ with hX₁
  set X₂ := reflMat h (h.bar a)⁻¹ y₂ with hX₂
  have hAdet : (X₁ * X₂).det = 1 := by
    rw [det_mul, hdet₁, hdet₂, h.bar_bar]
    field_simp
  set g : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero (X₁ * X₂)
    (by rw [hAdet]; exact one_ne_zero) with hg
  have hgA : (g : Matrix (Fin n) (Fin n) K) = X₁ * X₂ := rfl
  have hgU : g ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, hgA, Units.val_one, Matrix.mul_one, Matrix.map_mul, transpose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc (X₁.map h.bar)ᵀ, hU₁, Matrix.one_mul, hU₂]
  have hcomm : (g : Matrix (Fin n) (Fin n) K) * ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((R : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) := by
    rw [hgA, hR]
    refine commute_radical μ (c := 1) ?_ ?_
    · rw [← mulVec_mulVec, hd₂, hd₁, one_smul]
    · rw [transpose_mul, ← mulVec_mulVec, hd₁', hd₂', one_smul]
  obtain ⟨c, hc⟩ := exists_sq_scalar h (by omega) hE σ hσ hγ hC (A := ⟨g, hgU⟩) hAdet hcomm
  set P : (Fin n → K) → Prop := fun v => y₂ ⬝ᵥ v = 0 ∧ barVec h y₂ ⬝ᵥ v = 0 with hP
  have hPv : ∀ v : Fin n → K, v i₃ = 0 → v i₄ = 0 → v i₅ = 0 → P v := fun v h3 h4 h5 =>
    ⟨reflVec_dotProduct_eq_zero _ h3 h4 h5, by
      rw [barVec_reflVec]
      exact reflVec_dotProduct_eq_zero _ h3 h4 h5⟩
  have hvan : ∀ b : K, ∀ m : Fin n, m = i₃ ∨ m = i₄ ∨ m = i₅ → reflVec K b i₀ i₁ i₂ m = 0 := by
    intro b m hm
    rcases hm with rfl | rfl | rfl <;>
      exact reflVec_apply_of_ne b (hne _ _ (by norm_num)) (hne _ _ (by norm_num))
        (hne _ _ (by norm_num))
  have hPy₁ : P y₁ := hPv _ (hvan _ _ (Or.inl rfl)) (hvan _ _ (Or.inr (Or.inl rfl)))
    (hvan _ _ (Or.inr (Or.inr rfl)))
  have hPb₁ : P (barVec h y₁) := by
    rw [hy₁, barVec_reflVec]
    exact hPv _ (hvan _ _ (Or.inl rfl)) (hvan _ _ (Or.inr (Or.inl rfl)))
      (hvan _ _ (Or.inr (Or.inr rfl)))
  have he₁ : P (ev K i₁) := hPv _ (Pi.single_eq_of_ne (hne _ _ (by norm_num)) _)
    (Pi.single_eq_of_ne (hne _ _ (by norm_num)) _) (Pi.single_eq_of_ne (hne _ _ (by norm_num)) _)
  have hPT : ∀ v, P v → P (X₁ᵀ *ᵥ v) := by
    rintro v ⟨h1, h2⟩
    rw [hX₁, reflMat_transpose_mulVec]
    exact ⟨by rw [dotProduct_add, dotProduct_smul, h1, hPy₁.1, smul_zero, add_zero],
      by rw [dotProduct_add, dotProduct_smul, h2, hPy₁.2, smul_zero, add_zero]⟩
  have hPX : ∀ v, P v → P (X₁ *ᵥ v) := by
    rintro v ⟨h1, h2⟩
    rw [hX₁, reflMat_mulVec]
    exact ⟨by rw [dotProduct_add, dotProduct_smul, h1, hPb₁.1, smul_zero, add_zero],
      by rw [dotProduct_add, dotProduct_smul, h2, hPb₁.2, smul_zero, add_zero]⟩
  have htriv : ∀ v, P v → X₂ *ᵥ (X₂ᵀ *ᵥ v) = v := by
    rintro v ⟨h1, h2⟩
    rw [hX₂, reflMat_transpose_mulVec, h2, mul_zero, zero_smul, add_zero, reflMat_mulVec, h1,
      mul_zero, zero_smul, add_zero]
  have hred : (X₁ * X₂ * (X₁ * X₂)ᵀ * (X₁ * X₂ * (X₁ * X₂)ᵀ)) *ᵥ ev K i₁ =
      (X₁ * X₁ᵀ * (X₁ * X₁ᵀ)) *ᵥ ev K i₁ := by
    simp only [transpose_mul, ← mulVec_mulVec]
    rw [htriv _ (hPT _ he₁), htriv _ (hPT _ (hPX _ (hPT _ he₁)))]
  have hval := congrFun (congrArg (fun N => N *ᵥ ev K i₁) hc) i₀
  simp only at hval
  rw [scalar_mulVec_ev_apply (hne _ _ (by norm_num))] at hval
  change (((g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ *
    ((g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)ᵀ)) *ᵥ ev K i₁) i₀ = 0 at hval
  rw [hgA, hred, hX₁, reflSq_mulVec_apply h hyy₁, hyb₁] at hval
  simp only [ev, dotProduct_single, mul_one] at hval
  rw [hy₁, barVec_reflVec, reflVec_apply_mid _ (hne _ _ (by norm_num)) (hne _ _ (by norm_num)),
    reflVec_apply_mid _ (hne _ _ (by norm_num)) (hne _ _ (by norm_num)),
    reflVec_apply_left _ (hne _ _ (by norm_num)) (hne _ _ (by norm_num)),
    reflVec_apply_left _ (hne _ _ (by norm_num)) (hne _ _ (by norm_num)),
    Pi.single_eq_of_ne (hne _ _ (by norm_num)), zero_add, one_mul, one_mul] at hval
  have hτ : a + h.bar a ≠ 0 := fun h0 => ha (CharTwo.add_eq_zero.mp h0).symm
  have : (a⁻¹) ^ 2 * (a + h.bar a) * (h.bar a + a) ≠ 0 := by
    rw [add_comm (h.bar a) a]
    exact mul_ne_zero (mul_ne_zero (by simp [ha0]) hτ) hτ
  exact this hval

end Final

section Config

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem oddCore_inf_eq_bot {W : Type*} [Group W] [Finite W] {X C : Subgroup W} (hX : X.Normal)
    (hO : CFSG.oddCore ↥C = ⊥) : CFSG.oddCore ↥(X ⊓ C) = ⊥ := by
  set G := X ⊓ C with hG
  have hchar : (CFSG.oddCore ↥G).Characteristic := OddCore.characteristic G
  set Q := (CFSG.oddCore ↥G).map G.subtype with hQ
  have hQC : Q ≤ C := (map_subtype_le _).trans inf_le_right
  have hodd : Odd (Nat.card Q) := by
    rw [hQ, card_map_of_injective G.subtype_injective]
    exact OddCore.odd_card G
  have hnorm : ∀ c ∈ C, c ∈ normalizer (Q : Set W) := by
    intro c hc
    have hcG : c ∈ normalizer (G : Set W) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact mem_inf.mpr ⟨hX.conj_mem _ (mem_inf.mp hx).1 c,
          C.mul_mem (C.mul_mem hc (mem_inf.mp hx).2) (C.inv_mem hc)⟩
      · intro hx
        have h1 := hX.conj_mem _ (mem_inf.mp hx).1 c⁻¹
        have h2 := C.mul_mem (C.mul_mem (C.inv_mem hc) (mem_inf.mp hx).2) hc
        refine mem_inf.mpr ⟨?_, ?_⟩
        · simpa [mul_assoc] using h1
        · simpa [mul_assoc] using h2
    have hGc := mem_normalizer_iff_map_conj_eq.mp hcG
    let φ : G ≃* G := ((MulAut.conj c).subgroupMap G).trans (MulEquiv.subgroupCongr hGc)
    have hφ : (CFSG.oddCore ↥G).map φ.toMonoidHom = CFSG.oddCore ↥G :=
      characteristic_iff_map_eq.mp hchar φ
    rw [mem_normalizer_iff_map_conj_eq, hQ, Subgroup.map_map]
    have hcomp : (MulAut.conj c : W →* W).comp G.subtype = G.subtype.comp φ.toMonoidHom := by
      ext g
      rfl
    rw [hcomp, ← Subgroup.map_map, hφ]
  have hn : (Q.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQC).mpr fun c hc => hnorm c hc
  have hodd' : Odd (Nat.card (Q.subgroupOf C)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv]
  have hle : Q.subgroupOf C ≤ CFSG.oddCore ↥C := le_sSup ⟨hn, hodd'⟩
  rw [hO, le_bot_iff] at hle
  have hQ1 : Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQC hx⟩ : C) ∈ Q.subgroupOf C := hx
    rw [hle] at this
    exact congrArg Subtype.val ((mem_bot).mp this)
  exact (map_eq_bot_iff_of_injective _ G.subtype_injective).mp hQ1

theorem map_radicalMatrix_zero (μ : h.fixedField) :
    (radicalMatrix (0 : Fin n → h.fixedField) μ).map h.fixedField.subtype =
      1 + (μ : K) • vecMulVec onesVec onesVec := by
  ext i j
  simp only [radicalMatrix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    vecMulVec_apply, onesVec_apply, Pi.zero_apply, mul_zero, add_zero, smul_eq_mul,
    mul_one, Matrix.one_apply]
  split_ifs <;> simp

theorem false_of_config_bar (hev : Even n) (hn : 4 ≤ n) (h42 : ¬ (n = 4 ∧ f = 1))
    {E M : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hc : HypIIConfig (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) E M)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x)
    (hγ : primeFormFieldHom h isPrimeFormGram_one σ ∈ E)
    (hE0 : ∃ e ∈ E, e ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ∧
      e ≠ 1) : False := by
  have := fixedField_charP h
  have := fixedField_finite h
  have := h.finite
  have : CharP K 2 := h.charP
  have : Finite (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
    have : Finite (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := inferInstance
    exact Finite.of_injective (fun e : MulAut (primeFormP h _) => (e : primeFormP h _ → _))
      fun _ _ hab => MulEquiv.ext (congrFun hab)
  have hXn : (inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).Normal :=
    OuterAutomorphisms.inner_normal _
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  have hcase : ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = blockSwapJ n r :=
    Or.inl Units.val_one
  have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one]
  obtain ⟨hcent, -, -, hNinn, hNC, -, Θ, hΘ, -, -, hord2, -, e, he⟩ :=
    even_unitary_canonical_field_centralizer_transfer h (by omega) hq isPrimeFormGram_one hcase 1
      hCl σ hσ
  have hγ1 : primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord2
    omega
  have hO : CFSG.oddCore ↥(inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ}) = ⊥ := by
    have h0 := even_unitary_all_involution_full_centralizer_odd_core h isPrimeFormGram_one
      (by omega) hq (H := ⊤) le_top _ (mem_top _) hord2
    rw [top_inf_eq] at h0
    exact oddCore_inf_eq_bot hXn h0
  have hCγ := hc.centralizer_le_normalizer hXn hγ hγ1 hO
  have hXN : inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ} ≤
        ((primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    intro x hx
    obtain ⟨hxX, hxC⟩ := mem_inf.mp hx
    obtain ⟨g, φ, rfl⟩ := (hcent x).mp hxC
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxX
    have hφ : φ = 1 := by
      have h1 := primeFormFieldFactor_psi h isPrimeFormGram_one (by omega) hq
        ⟨fixedIsometryHom h hCl g, φ⟩
      rw [hs, ← mul_one (primeFormConjHom h _ _), ← map_one (primeFormFieldHom h
        isPrimeFormGram_one), primeFormFieldFactor_apply] at h1
      exact h1.symm
    refine ⟨g, ?_⟩
    rw [hφ, primeFormPsi_apply, map_one, mul_one]
    rfl
  have hE₀ : ∀ x ∈ E, x ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) →
      x ∈ ((primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp
        (fixedIsometryHom h hCl)).range := fun x hxE hxX =>
    hXN (mem_inf.mpr ⟨hxX, hc.le_centralizer hγ hxE⟩)
  set E₀' : Subgroup (MulAut (projectiveSL n h.fixedField)) :=
    ((E ⊓ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))).subgroupOf
      ((primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp
        (fixedIsometryHom h hCl)).range).map
      ((Subgroup.map (conjAut n h.fixedField) (matrixIsometryGroup
        ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField))).subtype.comp
          e.toMonoidHom) with hE₀'
  have hE₀N : E₀' ≤ (matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) h.fixedField)).map
      (conjAut n h.fixedField) := by
    rintro _ ⟨x, -, rfl⟩
    exact (e x).2
  have hnorm : ∀ g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) h.fixedField),
      ∀ x ∈ E₀', conjAut n h.fixedField g * x * (conjAut n h.fixedField g)⁻¹ ∈ E₀' := by
    rintro g hg _ ⟨y, hy, rfl⟩
    have hgN : conjAut n h.fixedField g ∈ (matrixIsometryGroup
        ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)).map
          (conjAut n h.fixedField) := mem_map_of_mem _ hg
    obtain ⟨z, hz⟩ := e.surjective ⟨_, hgN⟩
    have hzg : ((e z : _) : MulAut (projectiveSL n h.fixedField)) = conjAut n h.fixedField g := by
      rw [hz]
    obtain ⟨hyE, hyX⟩ := mem_inf.mp (mem_subgroupOf.mp hy)
    have hzN : (z : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∈
        inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ⊓
          centralizer {primeFormFieldHom h isPrimeFormGram_one σ} :=
      mem_inf.mpr ⟨hNinn z.2, hNC z.2⟩
    refine ⟨z * y * z⁻¹, mem_subgroupOf.mpr (mem_inf.mpr ⟨?_, ?_⟩), ?_⟩
    · exact (mem_normalizer_iff.mp (hCγ hzN) _).mp hyE
    · exact hXn.conj_mem _ hyX _
    · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul,
        map_inv, coe_subtype, hzg]
  have hne : E₀' ≠ ⊥ := by
    obtain ⟨x, hxE, hxX, hx1⟩ := hE0
    intro hbot
    have hmem : ((e ⟨x, hE₀ x hxE hxX⟩ : _) : MulAut (projectiveSL n h.fixedField)) ∈ E₀' :=
      ⟨⟨x, hE₀ x hxE hxX⟩, mem_subgroupOf.mpr (mem_inf.mpr ⟨hxE, hxX⟩), rfl⟩
    rw [hbot, mem_bot] at hmem
    apply hx1
    have : e ⟨x, hE₀ x hxE hxX⟩ = 1 := Subtype.ext hmem
    rw [MulEquiv.map_eq_one_iff] at this
    exact congrArg Subtype.val this
  have hq' : 4 ≤ Nat.card h.fixedField ∨ 5 ≤ n := by
    by_cases hn4 : n = 4
    · left
      have hf2 : 2 ≤ f := by
        have := h.one_le
        omega
      rw [h.card_fixedField]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    · right
      omega
  obtain ⟨μ, hμ, g₀, hg₀, hg₀E⟩ :=
    exists_root_of_normal h.one_le h.card_fixedField hev hn hq' hE₀N hnorm hne
  have hg₀O : g₀ ∈ matrixIsometryGroup
      ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) :=
    radicalGroup_le hev ⟨0, by omega⟩
      (mem_radicalGroup_of_dotProduct hev (x := 0) (by simp) hg₀)
  have hv₀N : primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (fixedIsometryHom h hCl ⟨g₀, hg₀O⟩) ∈
        ((primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := ⟨⟨g₀, hg₀O⟩, rfl⟩
  have hev₀ : ((e ⟨_, hv₀N⟩ : _) : MulAut (projectiveSL n h.fixedField)) =
      conjAut n h.fixedField g₀ := by
    have hPsi : primeFormPsi h isPrimeFormGram_one ⟨fixedIsometryHom h hCl ⟨g₀, hg₀O⟩, 1⟩ =
        primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          (fixedIsometryHom h hCl ⟨g₀, hg₀O⟩) := by
      rw [primeFormPsi_apply, map_one, mul_one]
    have hα : primeFormPsi h isPrimeFormGram_one ⟨fixedIsometryHom h hCl ⟨g₀, hg₀O⟩, 1⟩ ∈
        centralizer {primeFormFieldHom h isPrimeFormGram_one σ} := hPsi ▸ hNC hv₀N
    rw [he _ hv₀N (hNC hv₀N)]
    have := hΘ ⟨g₀, hg₀O⟩ 1 hα
    rw [map_one, map_one, mul_one] at this
    rw [← this]
    congr 1
    exact Subtype.ext hPsi.symm
  set v₀ := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    (fixedIsometryHom h hCl ⟨g₀, hg₀O⟩) with hv₀
  have hv₀E : v₀ ∈ E := by
    obtain ⟨y, hy, hye⟩ := hg₀E
    have : y = ⟨v₀, hv₀N⟩ := e.injective (Subtype.ext (by rw [hev₀]; exact hye))
    rw [this] at hy
    exact (mem_inf.mp (mem_subgroupOf.mp hy)).1
  have hv₀X : v₀ ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    hNinn hv₀N
  have hv₀1 : v₀ ≠ 1 := by
    intro h1
    have h2 : conjAut n h.fixedField g₀ = 1 := by
      rw [← hev₀]
      have : (⟨v₀, hv₀N⟩ : ((primeFormConjHom h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)).comp (fixedIsometryHom h hCl)).range) = 1 := Subtype.ext h1
      rw [this, map_one]
      rfl
    obtain ⟨a, ha⟩ := (conjAut_eq_one_iff (by omega) g₀).mp h2
    have := congrFun (congrFun (congrArg (fun x : GL (Fin n) h.fixedField =>
      (x : Matrix (Fin n) (Fin n) h.fixedField)) ha) ⟨0, by omega⟩) ⟨1, by omega⟩
    simp [GeneralLinearGroup.coe_scalar, hg₀, radicalMatrix, vecMulVec_apply, onesVec_apply]
      at this
    exact hμ this.symm
  have hv₀2 : orderOf v₀ = 2 := by
    refine orderOf_eq_prime ?_ hv₀1
    have hgg : (⟨g₀, hg₀O⟩ : matrixIsometryGroup
        ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)) ^ 2 = 1 :=
      Subtype.ext (Units.ext (by
        rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, sq, hg₀,
          radicalMatrix_mul_self hev (by simp) μ]
        rfl))
    rw [hv₀, ← map_pow, ← map_pow, hgg, map_one, map_one]
  have hOv₀ := even_unitary_all_involution_full_centralizer_odd_core h isPrimeFormGram_one
    (by omega) hq (H := inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    le_rfl v₀ hv₀X hv₀2
  have hCv₀ := hc.centralizer_le_normalizer hXn hv₀E hv₀1 hOv₀
  have hR : (((fixedIsometryHom h hCl ⟨g₀, hg₀O⟩ : primeFormUnitary h _) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + (μ : K) • vecMulVec onesVec onesVec := by
    rw [coe_fixedIsometryHom]
    change ((g₀ : Matrix (Fin n) (Fin n) h.fixedField)).map h.fixedField.subtype = _
    rw [hg₀, map_radicalMatrix_zero]
  by_cases hn4 : n = 4
  · subst hn4
    exact false_of_root_four_bar h hc.elemAbelian σ hσ hγ hR hCv₀
  · exact false_of_root_six_bar h (by obtain ⟨r, hr⟩ := hev; omega) hc.elemAbelian σ hσ hγ hR hCv₀

end Config

end CFSG.ComponentClassification.RankTwoHypIIUnitary
