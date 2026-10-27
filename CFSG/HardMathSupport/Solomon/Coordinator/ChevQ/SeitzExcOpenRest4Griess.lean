module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Case3
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwTorus
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Killed
public import CFSG.LieType.SeitzGeneration.HyperEx
public import CFSG.LieType.SeitzGeneration.HeisLinearFourier

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups commutatorElement

section SL5

variable {K : Type} [Field K]

private theorem comm_aux {R : Type*} [Ring R] (p q r : R) (hpp : p * p = 0) (hqq : q * q = 0)
    (hqp : q * p = 0) (hpq : p * q = r) (hrp : r * p = 0) (hrq : r * q = 0) :
    (1 + p) * (1 + q) * (1 + -p) * (1 + -q) = 1 + r := by
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_one, one_mul, hpp, hqq, hqp, hpq, hrp, hrq,
    add_zero]
  abel

theorem tv_commutator {i a j : Fin 5} (hia : i ≠ a) (haj : a ≠ j) (hij : i ≠ j) (s t : K) :
    ⁅SpecialLinearGroup.transvection hia s, SpecialLinearGroup.transvection haj t⁆ =
      SpecialLinearGroup.transvection hij (s * t) := by
  rw [commutatorElement_def, SpecialLinearGroup.transvection_inv,
    SpecialLinearGroup.transvection_inv]
  have h : ((SpecialLinearGroup.transvection hia s * SpecialLinearGroup.transvection haj t *
      SpecialLinearGroup.transvection hia (-s) * SpecialLinearGroup.transvection haj (-t) :
        SL(5, K)) : Matrix (Fin 5) (Fin 5) K) = 1 + single i j (s * t) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe]
    rw [← single_neg, ← single_neg]
    exact comm_aux (single i a s) (single a j t) (single i j (s * t))
      (single_mul_single_of_ne _ _ _ _ hia.symm _) (single_mul_single_of_ne _ _ _ _ haj.symm _)
      (single_mul_single_of_ne _ _ _ _ hij.symm _) (single_mul_single_same _ _ _ _ _)
      (single_mul_single_of_ne _ _ _ _ hij.symm _) (single_mul_single_of_ne _ _ _ _ haj.symm _)
  exact Subtype.ext (h.trans (SpecialLinearGroup.transvection_coe hij (s * t)).symm)

theorem tv_inj {i j : Fin 5} (hij : i ≠ j) {s t : K}
    (h : SpecialLinearGroup.transvection hij s = SpecialLinearGroup.transvection hij t) :
    s = t := by
  have h' := congrArg (fun A : SL(5, K) => (A : Matrix (Fin 5) (Fin 5) K) i j) h
  simpa [SpecialLinearGroup.transvection_coe, one_apply_ne hij] using h'

@[expose] def rotSL : SL(5, K) :=
  ⟨((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K, by
    rw [det_permutation, Equiv.Perm.sign_inv, sign_finRotate]
    norm_num⟩

theorem coe_rotSL : ((rotSL : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
    ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K := rfl

theorem rotSL_mul_single (i j : Fin 5) (t : K) :
    (((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) * single i j t =
      single (finRotate 5 i) (finRotate 5 j) t *
        (((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp only [submatrix_apply, id, single_apply]
  have e1 : (i = ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)) a) ↔ (finRotate 5 i = a) := by
    rw [Equiv.Perm.inv_def, Equiv.eq_symm_apply]
  have e2 : (finRotate 5 j = (((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)) : Fin 5 ≃ Fin 5).symm b) ↔
      (j = b) := by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]
    exact (finRotate 5).injective.eq_iff
  by_cases h1 : finRotate 5 i = a <;> by_cases h2 : j = b
  · rw [if_pos ⟨e1.2 h1, h2⟩, if_pos ⟨h1, e2.2 h2⟩]
  · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 (e2.1 h.2))]
  · rw [if_neg (fun h => h1 (e1.1 h.1)), if_neg (fun h => h1 h.1)]
  · rw [if_neg (fun h => h1 (e1.1 h.1)), if_neg (fun h => h1 h.1)]

theorem rotSL_conj_tv {i j : Fin 5} (hij : i ≠ j) (t : K) :
    rotSL * SpecialLinearGroup.transvection hij t * rotSL⁻¹ =
      SpecialLinearGroup.transvection ((finRotate 5).injective.ne hij) t := by
  rw [mul_inv_eq_iff_eq_mul]
  have h : ((rotSL * SpecialLinearGroup.transvection hij t : SL(5, K)) :
      Matrix (Fin 5) (Fin 5) K) =
      ((SpecialLinearGroup.transvection ((finRotate 5).injective.ne hij) t * rotSL : SL(5, K)) :
        Matrix (Fin 5) (Fin 5) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      coe_rotSL]
    rw [mul_add, add_mul, mul_one, one_mul, rotSL_mul_single]
  exact Subtype.ext h

theorem fourier_comm_rotSL {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {B : SL(5, K)} {t : Fin 5 → K}
    (hB : (B : Matrix (Fin 5) (Fin 5) K) * heisFourierMat ζ = heisFourierMat ζ * diagonal t) :
    B * rotSL = rotSL * B := by
  set Φ : Matrix (Fin 5) (Fin 5) K := heisFourierMat ζ with hΦ
  set S : Matrix (Fin 5) (Fin 5) K := heisShiftMat K 5 with hS
  set D : Matrix (Fin 5) (Fin 5) K := diagonal fun j : Fin 5 => ζ ^ (j : ℕ) with hD
  have hdet : IsUnit Φ.det := isUnit_iff_ne_zero.2 (det_heisFourierMat_ne_zero hζ)
  have hΦi : Φ * Φ⁻¹ = 1 := mul_nonsing_inv Φ hdet
  have hiΦ : Φ⁻¹ * Φ = 1 := nonsing_inv_mul Φ hdet
  have hSΦ : S * Φ = Φ * D := heisShiftMat_mul_heisFourierMat hζ.pow_eq_one
  have hBe : (B : Matrix (Fin 5) (Fin 5) K) = Φ * diagonal t * Φ⁻¹ := by
    rw [← hB, mul_assoc, hΦi, mul_one]
  have hSe : S = Φ * D * Φ⁻¹ := by rw [← hSΦ, mul_assoc, hΦi, mul_one]
  have hcomm : (B : Matrix (Fin 5) (Fin 5) K) * S = S * B := by
    rw [hBe, hSe]
    have hdd : diagonal t * D = D * diagonal t := by
      rw [hD, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext k
      ring
    calc Φ * diagonal t * Φ⁻¹ * (Φ * D * Φ⁻¹) = Φ * (diagonal t * D) * Φ⁻¹ := by
          simp only [mul_assoc]
          rw [← mul_assoc Φ⁻¹ Φ, hiΦ, one_mul]
      _ = Φ * (D * diagonal t) * Φ⁻¹ := by rw [hdd]
      _ = Φ * D * Φ⁻¹ * (Φ * diagonal t * Φ⁻¹) := by
          simp only [mul_assoc]
          rw [← mul_assoc Φ⁻¹ Φ, hiΦ, one_mul]
  have hPS : (((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) * S = 1 := by
    rw [hS, heisShiftMat, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  have hSP : S * (((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K) = 1 := by
    rw [hS, heisShiftMat, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  set P : Matrix (Fin 5) (Fin 5) K := ((finRotate 5)⁻¹ : Equiv.Perm (Fin 5)).permMatrix K with hP
  have h : ((B * rotSL : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) =
      ((rotSL * B : SL(5, K)) : Matrix (Fin 5) (Fin 5) K) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rotSL]
    calc (B : Matrix (Fin 5) (Fin 5) K) * P = P * S * (B * P) := by
          rw [hPS, one_mul]
      _ = P * (S * B) * P := by simp only [mul_assoc]
      _ = P * (B * S) * P := by rw [hcomm]
      _ = P * B * (S * P) := by simp only [mul_assoc]
      _ = P * B := by rw [hSP, mul_one]
  exact Subtype.ext h

theorem conjDiagn_conjDiagn (d e : Fin 5 → Kˣ) (A : SL(5, K)) :
    conjDiagn d (conjDiagn e A) = conjDiagn (d * e) A := by
  have h : (conjDiagnHom d).comp (conjDiagnHom e) = conjDiagnHom (d * e) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.comp_apply, conjDiagnHom_apply]
    rw [conjDiagn_transvection, conjDiagn_transvection, conjDiagn_transvection]
    congr 1
    simp only [Pi.mul_apply, Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

theorem conjDiagn_one' (A : SL(5, K)) : conjDiagn (1 : Fin 5 → Kˣ) A = A := by
  have h : conjDiagnHom (1 : Fin 5 → Kˣ) = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.id_apply, conjDiagnHom_apply]
    rw [conjDiagn_transvection]
    congr 1
    simp
  exact DFunLike.congr_fun h A

theorem conjDiagn_inv_conjDiagn (d : Fin 5 → Kˣ) (A : SL(5, K)) :
    conjDiagn d⁻¹ (conjDiagn d A) = A := by
  rw [conjDiagn_conjDiagn, inv_mul_cancel, conjDiagn_one']

theorem conjDiagn_conjDiagn_inv (d : Fin 5 → Kˣ) (A : SL(5, K)) :
    conjDiagn d (conjDiagn d⁻¹ A) = A := by
  rw [conjDiagn_conjDiagn, mul_inv_cancel, conjDiagn_one']

theorem conjDiagn_of_diagonal (d : Fin 5 → Kˣ) {A : SL(5, K)} {t : Fin 5 → K}
    (hA : (A : Matrix (Fin 5) (Fin 5) K) = diagonal t) : conjDiagn d A = A := by
  apply Subtype.ext
  rw [coe_conjDiagn, hA]
  change diagonal (fun i => (d i : K)) * diagonal t * diagonal (fun i => (((d i)⁻¹ : Kˣ) : K)) =
    diagonal t
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  rw [Units.val_inv_eq_inv_val]
  field_simp

end SL5

section Signs

variable {K : Type} [Field K]

theorem exact_cocycle (μ : Fin 5 → Fin 5 → K) (hμ : ∀ i j, i ≠ j → μ i j ≠ 0)
    (h3 : ∀ i a j, i ≠ a → a ≠ j → i ≠ j → μ i j = μ i a * μ a j) :
    ∀ i j, i ≠ j → μ i j * (if j = 0 then 1 else μ j 0) = (if i = 0 then 1 else μ i 0) := by
  intro i j hij
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, if_neg hij, mul_one]
  · by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, if_neg hj]
      obtain ⟨a, ha0, haj⟩ : ∃ a : Fin 5, a ≠ 0 ∧ a ≠ j := by
        by_cases h1 : j = 1
        · exact ⟨2, by decide, by rw [h1]; decide⟩
        · exact ⟨1, by decide, Ne.symm h1⟩
      have e1 := h3 a 0 j ha0 (Ne.symm hj) haj
      have e2 := h3 a j 0 haj hj ha0
      have e3 : μ a 0 * 1 = μ a 0 * (μ 0 j * μ j 0) := by
        calc μ a 0 * 1 = μ a j * μ j 0 := by rw [mul_one, e2]
          _ = μ a 0 * μ 0 j * μ j 0 := by rw [e1]
          _ = μ a 0 * (μ 0 j * μ j 0) := by ring
      exact (mul_left_cancel₀ (hμ a 0 ha0) e3).symm
    · rw [if_neg hj, if_neg hi]
      exact (h3 i j 0 hij hj hi).symm

end Signs

section Fourier

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

@[expose] def SignConj (y : ModGL Tag.E8 K) (w : WeylGroup Tag.E8) : Prop :=
  ∀ α, IsRoot Tag.E8 α → ∃ η : ℤ, (η = 1 ∨ η = -1) ∧
    ∀ c : K, y * pinnedX Tag.E8 K α c * y⁻¹ = pinnedX Tag.E8 K (w • α) ((η : K) * c)

end Fourier

section SignConjProd

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

theorem signConj_one : SignConj (1 : ModGL Tag.E8 K) 1 := fun α _ =>
  ⟨1, Or.inl rfl, fun c => by simp⟩

theorem SignConj.mul {y₁ y₂ : ModGL Tag.E8 K} {w₁ w₂ : WeylGroup Tag.E8}
    (h₁ : SignConj y₁ w₁) (h₂ : SignConj y₂ w₂) : SignConj (y₁ * y₂) (w₁ * w₂) := by
  intro α hα
  obtain ⟨η₂, hη₂, h2⟩ := h₂ α hα
  obtain ⟨η₁, hη₁, h1⟩ := h₁ (w₂ • α) (IsRoot.smul hα w₂)
  refine ⟨η₁ * η₂, ?_, fun c => ?_⟩
  · rcases hη₁ with rfl | rfl <;> rcases hη₂ with rfl | rfl <;> simp
  · calc y₁ * y₂ * pinnedX Tag.E8 K α c * (y₁ * y₂)⁻¹
          = y₁ * (y₂ * pinnedX Tag.E8 K α c * y₂⁻¹) * y₁⁻¹ := by group
      _ = y₁ * pinnedX Tag.E8 K (w₂ • α) ((η₂ : K) * c) * y₁⁻¹ := by rw [h2]
      _ = pinnedX Tag.E8 K (w₁ • w₂ • α) ((η₁ : K) * ((η₂ : K) * c)) := h1 _
      _ = pinnedX Tag.E8 K ((w₁ * w₂) • α) (((η₁ * η₂ : ℤ) : K) * c) := by
          rw [mul_smul]
          push_cast
          ring_nf

theorem SignConj.pow {y : ModGL Tag.E8 K} {w : WeylGroup Tag.E8} (h : SignConj y w) :
    ∀ n : ℕ, SignConj (y ^ n) (w ^ n)
  | 0 => by simpa using signConj_one
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact (SignConj.pow h n).mul h

theorem allRootWeylSign_E8 {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot Tag.E8 α) (i : Fin Tag.E8.rank) :
    allRootWeylSign Tag.E8 i α = 1 ∨ allRootWeylSign Tag.E8 i α = -1 := by
  have h := allRootWeylSign_eq hα i
  set F := rootOperatorFamily Tag.E8
  have h1 : F.pinnedFamilySign α * F.pinnedFamilySign α = 1 := by
    rcases F.pinnedFamilySign_eq α with h | h <;> rw [h] <;> norm_num
  have h2 : F.sign i ⟨α, hα⟩ * F.sign i ⟨α, hα⟩ = 1 := F.sign_mul_self i _
  have h3 : F.pinnedFamilySign (reflect Tag.E8 i α) * F.pinnedFamilySign (reflect Tag.E8 i α) = 1 := by
    rcases F.pinnedFamilySign_eq (reflect Tag.E8 i α) with h | h <;> rw [h] <;> norm_num
  have hsq : allRootWeylSign Tag.E8 i α * allRootWeylSign Tag.E8 i α = 1 := by
    rw [h]
    calc _ = (F.pinnedFamilySign α * F.pinnedFamilySign α) * (F.sign i ⟨α, hα⟩ * F.sign i ⟨α, hα⟩) *
        (F.pinnedFamilySign (reflect Tag.E8 i α) * F.pinnedFamilySign (reflect Tag.E8 i α)) := by
          ring
      _ = 1 := by rw [h1, h2, h3]; norm_num
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 hsq with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem signConj_weylElt (i : Fin Tag.E8.rank) :
    SignConj (weylElt Tag.E8 K i 1) (simple Tag.E8 i) := by
  intro α hα
  refine ⟨allRootWeylSign Tag.E8 i α, allRootWeylSign_E8 hα i, fun c => ?_⟩
  rw [weylElt_one_mul_pinnedX_mul_inv K i hα c, simple_smul]

theorem signConj_prod (ω : List (Fin Tag.E8.rank)) :
    SignConj ((ω.map fun i => weylElt Tag.E8 K i 1).prod)
      ((coxeterSystem Tag.E8).wordProd ω) := by
  induction ω with
  | nil => simpa using signConj_one
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons]
    exact (signConj_weylElt i).mul ih

theorem mapsRootLines_prod (ω : List (Fin Tag.E8.rank)) :
    MapsRootLines ((ω.map fun i => weylElt Tag.E8 K i 1).prod)
      ((coxeterSystem Tag.E8).wordProd ω) := by
  induction ω with
  | nil => simpa using (mapsRootLines_one (τ := Tag.E8) (R := K))
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons]
    exact (mapsRootLines_weylElt i).mul ih

theorem mapsRootLines_pow {g : ModGL Tag.E8 K} {w : WeylGroup Tag.E8} (h : MapsRootLines g w) :
    ∀ n : ℕ, MapsRootLines (g ^ n) (w ^ n)
  | 0 => by simpa using (mapsRootLines_one (τ := Tag.E8) (R := K))
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact (mapsRootLines_pow h n).mul h

theorem prod_weylElt_mem_monomial (ω : List (Fin Tag.E8.rank)) :
    (ω.map fun i => weylElt Tag.E8 K i 1).prod ∈ monomialSubgroup Tag.E8 K := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact weylElt_mem_monomialSubgroup i

theorem prod_weylElt_mem_adjointGroup (ω : List (Fin Tag.E8.rank)) :
    (ω.map fun i => weylElt Tag.E8 K i 1).prod ∈ adjointGroup Tag.E8 K := by
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact weylElt_mem_adjointGroup i 1

end SignConjProd

section Torus

variable {K : Type} [Field K]

theorem prod_zpow_eq_zpow_sum' {ι : Type*} (s : Finset ι) (u : Kˣ) (n : ι → ℤ) :
    ∏ k ∈ s, u ^ n k = u ^ (∑ k ∈ s, n k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, _root_.zpow_add]

theorem rootChar_powVec (u : Kˣ) (c : Fin Tag.E8.rank → ℕ) (v : Fin Tag.E8.rank → ℤ) :
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar (fun k => u ^ c k) v =
      u ^ (∑ k, (c k : ℤ) * v k) := by
  unfold CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar
  rw [← prod_zpow_eq_zpow_sum']
  refine Finset.prod_congr rfl fun k _ => ?_
  show (u ^ c k) ^ v k = u ^ ((c k : ℤ) * v k)
  rw [← zpow_natCast, ← _root_.zpow_mul]

theorem zpow_eq_zpow_of_modEq {u : Kˣ} (hu : IsPrimitiveRoot u 5) {n m : ℤ} (h : n % 5 = m % 5) :
    u ^ n = u ^ m := by
  have hd : (5 : ℤ) ∣ n - m := Int.ModEq.dvd h.symm
  have h1 : u ^ (n - m) = 1 := (hu.zpow_eq_one_iff_dvd _).2 (by exact_mod_cast hd)
  rw [_root_.zpow_sub, mul_inv_eq_one] at h1
  exact h1

end Torus

section Data

open CFSG.RankThree.E6 (chainRoot)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.RankThree.Lattice

@[expose] def griessWWord : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4,
    3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 1, 3, 2, 0]

@[expose] def griessVWord : List (Fin Tag.E8.rank) :=
  [7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3,
    4, 5, 2, 1, 3, 4, 0, 2, 3, 1]

@[expose] def czVec : Fin Tag.E8.rank → ℕ := ![0, 0, 0, 0, 1, 0, 0, 0]

@[expose] def cxVec : Fin Tag.E8.rank → ℕ := ![3, 3, 3, 3, 0, 1, 1, 1]

@[expose] def griessList1 : List (Fin Tag.E8.rank → ℤ) :=
  [![-2, -3, -3, -5, -4, -3, -2, -1], ![-1, -2, -2, -4, -3, -2, -1, 0],
    ![-1, -2, -2, -3, -3, -3, -2, -1], ![-1, -2, -2, -3, -2, -1, 0, 0],
    ![-1, -1, -1, -2, -2, -2, -2, -1], ![-1, -1, -1, -2, -1, 0, 0, 0],
    ![-1, -1, -1, -1, -1, -1, -1, -1], ![0, -1, -1, -2, -2, -2, -1, 0],
    ![0, -1, -1, -1, -1, -1, 0, 0], ![0, 0, 0, -1, -1, -1, -1, 0], ![0, 0, 0, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 0, 0], ![0, 1, 1, 2, 2, 2, 1, 0], ![1, 1, 1, 1, 1, 1, 1, 1],
    ![1, 1, 1, 2, 1, 0, 0, 0], ![1, 1, 1, 2, 2, 2, 2, 1], ![1, 2, 2, 3, 2, 1, 0, 0],
    ![1, 2, 2, 3, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1, 0], ![2, 3, 3, 5, 4, 3, 2, 1]]

@[expose] def griessSteps : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) :=
  [(![-1, -1, -1, -1, 0, 0, 0, 0], ![0, 0, 0, -1, -1, -1, -1, 0]),
    (![-1, 0, -1, -1, 0, 0, 0, 0], ![0, -1, -1, -1, -1, -1, 0, 0]),
    (![0, -1, -1, -1, 0, 0, 0, 0], ![0, 0, 0, -1, -1, -1, -1, 0]),
    (![0, 0, -1, 0, 0, 0, 0, 0], ![-1, -1, -1, -2, -1, 0, 0, 0]),
    (![0, 0, 0, -1, 0, 0, 0, 0], ![-1, -1, -1, -1, -1, -1, -1, -1]),
    (![0, 0, 0, -1, 0, 0, 0, 0], ![0, -1, -1, -1, -1, -1, 0, 0]),
    (![0, 0, 0, -1, 0, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 1, 1, 1]),
    (![0, 0, 1, 0, 0, 0, 0, 0], ![1, 1, 1, 2, 1, 0, 0, 0]),
    (![0, 1, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0]),
    (![1, 0, 1, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 1, 0, 0]),
    (![1, 1, 1, 1, 0, 0, 0, 0], ![-1, -1, -1, -2, -1, 0, 0, 0]),
    (![1, 1, 1, 1, 0, 0, 0, 0], ![0, 0, 0, 1, 1, 1, 1, 0]),
    (![-1, -1, -1, -1, 0, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, -1, -1, 0, 0, 0]),
    (![-1, -1, -1, -2, -1, -1, -1, 0], ![1, 1, 1, 2, 1, 1, 1, 1]),
    (![-1, -1, -2, -2, -1, -1, 0, 0], ![1, 1, 2, 2, 1, 0, 0, 0]),
    (![0, -1, -1, -2, -1, -1, -1, 0], ![0, 1, 1, 2, 1, 1, 0, 0]),
    (![-1, -1, -2, -2, -1, 0, 0, 0], ![1, 1, 2, 2, 1, 1, 0, 0]),
    (![-1, -1, -1, -2, -1, -1, -1, -1], ![1, 1, 1, 2, 1, 1, 1, 0]),
    (![0, -1, -1, -2, -1, -1, 0, 0], ![0, 1, 1, 2, 1, 1, 1, 0])]

@[expose] def ChainOK : List (Fin Tag.E8.rank → ℤ) →
    List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) → Prop
  | _, [] => True
  | S, (α, β) :: rest => (α ∈ S ∧ β ∈ S ∧ (∃ m : Fin 240, e8RootVec m = α) ∧
      (∃ m : Fin 240, e8RootVec m = β) ∧ (∃ m : Fin 240, e8RootVec m = α + β) ∧ α ≠ β ∧
      α ≠ -β) ∧ ChainOK (S ++ [α + β]) rest

instance ChainOK.decidable : ∀ S steps, Decidable (ChainOK S steps)
  | _, [] => isTrue trivial
  | S, (α, β) :: rest => by
      unfold ChainOK
      haveI := ChainOK.decidable (S ++ [α + β]) rest
      infer_instance

@[expose] def chainEnd : List (Fin Tag.E8.rank → ℤ) →
    List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)) → List (Fin Tag.E8.rank → ℤ)
  | S, [] => S
  | S, (α, β) :: rest => chainEnd (S ++ [α + β]) rest

theorem griessChain_ok : ChainOK (e8ListA ++ griessList1) griessSteps := by
  decide +kernel

theorem griessChain_targets : ∀ i : Fin Tag.E8.rank,
    Pi.single i 1 ∈ chainEnd (e8ListA ++ griessList1) griessSteps ∧
      -Pi.single i 1 ∈ chainEnd (e8ListA ++ griessList1) griessSteps := by
  decide +kernel

theorem griessW_sigmaA_data : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 griessWWord *ᵥ (wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 e8WordA *ᵥ chainRoot e8a4chain (i + 1) (j + 1) := by
  decide +kernel

theorem griessW_sigmaV_data : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 griessWWord *ᵥ (wordMat Tag.E8 griessVWord *ᵥ chainRoot e8a4chain i j) =
      wordMat Tag.E8 griessVWord *ᵥ chainRoot e8a4chain (i + 1) (j + 1) := by
  decide +kernel

theorem griessV_img : ∀ i j : Fin 5, i ≠ j →
    wordMat Tag.E8 griessVWord *ᵥ chainRoot e8a4chain i j ∈ griessList1 := by
  decide +kernel

theorem griessV_cover : ∀ r ∈ griessList1, ∃ i j : Fin 5, i ≠ j ∧
    r = wordMat Tag.E8 griessVWord *ᵥ chainRoot e8a4chain i j := by
  decide +kernel

theorem cz_wbA_data : ∀ i : Fin 5,
    (∑ k, (czVec k : ℤ) * (wordMat Tag.E8 e8WordA *ᵥ e8a4Weight i) k) % 5 = 2 := by
  decide +kernel

theorem cx_wbV_data : ∀ i : Fin 5,
    (∑ k, (cxVec k : ℤ) * (wordMat Tag.E8 griessVWord *ᵥ e8a4Weight i) k) % 5 = 4 := by
  decide +kernel

theorem cz_fixed_data : ∀ i : Fin Tag.E8.rank,
    (∑ k, (czVec k : ℤ) * (wordMat Tag.E8 griessWWord.reverse *ᵥ Pi.single i 1) k) % 5 =
      (czVec i : ℤ) % 5 := by
  decide +kernel

theorem cx_fixed_data : ∀ i : Fin Tag.E8.rank,
    (∑ k, (cxVec k : ℤ) * (wordMat Tag.E8 griessWWord.reverse *ᵥ Pi.single i 1) k) % 5 =
      (cxVec i : ℤ) % 5 := by
  decide +kernel

theorem griessW_pow_five_data : wordMat Tag.E8 griessWWord ^ 5 = 1 := by
  decide +kernel

theorem griessW_pow_ne_data : ∀ m ∈ ({1, 2, 3, 4} : Finset ℕ),
    wordMat Tag.E8 griessWWord ^ m *ᵥ (Pi.single 0 1 : Fin Tag.E8.rank → ℤ) ≠ Pi.single 0 1 := by
  decide +kernel

end Data

section Triple

variable {G : Type*} [Group G] {p : ℕ}

theorem pow_mul_pow_mul_pow_mul {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (i j k i' j' k' : ℕ) :
    a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') := by
  have h1 : c ^ k * a ^ i' = a ^ i' * c ^ k := ((hac.pow_pow i' k).eq).symm
  have h2 : b ^ j * a ^ i' = a ^ i' * b ^ j := ((hab.pow_pow i' j).eq).symm
  have h3 : c ^ k * b ^ j' = b ^ j' * c ^ k := ((hbc.pow_pow j' k).eq).symm
  calc a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k')
      = a ^ i * b ^ j * (c ^ k * a ^ i') * b ^ j' * c ^ k' := by simp only [mul_assoc]
    _ = a ^ i * (b ^ j * a ^ i') * c ^ k * b ^ j' * c ^ k' := by rw [h1]; simp only [mul_assoc]
    _ = a ^ i * a ^ i' * b ^ j * (c ^ k * b ^ j') * c ^ k' := by rw [h2]; simp only [mul_assoc]
    _ = a ^ i * a ^ i' * (b ^ j * b ^ j') * (c ^ k * c ^ k') := by rw [h3]; simp only [mul_assoc]
    _ = a ^ (i + i') * b ^ (j + j') * c ^ (k + k') := by rw [pow_add, pow_add, pow_add]

theorem mem_closure_triple_iff [hp : Fact p.Prime] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (g : G) : g ∈ Subgroup.closure ({a, b, c} : Set G) ↔
      ∃ v : Fin p × Fin p × Fin p, a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ) = g := by
  have hp1 : 1 < p := hp.out.one_lt
  set S : Set G := Set.range fun v : Fin p × Fin p × Fin p =>
    a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ) with hS
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨⟨i, j, k⟩, rfl⟩ _ ⟨⟨i', j', k'⟩, rfl⟩
    refine ⟨⟨⟨(i + i' : ℕ) % p, Nat.mod_lt _ (by omega)⟩, ⟨(j + j' : ℕ) % p,
      Nat.mod_lt _ (by omega)⟩, ⟨(k + k' : ℕ) % p, Nat.mod_lt _ (by omega)⟩⟩, ?_⟩
    simp only
    rw [pow_mul_pow_mul_pow_mul hab hac hbc, ← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb,
      ← pow_eq_pow_mod _ hc]
  have hone : (1 : G) ∈ S :=
    ⟨⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩⟩, by simp⟩
  have hpowp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨⟨i, j, k⟩, rfl⟩
    simp only
    have hbc' : Commute (b ^ (j : ℕ)) (c ^ (k : ℕ)) := hbc.pow_pow _ _
    have habc : Commute (a ^ (i : ℕ)) (b ^ (j : ℕ) * c ^ (k : ℕ)) :=
      (hab.pow_pow _ _).mul_right (hac.pow_pow _ _)
    rw [mul_assoc, habc.mul_pow, hbc'.mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm (i : ℕ),
      mul_comm (j : ℕ), mul_comm (k : ℕ), pow_mul, pow_mul, pow_mul, ha, hb, hc]
    simp
  have hpow : ∀ x ∈ S, ∀ n : ℕ, x ^ n ∈ S := by
    intro x hx n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  let T : Subgroup G :=
    { carrier := S
      mul_mem' := fun hx hy => hmul _ hx _ hy
      one_mem' := hone
      inv_mem' := by
        intro x hx
        have hx1 : x⁻¹ = x ^ (p - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel (by omega),
            hpowp x hx]
        rw [hx1]
        exact hpow x hx _ }
  have hle : Subgroup.closure ({a, b, c} : Set G) ≤ T := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨⟨⟨1, hp1⟩, ⟨0, by omega⟩, ⟨0, by omega⟩⟩, by simp⟩
    · exact ⟨⟨⟨0, by omega⟩, ⟨1, hp1⟩, ⟨0, by omega⟩⟩, by simp⟩
    · exact ⟨⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨1, hp1⟩⟩, by simp⟩
  constructor
  · intro hg
    exact hle hg
  · rintro ⟨⟨i, j, k⟩, rfl⟩
    have ha' : a ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
    have hb' : b ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
    have hc' : c ∈ Subgroup.closure ({a, b, c} : Set G) := Subgroup.subset_closure (by simp)
    exact mul_mem (mul_mem (pow_mem ha' _) (pow_mem hb' _)) (pow_mem hc' _)

theorem closure_triple_facts [hp : Fact p.Prime] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hinj : Function.Injective fun v : Fin p × Fin p × Fin p =>
      a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ)) :
    Nat.card (Subgroup.closure ({a, b, c} : Set G)) = p ^ 3 := by
  have hset : (Subgroup.closure ({a, b, c} : Set G) : Set G) = Set.range fun v : Fin p × Fin p ×
      Fin p => a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ) := by
    ext g
    rw [SetLike.mem_coe, mem_closure_triple_iff hab hac hbc ha hb hc]
    rfl
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_fin]
  ring

end Triple

section Pair

variable {G : Type*} [Group G] {p : ℕ}

theorem mem_closure_pair_iff [hp : Fact p.Prime] {a b : G} (hab : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (g : G) : g ∈ Subgroup.closure ({a, b} : Set G) ↔
      ∃ v : Fin p × Fin p, a ^ (v.1 : ℕ) * b ^ (v.2 : ℕ) = g := by
  have hp1 : 1 < p := hp.out.one_lt
  have heq : Subgroup.closure ({a, b} : Set G) = Subgroup.closure ({a, b, 1} : Set G) := by
    refine le_antisymm (Subgroup.closure_mono (by intro x hx; rcases hx with rfl | rfl <;> simp))
      ((Subgroup.closure_le _).2 ?_)
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact one_mem _
  rw [heq, mem_closure_triple_iff hab (Commute.one_right a) (Commute.one_right b) ha hb (one_pow p)]
  constructor
  · rintro ⟨⟨i, j, k⟩, rfl⟩
    exact ⟨⟨i, j⟩, by simp⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨⟨i, j, ⟨0, by omega⟩⟩, by simp⟩

theorem card_closure_pair [hp : Fact p.Prime] {a b : G} (hab : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hinj : Function.Injective fun v : Fin p × Fin p => a ^ (v.1 : ℕ) * b ^ (v.2 : ℕ)) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  have hset : (Subgroup.closure ({a, b} : Set G) : Set G) = Set.range fun v : Fin p × Fin p =>
      a ^ (v.1 : ℕ) * b ^ (v.2 : ℕ) := by
    ext g
    rw [SetLike.mem_coe, mem_closure_pair_iff hab ha hb]
    rfl
  rw [← SetLike.coe_sort_coe, hset, Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_fin]
  ring

theorem relIndex_of_card {F E : Subgroup G} (hFE : F ≤ E) (hF : Nat.card F = p ^ 2)
    (hE : Nat.card E = p ^ 3) (hp : 0 < p) : F.relIndex E = p := by
  have h := Subgroup.relIndex_mul_card (H := F) (K := E)
  rw [inf_eq_left.2 hFE, hF, hE] at h
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have : F.relIndex E * p ^ 2 = p * p ^ 2 := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp2 this

theorem pair_injective_of_triple {a b c : G} (hp : 0 < p)
    (hinj : Function.Injective fun v : Fin p × Fin p × Fin p =>
      a ^ (v.1 : ℕ) * b ^ (v.2.1 : ℕ) * c ^ (v.2.2 : ℕ)) :
    (Function.Injective fun v : Fin p × Fin p => a ^ (v.1 : ℕ) * b ^ (v.2 : ℕ)) ∧
      (Function.Injective fun v : Fin p × Fin p => a ^ (v.1 : ℕ) * c ^ (v.2 : ℕ)) ∧
      (Function.Injective fun v : Fin p × Fin p => b ^ (v.1 : ℕ) * c ^ (v.2 : ℕ)) := by
  refine ⟨fun v w h => ?_, fun v w h => ?_, fun v w h => ?_⟩
  · have := @hinj (v.1, v.2, ⟨0, hp⟩) (w.1, w.2, ⟨0, hp⟩) (by simpa using h)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 this.2.1
  · have := @hinj (v.1, ⟨0, hp⟩, v.2) (w.1, ⟨0, hp⟩, w.2) (by simpa using h)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 this.2.2
  · have := @hinj (⟨0, hp⟩, v.1, v.2) (⟨0, hp⟩, w.1, w.2) (by simpa using h)
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.2.1 this.2.2

theorem mem_hyperClosure_pair {E : Subgroup G} {a b : G}
    (hle : Subgroup.closure ({a, b} : Set G) ≤ E)
    (hidx : (Subgroup.closure ({a, b} : Set G)).relIndex E = p) {k : G}
    (ha : a * k = k * a) (hb : b * k = k * b) : k ∈ hyperClosure p ⊤ E := by
  refine Subgroup.subset_closure ⟨Subgroup.mem_top k, _, hle, hidx, fun f hf => ?_⟩
  have hc : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer {k} := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 ha
    · exact Subgroup.mem_centralizer_singleton_iff.2 hb
  exact Subgroup.mem_centralizer_singleton_iff.1 (hc hf)

end Pair

section GriessDefs

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable (K : Type) [Field K]

set_option linter.unusedSectionVars false

@[expose] noncomputable def griessY0 : ModGL Tag.E8 K :=
  (griessWWord.map fun i => weylElt Tag.E8 K i 1).prod

@[expose] noncomputable def griessY : ModGL Tag.E8 K := griessY0 K ^ 6

variable {K} {ζ : K}

@[expose] noncomputable def griessU (hζ : IsPrimitiveRoot ζ 5) : Kˣ :=
  Units.mk0 ζ (hζ.ne_zero (by norm_num))

@[expose] noncomputable def griessZ (hζ : IsPrimitiveRoot ζ 5) : ModGL Tag.E8 K :=
  rootDiagUnit Tag.E8 fun k => griessU hζ ^ czVec k

@[expose] noncomputable def griessX (hζ : IsPrimitiveRoot ζ 5) : ModGL Tag.E8 K :=
  rootDiagUnit Tag.E8 fun k => griessU hζ ^ cxVec k

end GriessDefs

section Griess

open CFSG.RankThree.E6 (chainRoot)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.RankThree.Lattice
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

set_option linter.unusedSectionVars false

@[expose] noncomputable def griessW : WeylGroup Tag.E8 :=
  (coxeterSystem Tag.E8).wordProd griessWWord

@[expose] noncomputable def griessV : WeylGroup Tag.E8 :=
  (coxeterSystem Tag.E8).wordProd griessVWord

theorem griessW_smul (u : Fin Tag.E8.rank → ℤ) : griessW • u = wordMat Tag.E8 griessWWord *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 griessWWord u

theorem griessV_smul (u : Fin Tag.E8.rank → ℤ) : griessV • u = wordMat Tag.E8 griessVWord *ᵥ u :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 griessVWord u

theorem griessW_pow_smul (n : ℕ) (u : Fin Tag.E8.rank → ℤ) :
    (griessW ^ n) • u = (wordMat Tag.E8 griessWWord ^ n) *ᵥ u := by
  induction n generalizing u with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_smul, griessW_smul, ih, pow_succ, Matrix.mulVec_mulVec]

theorem griessW_pow_five : griessW ^ 5 = 1 := by
  apply eq_of_smul_eq_smul (α := Fin Tag.E8.rank → ℤ)
  intro u
  rw [griessW_pow_smul, griessW_pow_five_data, Matrix.one_mulVec, one_smul]

theorem griessW_pow_ne {m : ℕ} (hm : m ∈ ({1, 2, 3, 4} : Finset ℕ)) : griessW ^ m ≠ 1 := by
  intro h
  apply griessW_pow_ne_data m hm
  rw [← griessW_pow_smul, h, one_smul]

theorem orderOf_griessW : orderOf griessW = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime griessW_pow_five (by simpa using griessW_pow_ne (m := 1) (by decide))

theorem griessW_pow_six : griessW ^ 6 = griessW := by
  rw [pow_succ, griessW_pow_five, one_mul]

theorem rot5 (i : Fin 5) : finRotate 5 i = i + 1 := finRotate_succ_apply i

theorem griessW_sigmaA {i j : Fin 5} (hij : i ≠ j) :
    griessW • sigmaRootE8A4 e8VA i j = sigmaRootE8A4 e8VA (finRotate 5 i) (finRotate 5 j) := by
  rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, griessW_smul, e8VA_smul, e8VA_smul, rot5, rot5]
  exact griessW_sigmaA_data i j hij

theorem griessW_sigmaV {i j : Fin 5} (hij : i ≠ j) :
    griessW • sigmaRootE8A4 griessV i j = sigmaRootE8A4 griessV (finRotate 5 i) (finRotate 5 j) := by
  rw [sigmaRootE8A4_eq_smul, sigmaRootE8A4_eq_smul, griessW_smul, griessV_smul, griessV_smul,
    rot5, rot5]
  exact griessW_sigmaV_data i j hij

theorem sigmaSet_e8VA : sigmaSetE8A4 e8VA = {r | r ∈ e8ListA} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, e8VA_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact e8A_img i j hij
  · intro hr
    exact e8A_cover r hr

theorem sigmaSet_griessV : sigmaSetE8A4 griessV = {r | r ∈ griessList1} := by
  rw [sigmaSetE8A4_eq]
  ext r
  simp only [Set.mem_ofPred_eq, sigmaRootE8A4_eq_smul, griessV_smul]
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact griessV_img i j hij
  · intro hr
    exact griessV_cover r hr

theorem e8_cartan_inv : ∃ B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ,
    B * Tag.E8.cartan = 1 :=
  ⟨!![4, 5, 7, 10, 8, 6, 4, 2; 5, 8, 10, 15, 12, 9, 6, 3; 7, 10, 14, 20, 16, 12, 8, 4;
    10, 15, 20, 30, 24, 18, 12, 6; 8, 12, 16, 24, 20, 15, 10, 5; 6, 9, 12, 18, 15, 12, 8, 4;
    4, 6, 8, 12, 10, 8, 6, 3; 2, 3, 4, 6, 5, 4, 3, 2], by decide +kernel⟩

theorem rootDiagUnit_mem_torus_E8 (a : Fin Tag.E8.rank → Kˣ) :
    rootDiagUnit Tag.E8 a ∈ torusGroup Tag.E8 K :=
  CFSG.HardMathSupport.Timmesfeld.CrossChar.rootDiagUnit_mem_torusGroup_of_unimodular
    e8_cartan_inv.choose_spec a

theorem torusGroup_le_adjointGroup_E8' : torusGroup Tag.E8 K ≤ adjointGroup Tag.E8 K :=
  (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2

theorem rootDiagUnit_pow (a : Fin Tag.E8.rank → Kˣ) (n : ℕ) :
    rootDiagUnit Tag.E8 a ^ n = rootDiagUnit Tag.E8 (a ^ n) := by
  induction n with
  | zero => simp [rootDiagUnit_one]
  | succ n ih => rw [pow_succ, ih, ← rootDiagUnit_mul, pow_succ]

theorem rootDiagUnit_inj {a b : Fin Tag.E8.rank → Kˣ}
    (h : rootDiagUnit Tag.E8 a = rootDiagUnit Tag.E8 b) : a = b := by
  funext i
  have ha := rootDiagUnit_conj_pinnedX a (isRoot_single Tag.E8 i) (1 : K)
  have hb := rootDiagUnit_conj_pinnedX b (isRoot_single Tag.E8 i) (1 : K)
  rw [h, hb] at ha
  have := pinnedX_injective (τ := Tag.E8) (R := K) _ ha
  have e : ∀ c : Fin Tag.E8.rank → Kˣ,
      rootChar c (Pi.single i 1) = c i := fun c => by
    simpa using rootChar_nsmul_single c i 1
  rw [e a, e b, mul_one, mul_one] at this
  exact Units.ext this.symm

theorem griessY0_mono : griessY0 K ∈ monomialSubgroup Tag.E8 K := prod_weylElt_mem_monomial _

theorem griessY_mono : griessY K ∈ monomialSubgroup Tag.E8 K := pow_mem griessY0_mono _

theorem griessY_mem : griessY K ∈ adjointGroup Tag.E8 K :=
  pow_mem (prod_weylElt_mem_adjointGroup _) _

theorem griessY0_sign : SignConj (griessY0 K) griessW := signConj_prod _

theorem griessY_sign : SignConj (griessY K) griessW := by
  have h := (griessY0_sign (K := K)).pow 6
  rwa [griessW_pow_six] at h

theorem griessY0_maps : MapsRootLines (griessY0 K) griessW := mapsRootLines_prod _

theorem weylQuotient_griessY :
    weylQuotientHom Tag.E8 K ⟨griessY K, griessY_mono⟩ = griessW := by
  apply weylQuotientHom_eq
  have h := mapsRootLines_pow (griessY0_maps (K := K)) 6
  rwa [griessW_pow_six] at h

theorem griessY_pow_five : griessY K ^ 5 = 1 := by
  set t := griessY0 K ^ 5 with ht
  have htm : t ∈ monomialSubgroup Tag.E8 K := pow_mem griessY0_mono _
  have hw1 : weylQuotientHom Tag.E8 K ⟨t, htm⟩ = 1 := by
    apply weylQuotientHom_eq
    have h := mapsRootLines_pow (griessY0_maps (K := K)) 5
    rwa [griessW_pow_five] at h
  have htT : t ∈ torusGroup Tag.E8 K :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_torusGroup_of_weylQuotientHom_eq_one htm hw1
  obtain ⟨a, ha⟩ := CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup htT
  have hsign : SignConj t 1 := by
    have h := (griessY0_sign (K := K)).pow 5
    rwa [griessW_pow_five] at h
  have hsq : a * a = 1 := by
    funext i
    obtain ⟨η, hη, hc⟩ := hsign _ (isRoot_single Tag.E8 i)
    have h1 := hc 1
    rw [← ha, rootDiagUnit_conj_pinnedX a (isRoot_single Tag.E8 i), one_smul] at h1
    have h2 := pinnedX_injective (τ := Tag.E8) (R := K) _ h1
    have e : rootChar a (Pi.single i 1) = a i := by simpa using rootChar_nsmul_single a i 1
    rw [e, mul_one, mul_one] at h2
    apply Units.ext
    simp only [Pi.mul_apply, Units.val_mul, Pi.one_apply, Units.val_one]
    rw [h2]
    rcases hη with rfl | rfl <;> norm_num
  have ht2 : t * t = 1 := by rw [← ha, ← rootDiagUnit_mul, hsq, rootDiagUnit_one]
  have h1 : ∀ s : ModGL Tag.E8 K, (s ^ 6) ^ 5 = (s ^ 5 * s ^ 5) ^ 3 := fun s => by
    rw [← pow_mul, ← pow_add, ← pow_mul]
  have h3 : griessY K ^ 5 = (t * t) ^ 3 := h1 (griessY0 K)
  rw [h3, ht2, one_pow]

variable {ζ : K}

theorem griessU_prim (hζ : IsPrimitiveRoot ζ 5) : IsPrimitiveRoot (griessU hζ) 5 :=
  IsPrimitiveRoot.coe_units_iff.1 (by simpa [griessU] using hζ)

theorem griessZ_torus (hζ : IsPrimitiveRoot ζ 5) : griessZ hζ ∈ torusGroup Tag.E8 K :=
  rootDiagUnit_mem_torus_E8 _

theorem griessX_torus (hζ : IsPrimitiveRoot ζ 5) : griessX hζ ∈ torusGroup Tag.E8 K :=
  rootDiagUnit_mem_torus_E8 _

theorem pow_five_vec (hζ : IsPrimitiveRoot ζ 5) (c : Fin Tag.E8.rank → ℕ) :
    (fun k => griessU hζ ^ c k) ^ 5 = 1 := by
  funext k
  simp only [Pi.pow_apply, Pi.one_apply]
  rw [← pow_mul, mul_comm, pow_mul, (griessU_prim hζ).pow_eq_one, one_pow]

theorem griessZ_pow_five (hζ : IsPrimitiveRoot ζ 5) : griessZ hζ ^ 5 = 1 := by
  rw [griessZ, rootDiagUnit_pow, pow_five_vec, rootDiagUnit_one]

theorem griessX_pow_five (hζ : IsPrimitiveRoot ζ 5) : griessX hζ ^ 5 = 1 := by
  rw [griessX, rootDiagUnit_pow, pow_five_vec, rootDiagUnit_one]

theorem weylAct_griessW_fixed (hζ : IsPrimitiveRoot ζ 5) (c : Fin Tag.E8.rank → ℕ)
    (hc : ∀ i : Fin Tag.E8.rank,
      (∑ k, (c k : ℤ) * (wordMat Tag.E8 griessWWord.reverse *ᵥ Pi.single i 1) k) % 5 =
        (c i : ℤ) % 5) :
    CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct griessW (fun k => griessU hζ ^ c k) =
      fun k => griessU hζ ^ c k := by
  funext i
  simp only [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct]
  have hinv : griessW⁻¹ = (coxeterSystem Tag.E8).wordProd griessWWord.reverse := by
    rw [CoxeterSystem.wordProd_reverse]
    rfl
  rw [hinv, wordProd_smul_eq_wordMat_mulVec, rootChar_powVec, ← zpow_natCast]
  exact zpow_eq_zpow_of_modEq (griessU_prim hζ) (by rw [hc i])

theorem griessY_comm_rootDiagUnit (hζ : IsPrimitiveRoot ζ 5) (c : Fin Tag.E8.rank → ℕ)
    (hc : ∀ i : Fin Tag.E8.rank,
      (∑ k, (c k : ℤ) * (wordMat Tag.E8 griessWWord.reverse *ᵥ Pi.single i 1) k) % 5 =
        (c i : ℤ) % 5) :
    griessY K * rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) =
      rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) * griessY K := by
  have h := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
    (⟨griessY K, griessY_mono⟩ : monomialSubgroup Tag.E8 K)
    (fun k => griessU hζ ^ c k)
  rw [weylQuotient_griessY, weylAct_griessW_fixed hζ c hc] at h
  calc griessY K * rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k)
      = griessY K * rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) * (griessY K)⁻¹ *
          griessY K := by group
    _ = _ := by rw [h]

theorem griessY_comm_Z (hζ : IsPrimitiveRoot ζ 5) : griessY K * griessZ hζ = griessZ hζ * griessY K :=
  griessY_comm_rootDiagUnit hζ czVec cz_fixed_data

theorem griessY_comm_X (hζ : IsPrimitiveRoot ζ 5) : griessY K * griessX hζ = griessX hζ * griessY K :=
  griessY_comm_rootDiagUnit hζ cxVec cx_fixed_data

theorem griessZ_comm_X (hζ : IsPrimitiveRoot ζ 5) : griessZ hζ * griessX hζ = griessX hζ * griessZ hζ := by
  rw [griessZ, griessX, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem conjDiagn_const (d : Fin 5 → Kˣ) (hd : ∀ i j, d i = d j) (A : SL(5, K)) :
    conjDiagn d A = A := by
  have h : conjDiagnHom d = MonoidHom.id _ := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := K)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.id_apply, conjDiagnHom_apply]
    rw [conjDiagn_transvection, hd i j]
    congr 1
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  exact DFunLike.congr_fun h A

theorem rootDiagUnit_comm_rho (hζ : IsPrimitiveRoot ζ 5) (v : WeylGroup Tag.E8)
    (c : Fin Tag.E8.rank → ℕ) (m : ℤ)
    (hc : ∀ i : Fin 5, (∑ k, (c k : ℤ) * (wbE8A4 v i) k) % 5 = m) (A : SL(5, K)) :
    rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) * rhoSigmaE8A4 K v A =
      rhoSigmaE8A4 K v A * rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) := by
  have h := rhoSigmaE8A4_torus (L := K) v (fun k => griessU hζ ^ c k) A
  rw [conjDiagn_const _ (fun i j => by
    rw [rootChar_powVec, rootChar_powVec]
    exact zpow_eq_zpow_of_modEq (griessU_prim hζ) (by rw [hc i, hc j]))] at h
  calc rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) * rhoSigmaE8A4 K v A
      = rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) * rhoSigmaE8A4 K v A *
          (rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k))⁻¹ *
          rootDiagUnit Tag.E8 (fun k => griessU hζ ^ c k) := by group
    _ = _ := by rw [h]

theorem griessZ_comm_rhoA (hζ : IsPrimitiveRoot ζ 5) (A : SL(5, K)) :
    griessZ hζ * rhoSigmaE8A4 K e8VA A = rhoSigmaE8A4 K e8VA A * griessZ hζ :=
  rootDiagUnit_comm_rho hζ e8VA czVec 2 (fun i => by
    rw [show wbE8A4 e8VA i = wordMat Tag.E8 e8WordA *ᵥ e8a4Weight i from e8VA_smul _]
    exact cz_wbA_data i) A

theorem griessX_comm_rhoV (hζ : IsPrimitiveRoot ζ 5) (A : SL(5, K)) :
    griessX hζ * rhoSigmaE8A4 K griessV A = rhoSigmaE8A4 K griessV A * griessX hζ :=
  rootDiagUnit_comm_rho hζ griessV cxVec 4 (fun i => by
    rw [show wbE8A4 griessV i = wordMat Tag.E8 griessVWord *ᵥ e8a4Weight i from griessV_smul _]
    exact cx_wbV_data i) A

@[expose] noncomputable def griessZA (hζ : IsPrimitiveRoot ζ 5) : adjointGroup Tag.E8 K :=
  ⟨griessZ hζ, torusGroup_le_adjointGroup_E8' (griessZ_torus hζ)⟩

@[expose] noncomputable def griessXA (hζ : IsPrimitiveRoot ζ 5) : adjointGroup Tag.E8 K :=
  ⟨griessX hζ, torusGroup_le_adjointGroup_E8' (griessX_torus hζ)⟩

theorem griessZA_comm_XA (hζ : IsPrimitiveRoot ζ 5) : Commute (griessZA hζ) (griessXA hζ) :=
  Subtype.ext (griessZ_comm_X hζ)

theorem griessZA_pow (hζ : IsPrimitiveRoot ζ 5) : griessZA hζ ^ 5 = 1 :=
  Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact griessZ_pow_five hζ)

theorem griessXA_pow (hζ : IsPrimitiveRoot ζ 5) : griessXA hζ ^ 5 = 1 :=
  Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact griessX_pow_five hζ)

theorem chain_le (H : Subgroup (ModGL Tag.E8 K)) :
    ∀ (steps : List ((Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)))
      (S : List (Fin Tag.E8.rank → ℤ)), ChainOK S steps →
      (∀ r ∈ S, rootSubgroup Tag.E8 K r ≤ H) →
      ∀ r ∈ chainEnd S steps, rootSubgroup Tag.E8 K r ≤ H := by
  intro steps
  induction steps with
  | nil => intro S _ hS; exact hS
  | cons st rest ih =>
    obtain ⟨α, β⟩ := st
    intro S hok hS
    obtain ⟨⟨hαS, hβS, hα, hβ, hαβ, hne, hne'⟩, hrest⟩ := hok
    refine ih (S ++ [α + β]) hrest fun r hr => ?_
    rcases List.mem_append.1 hr with hr | hr
    · exact hS r hr
    · rw [List.mem_singleton.1 hr]
      exact DetectE8.rootSubgroup_add_le_E8 H (isRoot_iff_exists_e8RootVec.2 hα)
        (isRoot_iff_exists_e8RootVec.2 hβ) hne hne' (isRoot_iff_exists_e8RootVec.2 hαβ)
        (hS α hαS) (hS β hβS)

end Griess

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess

end
