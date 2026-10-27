module

public import CFSG.RankThree.PartTwo.Census.Carrier.D4EvenLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZW

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even

section Dconj
variable {K : Type} [Field K]

@[expose] def dconjMat (a : Kˣ) (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  !![M 0 0, (a : K) * M 0 1; ((a⁻¹ : Kˣ) : K) * M 1 0, M 1 1]

theorem dconjMat_mul (a : Kˣ) (M N : Matrix (Fin 2) (Fin 2) K) :
    dconjMat a (M * N) = dconjMat a M * dconjMat a N := by
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dconjMat, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | field_simp | (field_simp; ring1)

theorem dconjMat_one (a : Kˣ) : dconjMat a (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dconjMat]

theorem det_dconjMat (a : Kˣ) (M : Matrix (Fin 2) (Fin 2) K) :
    (dconjMat a M).det = M.det := by
  have ha : (a : K) * ((a⁻¹ : Kˣ) : K) = 1 := by simp
  rw [Matrix.det_fin_two M]
  simp only [dconjMat, Matrix.det_fin_two_of]
  linear_combination (-(M 0 1 * M 1 0)) * ha

@[expose] def dconj (a : Kˣ) : SL2 K →* SL2 K where
  toFun X := ⟨dconjMat a X, by rw [det_dconjMat]; exact X.2⟩
  map_one' := Subtype.ext (by
    show dconjMat a (1 : Matrix (Fin 2) (Fin 2) K) = 1
    exact dconjMat_one a)
  map_mul' X Y := Subtype.ext (by
    show dconjMat a ((X * Y : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      dconjMat a (X : Matrix (Fin 2) (Fin 2) K) * dconjMat a (Y : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact dconjMat_mul a _ _)

theorem coe_dconj (a : Kˣ) (X : SL2 K) : ((dconj a X : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
    !![(X : Matrix (Fin 2) (Fin 2) K) 0 0, (a : K) * (X : Matrix (Fin 2) (Fin 2) K) 0 1;
      ((a⁻¹ : Kˣ) : K) * (X : Matrix (Fin 2) (Fin 2) K) 1 0, (X : Matrix (Fin 2) (Fin 2) K) 1 1] := rfl

theorem dconj_uSL (a : Kˣ) (c : K) : dconj a (uSL c) = uSL ((a : K) * c) :=
  SL2_ext (by simp [coe_dconj, coe_uSL]) (by simp [coe_dconj, coe_uSL]) (by simp [coe_dconj, coe_uSL])
    (by simp [coe_dconj, coe_uSL])

theorem dconj_vSL (a : Kˣ) (c : K) : dconj a (vSL c) = vSL (((a⁻¹ : Kˣ) : K) * c) :=
  SL2_ext (by simp [coe_dconj, coe_vSL]) (by simp [coe_dconj, coe_vSL]) (by simp [coe_dconj, coe_vSL])
    (by simp [coe_dconj, coe_vSL])

theorem dconj_one_apply (X : SL2 K) : dconj 1 X = X :=
  SL2_ext (by simp [coe_dconj]) (by simp [coe_dconj]) (by simp [coe_dconj]) (by simp [coe_dconj])

end Dconj

section Torus

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem torus_conj_rho (b : Fin Tag.D4.rank → Kˣ) (j : Fin Tag.D4.rank) (X : SL2 K) :
    rootDiagUnit Tag.D4 b * ρ j X * (rootDiagUnit Tag.D4 b)⁻¹ = ρ j (dconj (b j) X) := by
  have key : (MulAut.conj (rootDiagUnit Tag.D4 b)).toMonoidHom.comp (ρ j) =
      (ρ j).comp (dconj (b j)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower :
        Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) = ⊤) ?_
    rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · show rootDiagUnit Tag.D4 b * ρ j (uSL c) * (rootDiagUnit Tag.D4 b)⁻¹ =
        ρ j (dconj (b j) (uSL c))
      rw [simpleRootSL2_uSL, dconj_uSL, simpleRootSL2_uSL]
      exact (root_diagonal_conjugation Tag.D4 K b).1 j c
    · show rootDiagUnit Tag.D4 b * ρ j (vSL c) * (rootDiagUnit Tag.D4 b)⁻¹ =
        ρ j (dconj (b j) (vSL c))
      rw [simpleRootSL2_vSL, dconj_vSL, simpleRootSL2_vSL]
      exact (root_diagonal_conjugation Tag.D4 K b).2.1 j c
  exact DFunLike.congr_fun key X

theorem commute_rho_outer {i j : Fin Tag.D4.rank} (hi : i ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hj : j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hij : i ≠ j) (X Y : SL2 K) :
    Commute (ρ i X) (ρ j Y) :=
  commute_rankOneHom_outer K hi hj hij X Y

end Torus

section Aux

variable {K : Type} [Field K]

theorem sl2_comm_aux (t t' : K) (ht : t ≠ 0) (W : SL2 K)
    (hu : W * uSL (1 : K) = uSL t * W) (hv : W * vSL (1 : K) = vSL t' * W) :
    (W : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (W : Matrix (Fin 2) (Fin 2) K) 0 0 = t * (W : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  have hu00 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 0) hu
  have hu01 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 1) hu
  have hv00 := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) 0 0) hv
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at hu00 hu01 hv00
  have h10 : (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have : t * (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination (-1 : K) * hu00
    exact (mul_eq_zero.1 this).resolve_left ht
  refine ⟨by linear_combination hv00, h10, by linear_combination hu01⟩

end Aux

section Factor

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem factor_diag (hK2 : ringChar K ≠ 2) (b : Fin Tag.D4.rank → Kˣ) (j : Fin Tag.D4.rank)
    (W : SL2 K) (rest : ModGL Tag.D4 K) (hrest : ∀ X : SL2 K, Commute rest (ρ j X))
    (h : rootDiagUnit Tag.D4 b ^ 2 * (ρ j W * rest) = 1) :
    (W : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (W : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
      (W : Matrix (Fin 2) (Fin 2) K) 1 1 =
        ((b j : Kˣ) : K) ^ 2 * (W : Matrix (Fin 2) (Fin 2) K) 0 0 := by
  set T : ModGL Tag.D4 K := ρ j W * rest with hTdef
  have hT : T = rootDiagUnit Tag.D4 (b⁻¹ * b⁻¹) := by
    rw [rootDiagUnit_mul, ← CFSG.LieType.Chevalley.rootDiagUnit_inv, ← _root_.mul_inv_rev, ← pow_two]
    rw [← inv_pow] 
    exact eq_inv_of_mul_eq_one_right h
  have hconj : ∀ X : SL2 K, T * ρ j X * T⁻¹ = ρ j (W * X * W⁻¹) := by
    intro X
    rw [hTdef, _root_.mul_inv_rev, map_mul, map_mul, map_inv]
    calc ρ j W * rest * ρ j X * (rest⁻¹ * (ρ j W)⁻¹)
        = ρ j W * (rest * ρ j X * rest⁻¹) * (ρ j W)⁻¹ := by group
      _ = ρ j W * ρ j X * (ρ j W)⁻¹ := by rw [(hrest X).eq, mul_inv_cancel_right]
  have hconj2 : ∀ X : SL2 K, ρ j (W * X * W⁻¹) =
      ρ j (dconj ((b⁻¹ * b⁻¹) j) X) := by
    intro X
    rw [← hconj, hT]
    exact torus_conj_rho (b⁻¹ * b⁻¹) j X
  have hX : ∀ X : SL2 K, W * X = dconj ((b⁻¹ * b⁻¹) j) X * W := by
    intro X
    have := simpleRootSL2_injective hK2 j (hconj2 X)
    rw [← this]
    group
  have ha : (((b⁻¹ * b⁻¹) j : Kˣ) : K) ≠ 0 := Units.ne_zero _
  obtain ⟨h01, h10, h00⟩ := sl2_comm_aux (((b⁻¹ * b⁻¹) j : Kˣ) : K)
    ((((b⁻¹ * b⁻¹) j)⁻¹ : Kˣ) * 1) ha W
    (by rw [hX, dconj_uSL, mul_one]) (by rw [hX, dconj_vSL])
  refine ⟨h01, h10, ?_⟩
  have hbj : ((b j : Kˣ) : K) ≠ 0 := Units.ne_zero _
  have e : (((b⁻¹ * b⁻¹) j : Kˣ) : K) = (((b j : Kˣ) : K)⁻¹) ^ 2 := by simp [sq]
  rw [e] at h00
  field_simp at h00 ⊢
  linear_combination (-1 : K) * h00

end Factor

section Matrices

variable {K : Type} [Field K]

theorem sl2_upper_conj {X : SL2 K} (hX : (X : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (c : K) :
    X * uSL c * X⁻¹ = uSL ((X : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * c) := by
  rw [mul_inv_eq_iff_eq_mul]
  have hdet := det_SL2 X
  rw [hX] at hdet
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two, hX]
  · linear_combination (-(c * (X : Matrix (Fin 2) (Fin 2) K) 0 0)) * hdet

theorem exists_eigen (g : Matrix (Fin 2) (Fin 2) K) (ν : K)
    (hg : g * g = (ν ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ v : Fin 2 → K, v ≠ 0 ∧ ∃ l : K, g.mulVec v = l • v := by
  by_cases h : g + ν • (1 : Matrix (Fin 2) (Fin 2) K) = 0
  · refine ⟨![1, 0], by simp [funext_iff, Fin.forall_fin_two], -ν, ?_⟩
    have : g = -ν • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h
    rw [this]
    ext i
    fin_cases i <;> simp
  · obtain ⟨w, hw⟩ : ∃ w : Fin 2 → K,
        (g + ν • (1 : Matrix (Fin 2) (Fin 2) K)).mulVec w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine h (Matrix.ext fun i j => ?_)
      have := congrFun (hcon (Pi.single j 1)) i
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    refine ⟨(g + ν • (1 : Matrix (Fin 2) (Fin 2) K)).mulVec w, hw, ν, ?_⟩
    rw [Matrix.mulVec_mulVec]
    have : g * (g + ν • (1 : Matrix (Fin 2) (Fin 2) K)) =
        ν • (g + ν • (1 : Matrix (Fin 2) (Fin 2) K)) := by
      calc g * (g + ν • (1 : Matrix (Fin 2) (Fin 2) K)) = g * g + ν • g := by
            rw [mul_add, Matrix.mul_smul, Matrix.mul_one]
        _ = ν • (g + ν • (1 : Matrix (Fin 2) (Fin 2) K)) := by
            rw [hg, smul_add, smul_smul, ← pow_two, add_comm]
    rw [this, Matrix.smul_mulVec]

end Matrices

section Split

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem xUnit_inj_d4 (i : Fin Tag.D4.rank) {c c' : K}
    (h : xUnit Tag.D4 K i c = xUnit Tag.D4 K i c') : c = c' :=
  adjX_injective (τ := Tag.D4) (K := K) i (Subtype.ext h)

theorem rootDiagUnit_eq_one_apply {c : Fin Tag.D4.rank → Kˣ} (h : rootDiagUnit Tag.D4 c = 1)
    (i : Fin Tag.D4.rank) : c i = 1 := by
  have e := (root_diagonal_conjugation Tag.D4 K c).1 i 1
  rw [h, one_mul, inv_one, mul_one] at e
  have := xUnit_inj_d4 i e
  exact Units.ext (by simpa using this.symm)

theorem exists_SL2_firstCol (v : Fin 2 → K) (hv : v ≠ 0) :
    ∃ e : SL2 K, (e : Matrix (Fin 2) (Fin 2) K) 0 0 = v 0 ∧ (e : Matrix (Fin 2) (Fin 2) K) 1 0 = v 1 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (by ext i; fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![v 0, -(v 1)⁻¹; v 1, 0], ?_⟩, by simp, by simp⟩
    rw [Matrix.det_fin_two_of]
    field_simp
    simp [h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, by simp, by simp⟩
    rw [Matrix.det_fin_two_of]
    field_simp
    simp

theorem upper_of_eigen (a : Kˣ) (A e : SL2 K) (l : K)
    (h0 : (a : K) * ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (e : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (e : Matrix (Fin 2) (Fin 2) K) 1 0) =
        l * (e : Matrix (Fin 2) (Fin 2) K) 0 0)
    (h1 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (e : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (e : Matrix (Fin 2) (Fin 2) K) 1 0 =
        l * (e : Matrix (Fin 2) (Fin 2) K) 1 0) :
    ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_dconj,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, inv_inv]
  linear_combination ((e : Matrix (Fin 2) (Fin 2) K) 0 0) * h1 - ((e : Matrix (Fin 2) (Fin 2) K) 1 0) * h0

theorem exists_upper (a : Kˣ) (A : SL2 K)
    (w01 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (w10 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (w11 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (a : K) ^ 2 * ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0)
    (ω : K) (hω : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 = ω ^ 2) :
    ∃ e : SL2 K, ((dconj a⁻¹ e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  have ha0 : (a : K) ≠ 0 := Units.ne_zero _
  have eW00 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (a : K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_dconj, Matrix.mul_apply, Fin.sum_univ_two]
  have eW01 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 0 1 =
      (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (a : K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_dconj, Matrix.mul_apply, Fin.sum_univ_two]
  have eW10 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_dconj, Matrix.mul_apply, Fin.sum_univ_two]
  have eW11 : ((dconj a⁻¹ A * A : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, coe_dconj, Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (a : K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
    rw [← eW01]; exact w01
  have e10 : (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [← eW10]; exact w10
  have e00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (a : K)⁻¹ * (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = ω ^ 2 := by
    rw [← eW00]; exact hω
  have e11 : (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) K) 1 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = (a : K) ^ 2 * ω ^ 2 := by
    rw [← eW11, w11, hω]
  have hainv : (a : K) * (a : K)⁻¹ = 1 := mul_inv_cancel₀ ha0
  have e00' : (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = (a : K) * ω ^ 2 := by
    linear_combination (a : K) * e00 -
      ((A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 0) * hainv
  have e01' : (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 := by
    linear_combination (a : K) * e01 -
      ((A : Matrix (Fin 2) (Fin 2) K) 0 1 * (A : Matrix (Fin 2) (Fin 2) K) 1 1) * hainv
  set g : Matrix (Fin 2) (Fin 2) K := !![(a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 0,
      (a : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 1; (A : Matrix (Fin 2) (Fin 2) K) 1 0,
      (A : Matrix (Fin 2) (Fin 2) K) 1 1] with hg
  have hgg : g * g = (((a : K) * ω) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hg, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (a : K) * e00'
    · linear_combination (a : K) * e01'
    · linear_combination e10
    · linear_combination e11
  obtain ⟨v, hv, l, hl⟩ := exists_eigen g ((a : K) * ω) hgg
  have hl0 := congrFun hl 0
  have hl1 := congrFun hl 1
  simp [hg, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hl0 hl1
  obtain ⟨e, he0, he1⟩ := exists_SL2_firstCol v hv
  refine ⟨e, upper_of_eigen a A e l ?_ ?_⟩
  · rw [he0, he1]; linear_combination hl0
  · rw [he0, he1]; linear_combination hl1

theorem conj_inv_rho (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) (X : SL2 K) :
    (rootDiagUnit Tag.D4 b)⁻¹ * ρ k X * rootDiagUnit Tag.D4 b = ρ k (dconj ((b k)⁻¹) X) := by
  have := torus_conj_rho b⁻¹ k X
  rw [← CFSG.LieType.Chevalley.rootDiagUnit_inv, inv_inv] at this
  simpa using this

theorem normalizes_of_upper (b : Fin Tag.D4.rank → Kˣ) (k : Fin Tag.D4.rank) (A e : SL2 K)
    (R : ModGL Tag.D4 K) (hR : ∀ Y : SL2 K, Commute R (ρ k Y))
    (hX10 : ((dconj ((b k)⁻¹) e⁻¹ * A * e : SL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (c : K) :
    ∃ c' : K, ((ρ k e)⁻¹ * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k e) * xUnit Tag.D4 K k c *
      ((ρ k e)⁻¹ * (rootDiagUnit Tag.D4 b * (ρ k A * R)) * ρ k e)⁻¹ = xUnit Tag.D4 K k c' := by
  set h : ModGL Tag.D4 K := rootDiagUnit Tag.D4 b with hh
  set X : SL2 K := dconj ((b k)⁻¹) e⁻¹ * A * e with hX
  have hn : (ρ k e)⁻¹ * (h * (ρ k A * R)) * ρ k e = h * ρ k X * R := by
    have e2 : (ρ k e)⁻¹ * h = h * ρ k (dconj ((b k)⁻¹) e⁻¹) := by
      have := conj_inv_rho b k e⁻¹
      rw [map_inv] at this
      calc (ρ k e)⁻¹ * h = h * (h⁻¹ * (ρ k e)⁻¹ * h) := by group
        _ = h * ρ k (dconj ((b k)⁻¹) e⁻¹) := by rw [hh, this]
    rw [hX, map_mul, map_mul]
    calc (ρ k e)⁻¹ * (h * (ρ k A * R)) * ρ k e
        = ((ρ k e)⁻¹ * h) * ρ k A * (R * ρ k e) := by group
      _ = ((ρ k e)⁻¹ * h) * ρ k A * (ρ k e * R) := by rw [(hR e).eq]
      _ = h * ρ k (dconj ((b k)⁻¹) e⁻¹) * ρ k A * ρ k e * R := by rw [e2]; group
      _ = _ := by group
  refine ⟨((b k : Kˣ) : K) * (((X : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2) * c), ?_⟩
  rw [hn, _root_.mul_inv_rev, _root_.mul_inv_rev]
  have hRx : R * ρ k (uSL c) * R⁻¹ = ρ k (uSL c) := by
    rw [(hR (uSL c)).eq, mul_inv_cancel_right]
  calc h * ρ k X * R * xUnit Tag.D4 K k c * (R⁻¹ * (ρ k X)⁻¹ * h⁻¹)
      = h * ρ k X * (R * ρ k (uSL c) * R⁻¹) * (ρ k X)⁻¹ * h⁻¹ := by
        rw [simpleRootSL2_uSL]; group
    _ = h * (ρ k X * ρ k (uSL c) * (ρ k X)⁻¹) * h⁻¹ := by rw [hRx]; group
    _ = h * ρ k (X * uSL c * X⁻¹) * h⁻¹ := by rw [← map_mul, ← map_inv, ← map_mul]
    _ = h * ρ k (uSL ((X : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * c)) * h⁻¹ := by
        rw [sl2_upper_conj hX10]
    _ = _ := by
        rw [simpleRootSL2_uSL]
        exact (root_diagonal_conjugation Tag.D4 K b).1 k _

end Split

end CFSG.LocalAnalysis.GLTheoremA
