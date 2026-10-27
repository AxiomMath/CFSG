module

public import CFSG.LieType.SeitzGeneration.UnitaryHeisGU2
public import CFSG.LieType.SeitzGeneration.UnitaryHeisB12

public section

open scoped commutatorElement MatrixGroups

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def homMat (h : UnitaryFieldData ℓ f K) (ρ κ : K) (w : Fin 3 → K) :
    Matrix (Fin 3) (Fin 3) K :=
  ρ • (1 : Matrix (Fin 3) (Fin 3) K) + κ • vecMulVec w (fun j => h.bar (w j))

theorem homMat_apply (h : UnitaryFieldData ℓ f K) (ρ κ : K) (w : Fin 3 → K) (i j : Fin 3) :
    homMat h ρ κ w i j = ρ * (1 : Matrix (Fin 3) (Fin 3) K) i j + κ * (w i * h.bar (w j)) := by
  simp [homMat, Matrix.vecMulVec_apply]

theorem homMat_unitary (h : UnitaryFieldData ℓ f K) {ρ κ n : K} (w : Fin 3 → K)
    (hρ : h.bar ρ * ρ = 1) (hcross : h.bar ρ * κ + h.bar κ * ρ + h.bar κ * κ * n = 0)
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = n) :
    ((homMat h ρ κ w).map h.bar)ᵀ * homMat h ρ κ w = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, homMat_apply,
    Fin.sum_univ_three, map_add, map_mul, h.bar_bar]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> grind

theorem det_homMat (h : UnitaryFieldData ℓ f K) {ρ κ n : K} (w : Fin 3 → K)
    (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = n) :
    (homMat h ρ κ w).det = ρ ^ 2 * (ρ + κ * n) := by
  rw [Matrix.det_fin_three]
  simp only [homMat_apply]
  simp
  grind

theorem conj_homMat (h : UnitaryFieldData ℓ f K) {ρ κ : K} (w : Fin 3 → K)
    {P : Matrix (Fin 3) (Fin 3) K} (hP : P * (P.map h.bar)ᵀ = 1) :
    P * homMat h ρ κ w * (P.map h.bar)ᵀ = homMat h ρ κ (P *ᵥ w) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, homMat_apply,
    Fin.sum_univ_three, Matrix.mulVec, dotProduct, map_add, map_mul]
  have h00 := congrFun (congrFun hP 0) 0
  have h01 := congrFun (congrFun hP 0) 1
  have h02 := congrFun (congrFun hP 0) 2
  have h10 := congrFun (congrFun hP 1) 0
  have h11 := congrFun (congrFun hP 1) 1
  have h12 := congrFun (congrFun hP 1) 2
  have h20 := congrFun (congrFun hP 2) 0
  have h21 := congrFun (congrFun hP 2) 1
  have h22 := congrFun (congrFun hP 2) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three,
    Matrix.one_apply] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  fin_cases i <;> fin_cases j <;> simp <;> grind

@[expose] def blockDetMat (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 3) (Fin 3) K :=
  !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, X.det⁻¹]

theorem blockDetMat_mul (X Y : Matrix (Fin 2) (Fin 2) K) :
    blockDetMat (X * Y) = blockDetMat X * blockDetMat Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDetMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.det_mul]
  ring

theorem blockDetMat_one : blockDetMat (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDetMat]

theorem blockDetMat_eq {X : Matrix (Fin 2) (Fin 2) K} {d : K} (hd : X.det⁻¹ = d) :
    blockDetMat X = !![X 0 0, X 0 1, 0; X 1 0, X 1 1, 0; 0, 0, d] := by
  rw [blockDetMat, hd]

@[expose] def blockDetHom : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := blockDetMat
  map_one' := blockDetMat_one
  map_mul' := blockDetMat_mul

@[expose] def blockDetGL : GL (Fin 2) K →* GL (Fin 3) K :=
  Units.map blockDetHom

theorem coe_blockDetGL (A : GL (Fin 2) K) :
    ((blockDetGL A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      blockDetMat (A : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem blockDetGL_eq_blockOneGL {A : GL (Fin 2) K}
    (hA : (A : Matrix (Fin 2) (Fin 2) K).det = 1) : blockDetGL A = blockOneGL A := by
  apply Units.ext
  rw [coe_blockDetGL, coe_blockOneGL, blockDetMat, hA, inv_one]
  rfl

theorem su2_conj_mem (h : UnitaryFieldData ℓ f K) (hp3 : ℓ ≠ 3)
    (h17 : 17 ≤ ℓ ^ f) {M : ℕ} (hM6 : 6 ≤ M) (hM : ℓ ^ f + 1 ≤ 3 * M)
    (H : Subgroup (GL (Fin 3) K)) (P : GL (Fin 3) K)
    {μ₁ μ₂ ν₁ ν₂ α β : K} (hμ₁ : h.bar μ₁ * μ₁ = 1) (hμ₂ : h.bar μ₂ * μ₂ = 1)
    (hν₁ : h.bar ν₁ * ν₁ = 1) (hν₂ : h.bar ν₂ * ν₂ = 1) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hμM : M ≤ orderOf (μ₁ / μ₂)) (hν3 : 3 ≤ orderOf (ν₁ / ν₂))
    {A B : GL (Fin 2) K}
    (hAm : (A : Matrix (Fin 2) (Fin 2) K) = diagonal ![μ₁, μ₂])
    (hBm : (B : Matrix (Fin 2) (Fin 2) K) =
      !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)])
    (hA : P * blockDetGL A * P⁻¹ ∈ H) (hB : P * blockDetGL B * P⁻¹ ∈ H) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → P * blockDetGL g * P⁻¹ ∈ H := by
  intro g hg
  have := su2_le_of_pair h hp3 h17 hM6 hM
    (H.comap ((MulAut.conj P).toMonoidHom.comp blockDetGL)) hμ₁ hμ₂ hν₁ hν₂ hαβ hα hβ hμM hν3
    hAm hBm hA hB g hg
  exact this

section Frame

variable (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def frameMat (α β : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, α, h.bar β; 0, β, -h.bar α; 1, 0, 0]

theorem frameMat_mul_star {α β : K} (hαβ : h.bar α * α + h.bar β * β = 1) :
    frameMat h α β * ((frameMat h α β).map h.bar)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar] <;> grind

theorem star_mul_frameMat {α β : K} (hαβ : h.bar α * α + h.bar β * β = 1) :
    ((frameMat h α β).map h.bar)ᵀ * frameMat h α β = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar] <;> grind

@[expose] noncomputable def frameGL {α β : K} (hαβ : h.bar α * α + h.bar β * β = 1) :
    GL (Fin 3) K :=
  ⟨frameMat h α β, ((frameMat h α β).map h.bar)ᵀ, frameMat_mul_star h hαβ,
    star_mul_frameMat h hαβ⟩

end Frame

section Identities

variable (h : UnitaryFieldData ℓ f K)

theorem blockDetMat_diagonal {lam a : K} (hlam : lam * a * a = 1) :
    blockDetMat (diagonal ![lam, a]) = homMat h a (lam - a) ![1, 0, 0] := by
  have hdet : (diagonal ![lam, a] : Matrix (Fin 2) (Fin 2) K).det⁻¹ = a := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact inv_eq_of_mul_eq_one_right hlam
  rw [blockDetMat_eq hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [homMat_apply]

theorem blockDetMat_homology {ν₁ ν₂ α β : K} (hαβ : h.bar α * α + h.bar β * β = 1)
    (hν : ν₁ * ν₂ * ν₂ = 1) :
    blockDetMat !![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)] =
      homMat h ν₂ (ν₁ - ν₂) ![α, β, 0] := by
  have hdet : (!![ν₂ + (ν₁ - ν₂) * (α * h.bar α), (ν₁ - ν₂) * (α * h.bar β);
        (ν₁ - ν₂) * (β * h.bar α), ν₂ + (ν₁ - ν₂) * (β * h.bar β)] :
        Matrix (Fin 2) (Fin 2) K).det⁻¹ = ν₂ := by
    rw [Matrix.det_fin_two_of]
    have : ((ν₂ + (ν₁ - ν₂) * (α * h.bar α)) * (ν₂ + (ν₁ - ν₂) * (β * h.bar β)) -
        (ν₁ - ν₂) * (α * h.bar β) * ((ν₁ - ν₂) * (β * h.bar α))) = ν₁ * ν₂ := by
      linear_combination (ν₂ * (ν₁ - ν₂)) * hαβ
    rw [this]
    exact inv_eq_of_mul_eq_one_right (by linear_combination hν)
  rw [blockDetMat_eq hdet]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [homMat_apply]

theorem frameMat_mulVec (α β s t : K) :
    frameMat h α β *ᵥ ![s, t, 0] = ![t * α, t * β, s] := by
  ext i
  fin_cases i <;> simp [frameMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]

theorem frame_conj_diagonal {α β a : K} (hαβ : h.bar α * α + h.bar β * β = 1) (ha0 : a ≠ 0) :
    frameMat h α β * blockDetMat (diagonal ![a⁻¹, a]) * ((frameMat h α β).map h.bar)ᵀ =
      blockDetMat !![1 + (a - 1) * (α * h.bar α), (a - 1) * (α * h.bar β);
        (a - 1) * (β * h.bar α), 1 + (a - 1) * (β * h.bar β)] := by
  have hd1 : (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det⁻¹ = 1 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  have hd2 : (!![1 + (a - 1) * (α * h.bar α), (a - 1) * (α * h.bar β);
      (a - 1) * (β * h.bar α), 1 + (a - 1) * (β * h.bar β)] : Matrix (Fin 2) (Fin 2) K).det⁻¹ =
      a⁻¹ := by
    rw [Matrix.det_fin_two_of]
    have : ((1 + (a - 1) * (α * h.bar α)) * (1 + (a - 1) * (β * h.bar β)) -
        (a - 1) * (α * h.bar β) * ((a - 1) * (β * h.bar α))) = a := by
      linear_combination (a - 1) * hαβ
    rw [this]
  rw [blockDetMat_eq hd1, blockDetMat_eq hd2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frameMat, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar] <;> grind

end Identities

theorem su2_block_mem_of_generic (h : UnitaryFieldData ℓ f K)
    (hp3 : ℓ ≠ 3) (h17 : 17 ≤ ℓ ^ f) (hq3 : 3 ∣ ℓ ^ f + 1) {a : K}
    (ha : orderOf a = ℓ ^ f + 1) (H : Subgroup (GL (Fin 3) K))
    (hH1 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hH3 : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {w : Fin 3 → K} (hw : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 + h.bar (w 2) * w 2 = 1)
    (hw0 : w 0 ≠ 0) (hw1 : w 1 ≠ 0) (hw2 : w 2 ≠ 0)
    (hnz : h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0)
    (hHw : ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) w) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → blockOneGL g ∈ H := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := h.card_eq_sq
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ha
    omega
  have hna : h.bar a * a = 1 := by
    rw [bar_mul_self_eq_pow, ← ha]
    exact pow_orderOf_eq_one a
  have hlam : a⁻¹ ^ 2 * a * a = 1 := by field_simp
  have hlamN : h.bar (a⁻¹ ^ 2) * a⁻¹ ^ 2 = 1 := by
    rw [map_pow, map_inv₀, ← mul_pow, ← mul_inv, hna, inv_one, one_pow]
  obtain ⟨M, hM3⟩ : ∃ M, ℓ ^ f + 1 = 3 * M := hq3
  have hM6 : 6 ≤ M := by omega
  have hratio : orderOf (a⁻¹ ^ 2 / a) = M := by
    set u : Kˣ := Units.mk0 a ha0 with hu
    have e : a⁻¹ ^ 2 / a = (((u ^ 3)⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hu, Units.val_mk0]
      field_simp
    have hou : orderOf u = ℓ ^ f + 1 := by rw [← ha, ← orderOf_units, hu, Units.val_mk0]
    rw [e, orderOf_units, orderOf_inv, orderOf_pow' _ (by norm_num), hou, hM3,
      Nat.gcd_eq_right (dvd_mul_right 3 M), Nat.mul_div_cancel_left M (by norm_num)]
  set d : K := h.bar (w 0) * w 0 + h.bar (w 1) * w 1 with hd
  have hdfix : h.bar d = d := by
    rw [hd, map_add, map_mul, map_mul, h.bar_bar, h.bar_bar]
    ring
  obtain ⟨c, hc⟩ : ∃ c : K, h.bar c * c = d := by
    have hfix : CFSG.LieType.BorelTits.unitaryInvolution K ℓ f d = d := by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply]
      exact hdfix
    obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed (p := ℓ) (f := f) hK
      hfix hnz
    refine ⟨c, ?_⟩
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h.bar_apply] at hc
    exact hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnz
    rw [← hc]
    simp
  have hbc : h.bar c ≠ 0 := by simpa using hc0
  have hαβ' : h.bar (w 0 / c) * (w 0 / c) + h.bar (w 1 / c) * (w 1 / c) = 1 := by
    rw [map_div₀, map_div₀]
    field_simp
    linear_combination -hc
  set α' : K := w 0 / c with hα'
  set β' : K := w 1 / c with hβ'
  have hα'0 : α' ≠ 0 := div_ne_zero hw0 hc0
  have hβ'0 : β' ≠ 0 := div_ne_zero hw1 hc0
  have hαc : c * α' = w 0 := by rw [hα']; field_simp
  have hβc : c * β' = w 1 := by rw [hβ']; field_simp
  set P₁ : GL (Fin 3) K := frameGL h hαβ' with hP₁
  have hαβ1 : h.bar (w 2) * w 2 + h.bar c * c = 1 := by
    rw [hc]
    linear_combination hw
  have hdiag0 : (diagonal ![a⁻¹ ^ 2, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  have hdetB : (!![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] :
      Matrix (Fin 2) (Fin 2) K).det = a⁻¹ ^ 2 * a := by
    rw [Matrix.det_fin_two_of]
    linear_combination (a * (a⁻¹ ^ 2 - a)) * hαβ1
  have hdetB0 : (!![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hdetB]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero ha0)) ha0
  let A₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![a⁻¹ ^ 2, a]) hdiag0
  let B₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
      (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] hdetB0
  have hPstar : ((P₁ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = frameMat h α' β' := rfl
  have hPinv : ((P₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((frameMat h α' β').map h.bar)ᵀ := rfl
  have hv1 : frameMat h α' β' *ᵥ ![1, 0, 0] = ![0, 0, 1] := by
    rw [frameMat_mulVec]
    simp
  have hS1 : ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → P₁ * blockDetGL g * P₁⁻¹ ∈ H := by
    refine su2_conj_mem h hp3 h17 hM6 (by omega) H P₁ hlamN hna hlamN hna hαβ1 hw2 hc0
      (by rw [hratio]) (by rw [hratio]; omega) (A := A₁) (B := B₁) rfl rfl ?_ ?_
    · obtain ⟨g, hg, hgm⟩ := hH3
      have : P₁ * blockDetGL A₁ * P₁⁻¹ = g := by
        apply Units.ext
        rw [hgm, Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL]
        change frameMat h α' β' * blockDetMat (diagonal ![a⁻¹ ^ 2, a]) * _ = _
        rw [blockDetMat_diagonal h hlam, conj_homMat h _ (frameMat_mul_star h hαβ'), hv1]
      rw [this]
      exact hg
    · obtain ⟨g, hg, hgm⟩ := hHw
      have : P₁ * blockDetGL B₁ * P₁⁻¹ = g := by
        apply Units.ext
        rw [hgm, Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL]
        change frameMat h α' β' *
          blockDetMat !![a + (a⁻¹ ^ 2 - a) * (w 2 * h.bar (w 2)), (a⁻¹ ^ 2 - a) * (w 2 * h.bar c);
            (a⁻¹ ^ 2 - a) * (c * h.bar (w 2)), a + (a⁻¹ ^ 2 - a) * (c * h.bar c)] * _ = _
        rw [blockDetMat_homology h hαβ1 hlam, conj_homMat h _ (frameMat_mul_star h hαβ'),
          frameMat_mulVec]
        have hvw : (![c * α', c * β', w 2] : Fin 3 → K) = w := by
          ext i
          fin_cases i <;> simp [hαc, hβc]
        rw [hvw]
      rw [this]
      exact hg
  have hxa : (!![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] :
      Matrix (Fin 2) (Fin 2) K).det = a := by
    rw [Matrix.det_fin_two_of]
    linear_combination (a - 1) * hαβ'
  have hxa0 : (!![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    rw [hxa]
    exact ha0
  let B₂ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1 + (a - 1) * (α' * h.bar α'), (a - 1) * (α' * h.bar β');
      (a - 1) * (β' * h.bar α'), 1 + (a - 1) * (β' * h.bar β')] hxa0
  have hD0 : (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
  let D₁ : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![a⁻¹, a]) hD0
  have hD₁ : D₁ ∈ unitarySU ℓ f K 2 := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · show (diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).det = 1
      simp [Matrix.det_diagonal, Fin.prod_univ_two, ha0]
    · show ((diagonal ![a⁻¹, a] : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * diagonal ![a⁻¹, a] = 1
      have hbi : (h.bar a)⁻¹ * a⁻¹ = 1 := by
        rw [← mul_inv, hna, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hbi, hna]
  have hS2 : ∀ g : GL (Fin 2) K, g ∈ unitarySU ℓ f K 2 → 1 * blockDetGL g * 1⁻¹ ∈ H := by
    refine su2_conj_mem h hp3 h17 hM6 (by omega) H 1 hlamN hna hna (by simp) hαβ' hα'0 hβ'0
      (by rw [hratio]) (by rw [div_one, ha]; omega) (A := A₁) (B := B₂) rfl rfl ?_ ?_
    · obtain ⟨g, hg, hgm⟩ := hH1
      have : 1 * blockDetGL A₁ * 1⁻¹ = g := by
        apply Units.ext
        rw [hgm, one_mul, inv_one, mul_one, coe_blockDetGL]
        exact blockDetMat_diagonal h hlam
      rw [this]
      exact hg
    · have hmem := hS1 D₁ hD₁
      have : 1 * blockDetGL B₂ * 1⁻¹ = P₁ * blockDetGL D₁ * P₁⁻¹ := by
        rw [one_mul, inv_one, mul_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hPstar, hPinv, coe_blockDetGL, coe_blockDetGL]
        change _ = frameMat h α' β' * blockDetMat (diagonal ![a⁻¹, a]) * _
        rw [frame_conj_diagonal h hαβ' ha0]
        rfl
      rw [this]
      exact hmem
  intro g hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := ((mem_unitarySU_iff h).1 hg).1
  have := hS2 g hg
  rw [blockDetGL_eq_blockOneGL hdet, one_mul, inv_one, mul_one] at this
  exact this
