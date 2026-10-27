module

public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Elements
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis.Field

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)
open CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

variable {ℓ f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem norm_one_ne_zero {x : F} (hx : h.bar x * x = 1) : x ≠ 0 := by
  rintro rfl
  rw [mul_zero] at hx
  exact zero_ne_one hx

theorem norm_one_mul {x y : F} (hx : h.bar x * x = 1) (hy : h.bar y * y = 1) :
    h.bar (x * y) * (x * y) = 1 := by
  rw [map_mul]
  linear_combination (h.bar y * y) * hx + hy

theorem norm_one_inv {x : F} (hx : h.bar x * x = 1) : h.bar x⁻¹ * x⁻¹ = 1 := by
  rw [map_inv₀, ← mul_inv, hx, inv_one]

theorem norm_one_div {x y : F} (hx : h.bar x * x = 1) (hy : h.bar y * y = 1) :
    h.bar (x / y) * (x / y) = 1 := by
  rw [div_eq_mul_inv]
  exact norm_one_mul hx (norm_one_inv hy)

theorem norm_one_neg {x : F} (hx : h.bar x * x = 1) : h.bar (-x) * (-x) = 1 := by
  rw [map_neg, neg_mul_neg, hx]

theorem norm_one_pow {x : F} (hx : h.bar x * x = 1) (n : ℕ) : h.bar (x ^ n) * x ^ n = 1 := by
  rw [map_pow, ← mul_pow, hx, one_pow]

theorem norm_one_map (σ : F ≃+* F) {x : F} (hx : h.bar x * x = 1) : h.bar (σ x) * σ x = 1 := by
  rw [← map_bar_comm, ← map_mul, hx, map_one]

theorem norm_one_vec {a b c : F} (ha : h.bar a * a = 1) (hb : h.bar b * b = 1)
    (hc : h.bar c * c = 1) : ∀ i, h.bar (![a, b, c] i) * ![a, b, c] i = 1 := by
  intro i
  fin_cases i
  exacts [ha, hb, hc]

section Torus

variable [Finite F] {σ : F ≃+* F} {ω : Fˣ} {D X : unitaryIsom3 h}

theorem exists_diag_cube_mem (hh : HeisHypU h σ 1 ω D X) {z : F} (hz : h.bar z * z = 1) :
    ∃ g : unitarySU ℓ f F 3, (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) ∧
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(z ^ 3)⁻¹, z ^ 3, 1] := by
  have hz₁ : h.bar (σ z) * σ z = 1 := norm_one_map σ hz
  have hz₂ : h.bar (σ (σ z)) * σ (σ z) = 1 := norm_one_map σ hz₁
  have hz0 := norm_one_ne_zero hz
  have hz₁0 := norm_one_ne_zero hz₁
  have hz₂0 := norm_one_ne_zero hz₂
  have h3z : σ (σ (σ z)) = z := σ_three hh z
  have hN : h.bar (z * σ z * σ (σ z)) * (z * σ z * σ (σ z)) = 1 :=
    norm_one_mul (norm_one_mul hz hz₁) hz₂
  have hσN : σ (z * σ z * σ (σ z)) = z * σ z * σ (σ z) := by
    rw [map_mul, map_mul, h3z]
    ring
  have hb : h.bar (σ (σ z) / z) * (σ (σ z) / z) = 1 := norm_one_div hz₂ hz
  have hσb : σ (σ (σ z) / z) = z / σ z := by rw [map_div₀, h3z]
  have hσσb : σ (σ (σ (σ z) / z)) = σ z / σ (σ z) := by rw [hσb, map_div₀]
  have hσσσb : σ (σ (σ (σ (σ z) / z))) = σ (σ z) / z := σ_three hh _
  let g₁ := diagSU (h := h) ![(z * σ z * σ (σ z))⁻¹, z * σ z * σ (σ z), 1]
    (norm_one_vec (norm_one_inv hN) hN (by rw [map_one, one_mul]))
    (by change (z * σ z * σ (σ z))⁻¹ * (z * σ z * σ (σ z)) * 1 = 1
        rw [mul_one, inv_mul_cancel₀ (norm_one_ne_zero hN)])
  let a := σ (σ z) / z
  let g₂ := diagSU (h := h) ![a, σ a, σ (σ a)]
    (norm_one_vec hb (norm_one_map σ hb) (norm_one_map σ (norm_one_map σ hb)))
    (by change a * σ a * σ (σ a) = 1
        simp only [a]
        rw [hσσb, hσb]
        field_simp)
  let g₃ := diagSU (h := h) ![σ a, σ (σ (σ a)), σ (σ a)]
    (norm_one_vec (norm_one_map σ hb) (norm_one_map σ (norm_one_map σ (norm_one_map σ hb)))
      (norm_one_map σ (norm_one_map σ hb)))
    (by change σ a * σ (σ (σ a)) * σ (σ a) = 1
        simp only [a]
        rw [hσσσb, hσσb, hσb]
        field_simp)
  let T := diagSU (h := h) ![(z ^ 3)⁻¹, z ^ 3, 1]
    (norm_one_vec (norm_one_inv (norm_one_pow hz 3)) (norm_one_pow hz 3)
      (by rw [map_one, one_mul]))
    (by change (z ^ 3)⁻¹ * z ^ 3 * 1 = 1
        rw [mul_one, inv_mul_cancel₀ (pow_ne_zero 3 hz0)])
  have h1 : (g₁ : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
    refine mem_liftU_of_fU_cD hh (c := 1) (one_pow 3) one_cube_norm ?_ (coe_diagSU _ _ _)
    rw [Units.val_one, one_smul, coe_diagSU, diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i
    · change σ (z * σ z * σ (σ z))⁻¹ = (z * σ z * σ (σ z))⁻¹
      rw [map_inv₀, hσN]
    · exact hσN
    · exact map_one σ
  have h2 : (g₂ : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) :=
    mem_liftU_twist₁ hh (coe_diagSU _ _ _)
  have h3 : (g₃ : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) :=
    mem_liftU_twist₂ hh (a := σ a) (coe_diagSU _ _ _)
  have hT : (T : GL (Fin 3) F) = g₁ * g₂ * (g₃ : GL (Fin 3) F)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagSU, coe_diagSU, coe_diagSU, coe_diagSU,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · change (z ^ 3)⁻¹ * σ a = (z * σ z * σ (σ z))⁻¹ * a
      simp only [a]
      rw [hσb]
      field_simp
    · change z ^ 3 * σ (σ (σ a)) = z * σ z * σ (σ z) * σ a
      simp only [a]
      rw [hσσσb, hσb]
      field_simp
    · change 1 * σ (σ a) = 1 * σ (σ a)
      rfl
  refine ⟨T, ?_, coe_diagSU _ _ _⟩
  rw [hT]
  exact mul_mem (mul_mem h1 h2) (inv_mem h3)

end Torus

section Fix

theorem bar_vω {ω : F} (hbω : h.bar ω = ω ^ 2) (hω3 : ω ^ 3 = 1) :
    (fun i => h.bar (vω ω i)) = vωb ω := by
  funext i
  fin_cases i
  · exact map_one h.bar
  · change h.bar (ω ^ 2) = ω
    rw [map_pow, hbω, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]
  · exact hbω

theorem bar_vωb {ω : F} (hbω : h.bar ω = ω ^ 2) (hω3 : ω ^ 3 = 1) :
    (fun i => h.bar (vωb ω i)) = vω ω := by
  funext i
  fin_cases i
  · exact map_one h.bar
  · exact hbω
  · change h.bar (ω ^ 2) = ω
    rw [map_pow, hbω, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hω3, one_mul]

theorem σ_vω (σ : F ≃+* F) {ω : F} (hσω : σ ω = ω) : (fun i => σ (vω ω i)) = vω ω := by
  funext i
  fin_cases i
  · exact map_one σ
  · change σ (ω ^ 2) = ω ^ 2
    rw [map_pow, hσω]
  · exact hσω

theorem σ_vωb (σ : F ≃+* F) {ω : F} (hσω : σ ω = ω) : (fun i => σ (vωb ω i)) = vωb ω := by
  funext i
  fin_cases i
  · exact map_one σ
  · exact hσω
  · change σ (ω ^ 2) = ω ^ 2
    rw [map_pow, hσω]

theorem map_homR_equiv (σ : F ≃+* F) (v w : Fin 3 → F) (c : F) :
    (homR v w c).map σ = homR (fun i => σ (v i)) (fun i => σ (w i)) (σ c) :=
  map_homR σ.toRingHom v w c

theorem unitary_homR {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0)
    (hbω : h.bar ω = ω ^ 2) {c : F} (hc : h.bar c * c = 1) :
    ((homR (vω ω) (vωb ω) c).map h.bar)ᵀ * homR (vω ω) (vωb ω) c = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  rw [map_homR, bar_vω hbω hω3, bar_vωb hbω hω3, transpose_homR, homR_mul h3 (dot_vωb_vω hω),
    hc, homR_one]

theorem unitary_homRb {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (h3 : (3 : F) ≠ 0)
    (hbω : h.bar ω = ω ^ 2) {c : F} (hc : h.bar c * c = 1) :
    ((homR (vωb ω) (vω ω) c).map h.bar)ᵀ * homR (vωb ω) (vω ω) c = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  rw [map_homR, bar_vωb hbω hω3, bar_vω hbω hω3, transpose_homR, homR_mul h3 (dot_vω_vωb hω),
    hc, homR_one]

theorem unitary_smul {M : Matrix (Fin 3) (Fin 3) F} (hM : (M.map h.bar)ᵀ * M = 1) {κ : F}
    (hκ : h.bar κ * κ = 1) : ((κ • M).map h.bar)ᵀ * (κ • M) = 1 := by
  have e : (κ • M).map h.bar = h.bar κ • M.map h.bar := by
    ext i j
    simp [map_mul]
  rw [e, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, hκ, one_smul]

theorem det_smul_three (κ : F) (M : Matrix (Fin 3) (Fin 3) F) : (κ • M).det = κ ^ 3 * M.det := by
  rw [Matrix.det_smul, Fintype.card_fin]

theorem map_σ_smul (σ : F ≃+* F) {M : Matrix (Fin 3) (Fin 3) F} (hM : M.map σ = M) {κ : F}
    (hκ : κ ≠ 0) : (κ • M).map σ = (σ κ / κ) • (κ • M) := by
  rw [smul_smul, div_mul_cancel₀ _ hκ]
  ext i j
  have e := congrFun (congrFun hM i) j
  simp only [Matrix.map_apply] at e
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, e]

theorem norm_one_dfix₀ {s : F} (hs : h.bar s * s = 1) (hs2 : 1 + 2 * s ≠ 0) :
    h.bar (s * (s + 2) / (1 + 2 * s)) * (s * (s + 2) / (1 + 2 * s)) = 1 := by
  have h1t : 1 + 2 * h.bar s ≠ 0 := by
    intro e
    apply hs2
    have := congrArg h.bar e
    rwa [map_add, map_mul, map_one, map_ofNat, map_zero, h.bar_bar] at this
  have e : h.bar (s * (s + 2) / (1 + 2 * s)) = h.bar s * (h.bar s + 2) / (1 + 2 * h.bar s) := by
    rw [map_div₀, map_mul, map_add, map_add, map_mul, map_one, map_ofNat]
  rw [e, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h1t hs2)]
  linear_combination (h.bar s * s + 1 + 2 * h.bar s + 2 * s) * hs

theorem unitary_dfix {ω s : F} (hωn : h.bar ω * ω = 1) (hs : h.bar s * s = 1)
    (hs2 : 1 + 2 * s ≠ 0) : ((dfix ω s).map h.bar)ᵀ * dfix ω s = 1 :=
  unitary_diagonal (norm_one_vec (norm_one_dfix₀ hs hs2) (norm_one_mul (norm_one_neg hωn) hs)
    (norm_one_mul (norm_one_neg (norm_one_pow hωn 2)) hs))

theorem bar_det_mul {M : Matrix (Fin 3) (Fin 3) F} (hM : (M.map h.bar)ᵀ * M = 1) :
    h.bar M.det * M.det = 1 := by
  have := congrArg Matrix.det hM
  have e : (M.map h.bar).det = h.bar M.det := (RingHom.map_det h.bar M).symm
  rwa [det_mul, det_transpose, det_one, e] at this

variable [Finite F] {σ : F ≃+* F} {ω : Fˣ} {D X : unitaryIsom3 h}

theorem exists_unit_ratio {κ u : F} (hκ0 : κ ≠ 0) (hκ3 : κ ^ 3 = u) (hσu : σ u = u)
    (hκ : h.bar κ * κ = 1) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ h.bar (c : F) * c = 1 ∧ (c : F) = σ κ / κ := by
  have hσκ0 : σ κ ≠ 0 := (map_ne_zero σ).2 hκ0
  refine ⟨Units.mk0 (σ κ / κ) (div_ne_zero hσκ0 hκ0), ?_, ?_, rfl⟩
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow, ← map_pow, hκ3, hσu, Units.val_one,
      div_self (by rw [← hκ3]; exact pow_ne_zero 3 hκ0)]
  · rw [Units.val_mk0]
    exact norm_one_div (norm_one_map σ hκ) hκ

theorem exists_fixer_mem (hh : HeisHypU h σ 1 ω D X) (h3 : 3 ∣ ℓ ^ f + 1)
    (hω : (ω : F) ^ 2 + ω + 1 = 0) (hbω : h.bar (ω : F) = (ω : F) ^ 2) {s : F} (hσs : σ s = s)
    (hs : h.bar s * s = 1) :
    ∃ (g : unitarySU ℓ f F 3) (κ : F), κ ≠ 0 ∧
      (g : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) ∧
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = κ • xfix (ω : F) s := by
  have h3F : (3 : F) ≠ 0 := three_ne_zero' h h3
  have hs0 := norm_one_ne_zero hs
  have hs2 : 1 + 2 * s ≠ 0 := one_add_two_mul_ne_zero h h3F hs
  have hω3 : (ω : F) ^ 3 = 1 := by linear_combination ((ω : F) - 1) * hω
  have hωn : h.bar (ω : F) * ω = 1 := by rw [hbω, ← pow_succ, hω3]
  have hσω : σ (ω : F) = ω := hh.fixω
  obtain ⟨κ₁, hκ₁3, hκ₁⟩ := exists_cube_root_of_fixed h hh.ord h3 hσs hs
  have hκ₁0 := norm_one_ne_zero hκ₁
  obtain ⟨c₁, hc₁3, hc₁n, hc₁⟩ := exists_unit_ratio (σ := σ) hκ₁0 hκ₁3 hσs hκ₁
  have hσinv : σ s⁻¹ = s⁻¹ := by rw [map_inv₀, hσs]
  have hR₁σ : (homR (vω (ω : F)) (vωb ω) s⁻¹).map σ = homR (vω (ω : F)) (vωb ω) s⁻¹ := by
    rw [map_homR_equiv, σ_vω σ hσω, σ_vωb σ hσω, hσinv]
  have hR₂σ : (homR (vωb (ω : F)) (vω ω) s⁻¹).map σ = homR (vωb (ω : F)) (vω ω) s⁻¹ := by
    rw [map_homR_equiv, σ_vω σ hσω, σ_vωb σ hσω, hσinv]
  let B₁ := suOf h (κ₁ • homR (vω (ω : F)) (vωb ω) s⁻¹)
    (unitary_smul (unitary_homR hω h3F hbω (norm_one_inv hs)) hκ₁)
    (by rw [det_smul_three, det_homR h3F (dot_vωb_vω hω), hκ₁3, mul_inv_cancel₀ hs0])
  let B₂ := suOf h (κ₁ • homR (vωb (ω : F)) (vω ω) s⁻¹)
    (unitary_smul (unitary_homRb hω h3F hbω (norm_one_inv hs)) hκ₁)
    (by rw [det_smul_three, det_homR h3F (dot_vω_vωb hω), hκ₁3, mul_inv_cancel₀ hs0])
  have hB₁ : (B₁ : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
    refine mem_liftU_of_fU_cX hh hc₁3 hc₁n ?_ ?_
    · rw [coe_suOf, map_σ_smul σ hR₁σ hκ₁0, hc₁]
    · rw [coe_suOf, Matrix.mul_smul, Matrix.smul_mul, permP_mul_homR_vω hω]
  have hB₂ : (B₂ : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
    refine mem_liftU_of_fU_cX hh hc₁3 hc₁n ?_ ?_
    · rw [coe_suOf, map_σ_smul σ hR₂σ hκ₁0, hc₁]
    · rw [coe_suOf, Matrix.mul_smul, Matrix.smul_mul, permP_mul_homR_vωb hω]
  have hdU := unitary_dfix (ω := (ω : F)) hωn hs hs2
  have hδn := bar_det_mul hdU
  have hδ0 := norm_one_ne_zero hδn
  have hdσ : (dfix (ω : F) s).map σ = dfix (ω : F) s := by
    rw [dfix, diagonal_map (map_zero σ)]
    congr 1
    funext i
    fin_cases i <;> simp [hσs, hσω, map_ofNat]
  have hσδ : σ (dfix (ω : F) s).det = (dfix (ω : F) s).det := by
    have e : σ (dfix (ω : F) s).det = ((dfix (ω : F) s).map σ).det :=
      RingHom.map_det σ.toRingHom _
    rw [e, hdσ]
  obtain ⟨κd, hκd3, hκd⟩ := exists_cube_root_of_fixed h hh.ord h3
    (u := ((dfix (ω : F) s).det)⁻¹) (by rw [map_inv₀, hσδ]) (norm_one_inv hδn)
  have hκd0 := norm_one_ne_zero hκd
  obtain ⟨cd, hcd3, hcdn, hcd⟩ := exists_unit_ratio (σ := σ) hκd0 hκd3
    (by rw [map_inv₀, hσδ]) hκd
  let Dd := suOf h (κd • dfix (ω : F) s) (unitary_smul hdU hκd)
    (by rw [det_smul_three, hκd3, inv_mul_cancel₀ hδ0])
  have hDd : (Dd : GL (Fin 3) F) ∈ liftU h (hyperFixU h σ D X) := by
    refine mem_liftU_of_fU_cD hh hcd3 hcdn ?_ (t := κd • ![s * (s + 2) / (1 + 2 * s),
      -(ω : F) * s, -(ω : F) ^ 2 * s]) ?_
    · rw [coe_suOf, map_σ_smul σ hdσ hκd0, hcd]
    · rw [coe_suOf, dfix, ← diagonal_smul]
  refine ⟨B₁ * Dd * B₂, κ₁ * κd * κ₁, mul_ne_zero (mul_ne_zero hκ₁0 hκd0) hκ₁0,
    mul_mem (mul_mem hB₁ hDd) hB₂, ?_⟩
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_suOf, coe_suOf,
    coe_suOf, xfix]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

end Fix

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.U3Heis
