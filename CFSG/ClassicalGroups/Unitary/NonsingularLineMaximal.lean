module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3GenU3
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs

public section

namespace CFSG.ClassicalGroups.Unitary

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Q3.TL4.E3C269G
  CFSG.RankThree.Classical CFSG.Open Matrix Subgroup

variable {p f : ℕ} {K : Type} [Field K]

private def stdUnit : Fin 3 → K := Pi.single 2 1

private theorem stdUnit_norm (h : UnitaryFieldData p f K) :
    stdHermForm h 3 (stdUnit (K := K)) (stdUnit (K := K)) = 1 := by
  rw [show stdUnit (K := K) = Pi.single 2 1 from rfl, stdHermForm_single]
  exact Pi.single_eq_same 2 1

private noncomputable def lineInv (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
  (2 : K) • ((stdHermForm h 3 x).smulRight x) - LinearMap.id

private theorem lineInv_apply (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (v : Fin 3 → K) :
    lineInv h hx v = ((2 : K) * (stdHermForm h 3 x v)) • x - v := by
  simp [lineInv, LinearMap.smulRight_apply, smul_smul]

private theorem lineInv_isometry (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (v w : Fin 3 → K) :
    stdHermForm h 3 (lineInv h hx v) (lineInv h hx w) = stdHermForm h 3 v w := by
  rw [lineInv_apply, lineInv_apply]
  have hsymm : stdHermForm h 3 v x = h.bar (stdHermForm h 3 x v) :=
    ((stdHermForm_isSymm h 3).eq x v).symm
  simp only [map_sub, map_add, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hx, mul_one, mul_zero, zero_mul, sub_zero, map_zero,
    RingHom.id_apply, hsymm, map_mul, map_ofNat]
  ring

private theorem lineInv_self (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) : lineInv h hx x = x := by
  rw [lineInv_apply, hx, mul_one, two_smul]
  abel

private theorem lineInv_commute_of_perp (h : UnitaryFieldData p f K) {x y : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (hy : stdHermForm h 3 y y = 1)
    (hxy : stdHermForm h 3 x y = 0) :
    (lineInv h hx).comp (lineInv h hy) = (lineInv h hy).comp (lineInv h hx) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lineInv_apply, lineInv_apply,
    lineInv_apply, lineInv_apply]
  have hyx : stdHermForm h 3 y x = 0 := by
    rw [((stdHermForm_isSymm h 3).eq x y).symm, hxy, map_zero]
  simp only [map_sub, map_add, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hxy, hyx, mul_zero, zero_mul, sub_zero, zero_sub,
    add_zero, map_zero, RingHom.id_apply, smul_smul]
  module

private theorem comp_lineInv_of_isometry (h : UnitaryFieldData p f K) {x y : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (hy : stdHermForm h 3 y y = 1)
    {φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K)}
    (hφ : ∀ u v, stdHermForm h 3 (φ u) (φ v) = stdHermForm h 3 u v)
    (hxy : φ x = y) :
    φ.comp (lineInv h hx) = (lineInv h hy).comp φ := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lineInv_apply, lineInv_apply,
    map_sub, map_smul, hxy]
  have hval : stdHermForm h 3 y (φ v) = stdHermForm h 3 x v := by
    simpa [hxy] using hφ x v
  rw [hval]

private noncomputable def suOfIsometry (h : UnitaryFieldData p f K)
    {φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K)}
    (hφ : ∀ x y, stdHermForm h 3 (φ x) (φ y) = stdHermForm h 3 x y)
    (hdet : LinearMap.det φ = 1) : unitarySU p f K 3 :=
  let u : ↥(sesqSpecialUnitaryGroup (stdHermForm h 3)) :=
    ⟨isometryUnit (stdHermForm_separatingLeft h 3) hφ,
      mem_sesqSpecialUnitaryGroup.mpr
        ⟨(isometryUnit (stdHermForm_separatingLeft h 3) hφ).2, by
          simpa [coe_isometryUnit] using hdet⟩⟩
  ⟨Matrix.GeneralLinearGroup.toLin.symm (u : LinearMap.GeneralLinearGroup K (Fin 3 → K)), by
    rw [unitarySU_eq_gramSU h 3]
    rw [← toLin_mem_sesqSpecialUnitaryGroup_iff h 1]
    rw [MulEquiv.apply_symm_apply, ← stdHermForm_eq_gramForm h 3]
    exact u.2⟩

private theorem suOfIsometry_apply (h : UnitaryFieldData p f K)
    {φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K)}
    (hφ : ∀ x y, stdHermForm h 3 (φ x) (φ y) = stdHermForm h 3 x y)
    (hdet : LinearMap.det φ = 1) (v : Fin 3 → K) :
    (suOfIsometry h hφ hdet : unitarySU p f K 3) • v = φ v := by
  rw [Subgroup.smul_def]
  change (((suOfIsometry h hφ hdet : unitarySU p f K 3) : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ v = φ v
  rw [← Matrix.mulVecLin_apply, ← Matrix.GeneralLinearGroup.coe_toLin]
  simp only [suOfIsometry, MulEquiv.apply_symm_apply, coe_isometryUnit]

private theorem exists_su_of_eq_one (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {x m : Fin 3 → K} (hx : stdHermForm h 3 x x = 1) (hm : stdHermForm h 3 m m = 1)
    (hne : Submodule.span K {x} ≠ Submodule.span K {m})
    (ht1 : h.norm (stdHermForm h 3 x m) = 1) :
    ∃ g : unitarySU p f K 3, g • m = m ∧ ∃ n : Fin 3 → K,
      stdHermForm h 3 n n = 1 ∧ g • x = n ∧
        h.norm (stdHermForm h 3 x n) ≠ 0 ∧ h.norm (stdHermForm h 3 x n) ≠ 1 := by
  classical
  haveI : CharP K p := h.charP
  let B := stdHermForm h 3
  let a := B x m
  have ht1a : h.norm a = 1 := ht1
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at ht1a
    simp [UnitaryFieldData.norm] at ht1a
  have hbar_a0 : h.bar a ≠ 0 := (map_ne_zero h.bar).mpr ha0
  have ha_bar : a * h.bar a = 1 := ht1a
  have hbar_a_mul : h.bar a * a = 1 := by rw [mul_comm, ha_bar]
  have hBxm : B x m = a := rfl
  have hBmx : B m x = h.bar a := ((stdHermForm_isSymm h 3).eq x m).symm
  let y := h.bar a • m
  have hy : B y y = 1 := by
    rw [show y = h.bar a • m from rfl]
    simp only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul,
      h.bar_bar, RingHom.id_apply]
    rw [show B m m = 1 from hm, mul_one]
    exact hbar_a_mul
  have hBxy : B x y = 1 := by
    rw [show y = h.bar a • m from rfl, map_smul, hBxm, smul_eq_mul, hbar_a_mul]
  have hByx : B y x = 1 := by
    rw [((stdHermForm_isSymm h 3).eq x y).symm, hBxy, map_one]
  let v := x - y
  have hByv : B y v = 0 := by
    rw [show v = x - y from rfl, map_sub, hByx, hy, sub_self]
  have hBvv : B v v = 0 := by
    rw [show v = x - y from rfl]
    simp only [map_sub, LinearMap.sub_apply, hBxy, hByx, hy]
    rw [show B x x = 1 from hx]
    ring
  have hv0 : v ≠ 0 := by
    intro hv
    have hxy : x = y := by
      rw [show v = x - y from rfl] at hv
      exact sub_eq_zero.mp hv
    have hspan : Submodule.span K {x} = Submodule.span K {m} := by
      rw [hxy, show y = h.bar a • m from rfl]
      exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hbar_a0) m
    exact hne hspan
  have hσ := h.isUnitaryInvolution_barEquiv
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  obtain ⟨w, hwy, hww, hvw⟩ := exists_partner_perp hσ (x := y) (a := v) hy hv0 hBvv hByv
  have hwyB : B y w = 0 := hwy
  have hwyB' : B w y = 0 := by
    rw [((stdHermForm_isSymm h 3).eq y w).symm, hwyB, map_zero]
  have hwwB : B w w = 0 := hww
  have hvwB : B v w = 1 := hvw
  have hwv : B w v = 1 := by
    rw [((stdHermForm_isSymm h 3).eq v w).symm, hvwB, map_one]
  let φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := hermTransvection B w τ
  have hφiso : ∀ u v, B (φ u) (φ v) = B u v := by
    intro u v
    exact hermTransvection_isometry (stdHermForm_isSymm h 3) hwwB (show τ + h.bar τ = 0 from hτ) u v
  have hφdet : LinearMap.det φ = 1 := det_hermTransvection B hwwB τ
  let g : unitarySU p f K 3 := suOfIsometry h hφiso hφdet
  have hgy : g • y = y := by
    rw [show g = suOfIsometry h hφiso hφdet from rfl, suOfIsometry_apply,
      show φ y = y from ?_]
    rw [show φ = hermTransvection B w τ from rfl, hermTransvection_apply, hwyB', mul_zero,
      zero_smul, add_zero]
  have hgv : g • v = v + τ • w := by
    rw [show g = suOfIsometry h hφiso hφdet from rfl, suOfIsometry_apply,
      show φ v = v + τ • w from ?_]
    rw [show φ = hermTransvection B w τ from rfl, hermTransvection_apply, hwv, mul_one]
  have hgm : g • m = m := by
    have hscaled : h.bar a • (g • m) = h.bar a • m := by
      have h1 : h.bar a • (g • m) = h.bar a • φ m := by
        rw [suOfIsometry_apply h hφiso hφdet]
      have h2 : h.bar a • φ m = φ (h.bar a • m) := (map_smul φ (h.bar a) m).symm
      have h3 : φ (h.bar a • m) = g • (h.bar a • m) :=
        (suOfIsometry_apply h hφiso hφdet _).symm
      have h4 : g • (h.bar a • m) = h.bar a • m := by
        rw [show h.bar a • m = y from rfl]
        exact hgy
      exact h1.trans (h2.trans (h3.trans h4))
    funext i
    exact mul_left_cancel₀ hbar_a0 (congrFun hscaled i)
  have hgx : g • x = x + τ • w := by
    have hxy : x = y + v := by
      rw [show v = x - y from rfl]
      abel
    rw [hxy, smul_add, hgy, hgv]
    abel
  let n := g • x
  have hnval : B x n = 1 + τ := by
    rw [show n = g • x from rfl, hgx, map_add, map_smul]
    have hxw : B x w = 1 := by
      rw [show x = y + v from by rw [show v = x - y from rfl]; abel]
      rw [map_add, LinearMap.add_apply, hwyB, hvwB, zero_add]
    rw [hx, hxw]
    simp
  have hn : B n n = 1 := by
    rw [show n = g • x from rfl,
      show g • x = φ x from suOfIsometry_apply h hφiso hφdet x]
    exact (hφiso x x).trans hx
  have hnormn : h.norm (B x n) = 1 - τ ^ 2 := by
    rw [hnval, UnitaryFieldData.norm]
    have hτ' : τ + h.bar τ = 0 := hτ
    have hbτ : h.bar τ = -τ := by linear_combination hτ'

    rw [map_add, map_one, hbτ]
    ring
  have hτsq : τ ^ 2 ≠ 1 := by
    intro hsq
    have h2 : (2 : K) ≠ 0 :=
      Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · rw [h1] at hτ
      simp only [map_one] at hτ
      have h2' : (2 : K) = 0 := by linear_combination hτ
      exact h2 h2'
    · rw [h1] at hτ
      simp only [map_neg, map_one] at hτ
      have h2' : (2 : K) = 0 := by linear_combination -hτ
      exact h2 h2'
  refine ⟨g, hgm, n, hn, rfl, ?_, ?_⟩
  · rw [hnormn]
    intro h0
    exact hτsq (sub_eq_zero.mp h0).symm
  · rw [hnormn]
    intro h1
    have h2 : τ ^ 2 = 0 := by linear_combination -h1
    exact hτ0 (sq_eq_zero_iff.mp h2)

private theorem stdHermForm_smul_smul (h : UnitaryFieldData p f K) (c d : K)
    (v w : Fin 3 → K) :
    stdHermForm h 3 (c • v) (d • w) = h.bar c * (d * stdHermForm h 3 v w) := by
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

private theorem exists_su_map_of_orthonormalBases (h : UnitaryFieldData p f K)
    {b₁ b₂ : Module.Basis (Fin 3) K (Fin 3 → K)}
    (h₁ : ⇑b₁ ∈ orthonormalFrames (stdHermForm h 3) 3)
    (h₂ : ⇑b₂ ∈ orthonormalFrames (stdHermForm h 3) 3) :
    ∃ g : unitarySU p f K 3, g • b₁ 1 = b₂ 1 ∧ g • b₁ 2 = b₂ 2 := by
  classical
  let B := stdHermForm h 3
  let φ0 : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := b₁.constr K b₂
  have hφ0 : ∀ i, φ0 (b₁ i) = b₂ i := fun i => by
    simp [φ0, Module.Basis.constr_basis]
  have hφ0iso : ∀ u v, B (φ0 u) (φ0 v) = B u v := by
    refine isometry_of_mem_orthonormalFrames b₁ h₁ ?_
    exact mem_orthonormalFrames.mpr fun i j => by
      rw [hφ0 i, hφ0 j]
      exact mem_orthonormalFrames.mp h₂ i j
  have hNdet := norm_det_of_isometry h b₁ h₁ hφ0iso
  have hdet0 : LinearMap.det φ0 ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm] at hNdet
    simp at hNdet
  have hNinv : h.norm (LinearMap.det φ0)⁻¹ = 1 := by
    rw [UnitaryFieldData.norm, map_inv₀, ← mul_inv, ← UnitaryFieldData.norm, hNdet, inv_one]
  obtain ⟨k, hkiso, hkdet, hkfix⟩ := exists_isometry_det_eq_fix h b₁ h₁ hNinv
  let φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := φ0.comp k
  have hφiso : ∀ u v, B (φ u) (φ v) = B u v := by
    intro u v
    rw [show φ = φ0.comp k from rfl, LinearMap.comp_apply, LinearMap.comp_apply,
      hφ0iso, hkiso]
  have hφdet : LinearMap.det φ = 1 := by
    rw [show φ = φ0.comp k from rfl, LinearMap.det_comp, hkdet,
      mul_inv_cancel₀ hdet0]
  let g : unitarySU p f K 3 := suOfIsometry h hφiso hφdet
  refine ⟨g, ?_, ?_⟩
  · have hk0 : k (b₁ 1) = b₁ 1 := by simpa using hkfix 0
    rw [show g = suOfIsometry h hφiso hφdet from rfl, suOfIsometry_apply,
      show φ (b₁ 1) = b₂ 1 from ?_]
    rw [show φ = φ0.comp k from rfl, LinearMap.comp_apply, hk0, hφ0]
  · have hk1 : k (b₁ 2) = b₁ 2 := by simpa using hkfix 1
    rw [show g = suOfIsometry h hφiso hφdet from rfl, suOfIsometry_apply,
      show φ (b₁ 2) = b₂ 2 from ?_]
    rw [show φ = φ0.comp k from rfl, LinearMap.comp_apply, hk1, hφ0]




private theorem exists_su_of_ne_zero_one (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {x m : Fin 3 → K} (hx : stdHermForm h 3 x x = 1) (hm : stdHermForm h 3 m m = 1)
    (ht0 : h.norm (stdHermForm h 3 x m) ≠ 0)
    (ht1 : h.norm (stdHermForm h 3 x m) ≠ 1) :
    ∃ g : unitarySU p f K 3, g • m = m ∧ ∃ n : Fin 3 → K,
      stdHermForm h 3 n n = 1 ∧ stdHermForm h 3 x n = 0 ∧ g • x = n := by
  classical
  haveI : CharP K p := h.charP
  let B := stdHermForm h 3
  let a := B x m
  let t := h.norm a
  have ht1a : t ≠ 1 := ht1
  have ht0a : t ≠ 0 := ht0
  have htfix : h.bar t = t := by
    rw [show t = h.norm a from rfl, UnitaryFieldData.norm]
    simp only [map_mul, h.bar_bar]
    exact mul_comm _ _
  have h1t : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht1a)
  have h1tfix : h.bar (1 - t) = 1 - t := by rw [map_sub, map_one, htfix]
  have hσ := h.isUnitaryInvolution_barEquiv
  obtain ⟨b, hb⟩ := hσ.exists_norm (d := 1 - t) h1tfix
  have hb' : h.bar b * b = 1 - t := hb
  have hbn : h.norm b = 1 - t := by rw [UnitaryFieldData.norm, mul_comm, hb']
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at hbn
    simp [UnitaryFieldData.norm] at hbn
    exact h1t hbn.symm
  have hbar_b0 : h.bar b ≠ 0 := (map_ne_zero h.bar).mpr hb0
  have hbinv : h.bar b⁻¹ * b⁻¹ = (1 - t)⁻¹ := by
    rw [map_inv₀, ← mul_inv, hb']
  have hBmx : B m x = h.bar a := ((stdHermForm_isSymm h 3).eq x m).symm
  have hmm : B m m = 1 := hm
  have hxx : B x x = 1 := hx
  have hxm : B x m = a := rfl
  have ht' : t = a * h.bar a := rfl
  have hBaa0 : B (m - a • x) (m - a • x) = 1 - t := by
    simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hmm, hxx, hxm, hBmx, ht']
    ring
  let e2 := b⁻¹ • (m - a • x)
  have he2 : B e2 e2 = 1 := by
    rw [show e2 = b⁻¹ • (m - a • x) from rfl, stdHermForm_smul_smul, hBaa0]
    rw [show h.bar b⁻¹ * (b⁻¹ * (1 - t)) = (h.bar b⁻¹ * b⁻¹) * (1 - t) by ring]
    rw [hbinv, inv_mul_cancel₀ h1t]
  have hxe2 : B x e2 = 0 := by
    rw [show e2 = b⁻¹ • (m - a • x) from rfl, map_smul, map_sub, map_smul,
      show B x m = a from rfl, hx]
    simp [smul_eq_mul]
  have he2x : B e2 x = 0 := by
    rw [((stdHermForm_isSymm h 3).eq x e2).symm, hxe2, map_zero]
  have hframe2 : ∀ i j, B (![x, e2] i) (![x, e2] j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxx, he2, hxe2, he2x]
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  obtain ⟨e3, he3, he3orth⟩ :=
    exists_norm_one_perp_of_lt (B := B) (σ := h.bar) (stdHermForm_isSymm h 3)
      (stdHermForm_separatingLeft h 3) hc₀ (fun d hd _ => hσ.exists_norm hd)
      (r := 2) (by rw [Module.finrank_fin_fun]; norm_num) ![x, e2] hframe2
  have he3x : B x e3 = 0 := by simpa using he3orth 0
  have he3e2 : B e2 e3 = 0 := by simpa using he3orth 1
  have he3e2' : B e3 e2 = 0 := by
    rw [((stdHermForm_isSymm h 3).eq e2 e3).symm, he3e2, map_zero]
  have he3x' : B e3 x = 0 := by
    rw [((stdHermForm_isSymm h 3).eq x e3).symm, he3x, map_zero]
  let c := h.bar a / h.bar b
  have hcnorm : h.norm c = t / (1 - t) := by
    rw [UnitaryFieldData.norm, show c = h.bar a / h.bar b from rfl, map_div₀, h.bar_bar]
    field_simp [hb0, hbar_b0, hbn, h1t]
    rw [h.bar_bar, hb']
    rw [mul_comm (h.bar a) a, ← ht']
    ring
  let e := (1 - 2 * t) / (1 - t)
  have hefix : h.bar e = e := by
    rw [show e = (1 - 2 * t) / (1 - t) from rfl, map_div₀, map_sub, map_mul, map_one,
      map_ofNat, htfix, h1tfix]
  obtain ⟨d, hd⟩ := hσ.exists_norm (d := e) hefix
  have hd' : h.bar d * d = e := hd
  have hdn : h.norm d = e := by rw [UnitaryFieldData.norm, mul_comm, hd']
  let n := c • e2 + d • e3
  have hcn : h.bar c * c = h.norm c := by rw [UnitaryFieldData.norm, mul_comm]
  have hdn' : h.bar d * d = h.norm d := by rw [UnitaryFieldData.norm, mul_comm]
  have hcc : B (c • e2) (c • e2) = h.norm c := by
    rw [stdHermForm_smul_smul, he2, mul_one, UnitaryFieldData.norm, mul_comm]
  have hdd : B (d • e3) (d • e3) = h.norm d := by
    rw [stdHermForm_smul_smul, he3, mul_one, UnitaryFieldData.norm, mul_comm]
  have hcd : B (c • e2) (d • e3) = 0 := by
    rw [stdHermForm_smul_smul, he3e2, mul_zero, mul_zero]
  have hdc : B (d • e3) (c • e2) = 0 := by
    rw [stdHermForm_smul_smul, he3e2', mul_zero, mul_zero]
  have hn : B n n = 1 := by
    rw [show n = c • e2 + d • e3 from rfl]
    simp only [map_add, LinearMap.add_apply]
    rw [hcc, hcd, hdc, hdd, hcnorm, hdn]
    rw [show e = (1 - 2 * t) / (1 - t) from rfl]
    field_simp [h1t]
    ring
  have hxn : B x n = 0 := by
    rw [show n = c • e2 + d • e3 from rfl]
    simp only [map_add, map_smul, hxe2, he3x, mul_zero, add_zero]
    simp
  have hbe2 : b • e2 = m - a • x := by
    rw [show e2 = b⁻¹ • (m - a • x) from rfl, smul_smul, mul_inv_cancel₀ hb0, one_smul]
  have hmx : m = a • x + b • e2 := by rw [hbe2]; abel
  have he2n : B e2 n = c := by
    rw [show n = c • e2 + d • e3 from rfl]
    simp only [map_add, map_smul, he2, he3e2, smul_eq_mul, mul_one, mul_zero, add_zero]
  have hmn : B m n = h.bar a := by
    rw [hmx]
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hxn, he2n, mul_zero, zero_add]
    rw [show c = h.bar a / h.bar b from rfl]
    field_simp [hbar_b0]
  have hnm : B n m = a := by
    rw [((stdHermForm_isSymm h 3).eq m n).symm, hmn, h.bar_bar]
  have hBaa1 : B (m - a • n) (m - a • n) = 1 - t := by
    simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hmm, hn, hmn, hnm, ht']
    ring
  let w := b⁻¹ • (m - a • n)
  have hwn : B n w = 0 := by
    rw [show w = b⁻¹ • (m - a • n) from rfl, map_smul, map_sub, map_smul, hnm, hn]
    simp [smul_eq_mul]
  have hw : B w w = 1 := by
    rw [show w = b⁻¹ • (m - a • n) from rfl, stdHermForm_smul_smul, hBaa1]
    rw [show h.bar b⁻¹ * (b⁻¹ * (1 - t)) = (h.bar b⁻¹ * b⁻¹) * (1 - t) by ring]
    rw [hbinv, inv_mul_cancel₀ h1t]
  have hwn' : B w n = 0 := by
    rw [((stdHermForm_isSymm h 3).eq n w).symm, hwn, map_zero]
  have hframe_nw : ∀ i j, B (![n, w] i) (![n, w] j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hn, hw, hwn, hwn']
  obtain ⟨z, hz, hzorth⟩ :=
    exists_norm_one_perp_of_lt (B := B) (σ := h.bar) (stdHermForm_isSymm h 3)
      (stdHermForm_separatingLeft h 3) hc₀ (fun d hd _ => hσ.exists_norm hd)
      (r := 2) (by rw [Module.finrank_fin_fun]; norm_num) ![n, w] hframe_nw
  have hzn : B n z = 0 := by simpa using hzorth 0
  have hzw : B w z = 0 := by simpa using hzorth 1
  have hframe1 : ∀ i j, B (![e3, x, e2] i) (![e3, x, e2] j) =
      if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hxx, he2, he3, he3x, he3x', he3e2, he3e2', he2x, hxe2]
  have hzn' : B z n = 0 := by
    rw [((stdHermForm_isSymm h 3).eq n z).symm, hzn, map_zero]
  have hzw' : B z w = 0 := by
    rw [((stdHermForm_isSymm h 3).eq w z).symm, hzw, map_zero]
  have hframe2' : ∀ i j, B (![z, n, w] i) (![z, n, w] j) =
      if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hz, hn, hw, hzn, hzw, hzn', hzw', hwn, hwn']
  have hr3 : 3 = Module.finrank K (Fin 3 → K) := by rw [Module.finrank_fin_fun]
  let b₁ : Module.Basis (Fin 3) K (Fin 3 → K) := frameBasis hframe1 hr3
  let b₂ : Module.Basis (Fin 3) K (Fin 3 → K) := frameBasis hframe2' hr3
  have hb₁ : ⇑b₁ ∈ orthonormalFrames B 3 := by
    rw [coe_frameBasis hframe1 hr3]
    exact hframe1
  have hb₂ : ⇑b₂ ∈ orthonormalFrames B 3 := by
    rw [coe_frameBasis hframe2' hr3]
    exact hframe2'
  have hb₁1 : b₁ 1 = x := by
    rw [coe_frameBasis hframe1 hr3]
    simp
  have hb₁2 : b₁ 2 = e2 := by
    rw [coe_frameBasis hframe1 hr3]
    simp
  have hb₂1 : b₂ 1 = n := by
    rw [coe_frameBasis hframe2' hr3]
    simp
  have hb₂2 : b₂ 2 = w := by
    rw [coe_frameBasis hframe2' hr3]
    simp
  obtain ⟨g, hg1, hg2⟩ := exists_su_map_of_orthonormalBases h hb₁ hb₂
  have hgx : g • x = n := by
    rw [← hb₁1, ← hb₂1]
    exact hg1
  have hge2 : g • e2 = w := by
    rw [← hb₁2, ← hb₂2]
    exact hg2
  have hgsmul (c : K) (v : Fin 3 → K) : g • (c • v) = c • (g • v) := by
    have h1 : g • (c • v) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • v) := by
      rw [Subgroup.smul_def]
      rfl
    have h2 : g • v = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
      rw [Subgroup.smul_def]
      rfl
    rw [h1, h2, Matrix.mulVec_smul]
  have hgm : g • m = m := by
    rw [hmx, smul_add, hgsmul, hgsmul, hgx, hge2]
    rw [show w = b⁻¹ • (m - a • n) from rfl, smul_smul, mul_inv_cancel₀ hb0, one_smul]
    rw [hmx]
    abel
  exact ⟨g, hgm, n, hn, hxn, hgx⟩


private theorem unitaryInvT_apply_lineInv (h : UnitaryFieldData p f K) (v : Fin 3 → K) :
    (((unitaryInvT h : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      lineInv h (stdUnit_norm h) v := by
  rw [coe_unitaryInvT]
  rw [lineInv_apply]
  funext i
  fin_cases i <;>
    simp [negNegOneDiag, stdHermForm_single, stdUnit, Pi.single_apply,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.diagonal] <;> ring

private theorem centralizer_unitaryInvT_ne_top (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    Subgroup.centralizer ({unitaryInvT h} : Set (unitarySU p f K 3)) ≠ ⊤ := by
  classical
  have h2 : (2 : K) ≠ 0 := by
    haveI : CharP K p := h.charP
    exact Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  let e0 : Fin 3 → K := Pi.single 0 1
  let e1 : Fin 3 → K := Pi.single 1 1
  let e2 : Fin 3 → K := Pi.single 2 1
  let B := stdHermForm h 3
  have hx2 : B e2 e2 = 1 := by
    rw [show e2 = Pi.single 2 1 from rfl, stdHermForm_single]
    exact Pi.single_eq_same 2 1
  have hstd : ∀ i j, B (![e0, e1, e2] i) (![e0, e1, e2] j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B, e0, e1, e2, stdHermForm_single, Pi.single_eq_same]
  have himg : ∀ i j, B (![e2, -e1, e0] i) (![e2, -e1, e0] j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B, e0, e1, e2, stdHermForm_single, Pi.single_eq_same]
  have hr3 : 3 = Module.finrank K (Fin 3 → K) := by rw [Module.finrank_fin_fun]
  let b₁ : Module.Basis (Fin 3) K (Fin 3 → K) := frameBasis hstd hr3
  let b₂ : Module.Basis (Fin 3) K (Fin 3 → K) := frameBasis himg hr3
  have hb₁ : ⇑b₁ ∈ orthonormalFrames B 3 := by
    rw [coe_frameBasis hstd hr3]
    exact hstd
  have hb₂ : ⇑b₂ ∈ orthonormalFrames B 3 := by
    rw [coe_frameBasis himg hr3]
    exact himg
  have hb₁2 : b₁ 2 = e2 := by
    rw [coe_frameBasis hstd hr3]
    simp [e2, Pi.single_eq_same]
  have hb₂2 : b₂ 2 = e0 := by
    rw [coe_frameBasis himg hr3]
    simp [e0, Pi.single_eq_same]
  obtain ⟨g, -, hg2⟩ := exists_su_map_of_orthonormalBases h hb₁ hb₂
  have hgx : g • e2 = e0 := by
    rw [← hb₁2, ← hb₂2]
    exact hg2
  have hTx : unitaryInvT h • e2 = e2 := by
    have := unitaryInvT_apply_lineInv h e2
    rw [show unitaryInvT h • e2 =
      (((unitaryInvT h : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ e2 from by
      rw [Subgroup.smul_def]; rfl, this]
    rw [show e2 = stdUnit (K := K) from rfl]
    rw [lineInv_self h (stdUnit_norm h)]
  have hTe0 : unitaryInvT h • e0 = -e0 := by
    have := unitaryInvT_apply_lineInv h e0
    rw [show unitaryInvT h • e0 =
      (((unitaryInvT h : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ e0 from by
      rw [Subgroup.smul_def]; rfl, this]
    rw [lineInv_apply]
    have hBe0 : B (stdUnit (K := K)) e0 = 0 := by
      rw [show stdUnit (K := K) = Pi.single 2 1 from rfl,
        show e0 = Pi.single 0 1 from rfl]
      rw [stdHermForm_single]
      simp
    rw [hBe0, mul_zero, zero_smul]
    simp
  intro htop
  have hgC : g ∈ Subgroup.centralizer ({unitaryInvT h} : Set (unitarySU p f K 3)) := by
    rw [htop]
    exact Subgroup.mem_top g
  have hcomm : g * unitaryInvT h = unitaryInvT h * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hgC
  have h1 : g • (unitaryInvT h • e2) = unitaryInvT h • (g • e2) := by
    rw [← mul_smul, ← mul_smul, hcomm]
  rw [hTx, hgx, hTe0] at h1
  have hcoord := congrFun h1 0
  simp [e0, Pi.single_apply] at hcoord
  have hcoord' : (2 : K) = 0 := by linear_combination hcoord
  exact h2 hcoord'


private theorem centralizer_statedProj_eq_map (h : UnitaryFieldData p f K)
    {T : unitarySU p f K 3} (hT2 : T * T = 1) :
    (Subgroup.centralizer ({T} : Set (unitarySU p f K 3))).map
        (CFSG.RankThree.CentralCover.statedProjMk (unitarySU p f K 3)) =
      Subgroup.centralizer ({CFSG.RankThree.CentralCover.statedProjMk (unitarySU p f K 3) T} : Set (StatedProj (unitarySU p f K 3))) := by
  classical
  let S := unitarySU p f K 3
  let ρ : S →* StatedProj S := CFSG.RankThree.CentralCover.statedProjMk S
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x * T = T * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hx'])
  · intro hy
    obtain ⟨x, rfl⟩ := CFSG.RankThree.CentralCover.statedProjMk_surjective S y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨x, ?_, rfl⟩
    have hxT : x * T = T * x :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.commute_of_map_commute ρ
        (CFSG.RankThree.CentralCover.ker_statedProjMk_le_center S)
        (fun z hz => CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three h z hz)
        hT2 hy
    exact (Subgroup.mem_centralizer_singleton_iff).mpr (by simpa using hxT)

private theorem conj_lineInv_apply (h : UnitaryFieldData p f K) {x n : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (hn : stdHermForm h 3 n n = 1)
    {T : unitarySU p f K 3}
    (hT : ∀ v : Fin 3 → K, (((T : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hx v)
    (g : unitarySU p f K 3) (hgx : g • x = n) (v : Fin 3 → K) :
    (((g * T * g⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hn v := by
  let B := stdHermForm h 3
  let Mg : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let MgInv : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let MT : Matrix (Fin 3) (Fin 3) K := ((T : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  let φ : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    Matrix.mulVecLin (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
  have hφiso : ∀ a b, B (φ a) (φ b) = B a b := by
    intro a b
    have hg := (mem_unitarySU_iff_isometry h).mp g.2
    dsimp [φ, B]
    exact hg.2 a b
  have hφx : φ x = n := by
    change ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = n
    have h1 : g • x = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
      rw [Subgroup.smul_def]
      rfl
    rw [← h1, hgx]
  have hcomp := comp_lineInv_of_isometry h hx hn hφiso hφx
  have hMgInv : Mg * MgInv = 1 := by
    dsimp [Mg, MgInv]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMT : ∀ w, MT *ᵥ w = lineInv h hx w := by
    intro w
    exact hT w
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  change (Mg * MT * MgInv) *ᵥ v = lineInv h hn v
  have hfinal : Mg *ᵥ (MgInv *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hMgInv, Matrix.one_mulVec]
  calc (Mg * MT * MgInv) *ᵥ v
      = Mg *ᵥ (MT *ᵥ (MgInv *ᵥ v)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    _ = Mg *ᵥ (lineInv h hx (MgInv *ᵥ v)) := by rw [hMT]
    _ = φ (lineInv h hx (MgInv *ᵥ v)) := by rfl
    _ = lineInv h hn (φ (MgInv *ᵥ v)) := by
          rw [← LinearMap.comp_apply, hcomp, LinearMap.comp_apply]
    _ = lineInv h hn v := by
          rw [show φ (MgInv *ᵥ v) = v by
            dsimp [φ]
            exact hfinal]

private theorem commute_conj_lineInv (h : UnitaryFieldData p f K)
    {x n : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (hn : stdHermForm h 3 n n = 1)
    (hnx : stdHermForm h 3 n x = 0)
    {T : unitarySU p f K 3}
    (hT0 : ∀ v : Fin 3 → K, (((T : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hx v)
    (g : unitarySU p f K 3) (hgx : g • x = n) :
    (g * T * g⁻¹) * T = T * (g * T * g⁻¹) := by
  let S : unitarySU p f K 3 := g * T * g⁻¹
  change S * T = T * S
  have hlin := lineInv_commute_of_perp h hn hx hnx
  have hS : ∀ v, (((S : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hn v :=
    fun v => conj_lineInv_apply h hx hn hT0 g hgx v
  have hT : ∀ v, (((T : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      lineInv h hx v :=
    fun v => hT0 v
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hST : ∀ v, (((S * T : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      lineInv h hn (lineInv h hx v) := by
    intro v
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hS, hT]
  have hTS : ∀ v, (((T * S : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      lineInv h hx (lineInv h hn v) := by
    intro v
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hT, hS]
  have hSTi : ((S * T : unitarySU p f K 3) : GL (Fin 3) K) i j =
      lineInv h hn (lineInv h hx (Pi.single j 1)) i := by
    have := congrFun (hST (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  have hTSi : ((T * S : unitarySU p f K 3) : GL (Fin 3) K) i j =
      lineInv h hx (lineInv h hn (Pi.single j 1)) i := by
    have := congrFun (hTS (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
  have hcomp_apply := congrFun (congrArg (fun L : (Fin 3 → K) →ₗ[K] (Fin 3 → K) =>
    L (Pi.single j 1)) hlin) i
  have h' : (lineInv h hn) ((lineInv h hx) (Pi.single j 1)) i =
      (lineInv h hx) ((lineInv h hn) (Pi.single j 1)) i := by
    simpa using hcomp_apply
  exact hSTi.trans (h'.trans hTSi.symm)


private theorem conj_centralizer_le (h : UnitaryFieldData p f K)
    {T : unitarySU p f K 3} {Ksub : Subgroup (unitarySU p f K 3)}
    (hK : Subgroup.centralizer ({T} : Set (unitarySU p f K 3)) ≤ Ksub)
    {g : unitarySU p f K 3} (hg : g ∈ Ksub) :
    Subgroup.centralizer ({g * T * g⁻¹} : Set (unitarySU p f K 3)) ≤ Ksub := by
  intro x hx
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({T} : Set (unitarySU p f K 3)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc (g⁻¹ * x * g) * T = g⁻¹ * (x * (g * T * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * T * g⁻¹) * x) * g := by rw [hx]
      _ = T * (g⁻¹ * x * g) := by group
  have hxK := hK hx'
  have hxK' : g * (g⁻¹ * x * g) * g⁻¹ ∈ Ksub :=
    Ksub.mul_mem (Ksub.mul_mem hg hxK) (Ksub.inv_mem hg)
  rwa [show x = g * (g⁻¹ * x * g) * g⁻¹ by group]

private theorem commute_of_fixes_line (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) {T : unitarySU p f K 3}
    (hT0 : ∀ v : Fin 3 → K, (((T : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hx v)
    (g : unitarySU p f K 3) (hgx : g • x = x) : g * T = T * g := by
  have hconj : ∀ v : Fin 3 → K,
      (((g * T * g⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (((T : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v := by
    intro v
    rw [conj_lineInv_apply h hx hx hT0 g hgx v, hT0 v]
  have hEq : g * T * g⁻¹ = T := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    have h1 := congrFun (hconj (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h1
  calc g * T = (g * T * g⁻¹) * g := by group
    _ = T * g := by rw [hEq]

private theorem eq_top_of_two_centralizers (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {T U : unitarySU p f K 3}
    (hT2 : T * T = 1) (hU2 : U * U = 1) (hT1 : T ≠ 1) (hU1 : U ≠ 1)
    (hcomm : U * T = T * U) (hne : U ≠ T)
    {H : Subgroup (unitarySU p f K 3)}
    (hTH : Subgroup.centralizer ({T} : Set (unitarySU p f K 3)) ≤ H)
    (hUH : Subgroup.centralizer ({U} : Set (unitarySU p f K 3)) ≤ H) :
    H = ⊤ := by
  classical
  let S := unitarySU p f K 3
  let ρ : S →* StatedProj S := CFSG.RankThree.CentralCover.statedProjMk S
  have hTord : orderOf T = 2 := orderOf_eq_prime (by rw [sq]; exact hT2) hT1
  have hUord : orderOf U = 2 := orderOf_eq_prime (by rw [sq]; exact hU2) hU1
  have htP : orderOf (ρ T) = 2 := by
    have hsq : ρ T * ρ T = 1 := by rw [← map_mul, hT2, map_one]
    have hne1 : ρ T ≠ 1 := by
      intro h1
      have hker : T ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
      have hT3 := CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three h T hker
      have hT31 : T = T ^ 3 := by rw [pow_succ, sq, hT2, one_mul]
      exact hT1 (hT31.trans hT3)
    exact orderOf_eq_prime (by rw [sq]; exact hsq) hne1
  have huP : orderOf (ρ U) = 2 := by
    have hsq : ρ U * ρ U = 1 := by rw [← map_mul, hU2, map_one]
    have hne1 : ρ U ≠ 1 := by
      intro h1
      have hker : U ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
      have hU3 := CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three h U hker
      have hU31 : U = U ^ 3 := by rw [pow_succ, sq, hU2, one_mul]
      exact hU1 (hU31.trans hU3)
    exact orderOf_eq_prime (by rw [sq]; exact hsq) hne1
  have htsP : ρ T * ρ U = ρ U * ρ T := by rw [← map_mul, ← map_mul, hcomm]
  have hneP : ρ T ≠ ρ U := by
    intro hρ
    have hker : U * T ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, hρ]
      have : ρ U * ρ U = 1 := by rw [← hρ, ← map_mul, hT2, map_one]
      exact this
    have hc3 : (U * T) ^ 3 = 1 :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three h (U * T) hker
    have hc2 : (U * T) * (U * T) = 1 := by
      calc (U * T) * (U * T) = U * (T * U) * T := by group
        _ = U * (U * T) * T := by rw [hcomm]
        _ = (U * U) * (T * T) := by group
        _ = 1 := by rw [hU2, hT2, mul_one]
    have hc1 : U * T = 1 := by
      have hc31 : U * T = (U * T) ^ 3 := by rw [pow_succ, sq, hc2, one_mul]
      rw [hc31, hc3]
    have hUT : U = T := by
      calc U = U * (T * T) := by rw [hT2, mul_one]
        _ = (U * T) * T := by group
        _ = 1 * T := by rw [hc1]
        _ = T := one_mul T
    exact hne hUT
  have hgen := CFSG.ClassicalInvolution.Q3.TL4.E3C269G.sup_centralizer_eq_top_psu3
    h hp2 htP huP htsP hneP
  have hCmapT := centralizer_statedProj_eq_map h hT2
  have hCmapU := centralizer_statedProj_eq_map h hU2
  have hsup : Subgroup.map ρ (Subgroup.centralizer ({T} : Set S)) ⊔
      Subgroup.map ρ (Subgroup.centralizer ({U} : Set S)) = ⊤ := by
    rw [hCmapT, hCmapU, hgen]
  have htopP : H.map ρ = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hsup]
    exact sup_le (Subgroup.map_mono hTH) (Subgroup.map_mono hUH)
  have hkerC : ρ.ker ≤ Subgroup.centralizer ({T} : Set S) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp
      (CFSG.RankThree.CentralCover.ker_statedProjMk_le_center S hz) T).symm
  have hkerH : ρ.ker ≤ H := hkerC.trans hTH
  rw [eq_top_iff]
  intro y _
  have hy : ρ y ∈ H.map ρ := by rw [htopP]; exact Subgroup.mem_top _
  obtain ⟨x, hxH, hxy⟩ := Subgroup.mem_map.mp hy
  have hker : y * x⁻¹ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    group
  have hmem : y * x⁻¹ ∈ H := hkerH hker
  rw [show y = (y * x⁻¹) * x by group]
  exact H.mul_mem hmem hxH


private theorem lineInv_smul_eq (h : UnitaryFieldData p f K) {x : Fin 3 → K}
    (hx : stdHermForm h 3 x x = 1) (c : K) (hc : h.norm c = 1)
    (hxc : stdHermForm h 3 (c • x) (c • x) = 1) :
    lineInv h hxc = lineInv h hx := by
  apply LinearMap.ext
  intro v
  rw [lineInv_apply, lineInv_apply]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_smul, RingHom.id_apply]
  have hbar : h.bar c * c = 1 := by
    rw [mul_comm (h.bar c) c, ← UnitaryFieldData.norm, hc]
  have hcoef : (2 : K) * (h.bar c * stdHermForm h 3 x v) * c =
      (2 : K) * stdHermForm h 3 x v := by
    calc (2 : K) * (h.bar c * stdHermForm h 3 x v) * c =
        (h.bar c * c) * ((2 : K) * stdHermForm h 3 x v) := by ring
      _ = 1 * ((2 : K) * stdHermForm h 3 x v) := by rw [hbar]
      _ = (2 : K) * stdHermForm h 3 x v := one_mul _
  rw [hcoef]

private theorem conj_unitaryInvT_ne_of_perp (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {n : Fin 3 → K} (hn : stdHermForm h 3 n n = 1)
    (hxn : stdHermForm h 3 (stdUnit (K := K)) n = 0)
    (g : unitarySU p f K 3) (hgx : g • stdUnit (K := K) = n) :
    (g * unitaryInvT h * g⁻¹) ≠ unitaryInvT h := by
  classical
  haveI : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hTlin : ∀ v : Fin 3 → K,
      (((unitaryInvT h : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h (stdUnit_norm h) v :=
    fun v => unitaryInvT_apply_lineInv h v
  have hUact := conj_lineInv_apply h (stdUnit_norm h) hn hTlin g hgx
  have hnx : stdHermForm h 3 n (stdUnit (K := K)) = 0 := by
    rw [((stdHermForm_isSymm h 3).eq (stdUnit (K := K)) n).symm, hxn, map_zero]
  have hUx : (g * unitaryInvT h * g⁻¹) • stdUnit (K := K) = -stdUnit (K := K) := by
    rw [show (g * unitaryInvT h * g⁻¹) • stdUnit (K := K) =
      (((g * unitaryInvT h * g⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ stdUnit (K := K) from by
      rw [Subgroup.smul_def]; rfl, hUact, lineInv_apply, hnx]
    simp
  have hTx : unitaryInvT h • stdUnit (K := K) = stdUnit (K := K) := by
    rw [show unitaryInvT h • stdUnit (K := K) =
      (((unitaryInvT h : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ stdUnit (K := K) from by
      rw [Subgroup.smul_def]; rfl, hTlin, lineInv_self]
  intro hEq
  have h1 := congrArg (fun A : unitarySU p f K 3 => A • stdUnit (K := K)) hEq
  rw [hUx, hTx] at h1
  have hcontra : (-1 : K) = 1 := by
    have hb := congrArg (fun v : Fin 3 → K => stdHermForm h 3 (stdUnit (K := K)) v) h1
    rw [map_neg, show stdHermForm h 3 (stdUnit (K := K)) (stdUnit (K := K)) = 1
      from stdUnit_norm h] at hb
    simpa using hb
  have h2' : (2 : K) = 0 := by
    have h1 : (0 : K) = 2 := by
      calc (0 : K) = -1 + 1 := by ring
        _ = 1 + 1 := by rw [hcontra]
        _ = 2 := by norm_num
    exact h1.symm
  exact h2 h2'

private theorem eq_of_mulVecLin_eq {A B : unitarySU p f K 3}
    (h : ∀ v : Fin 3 → K, (((A : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (((B : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) : A = B := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using h1


private theorem unitaryInvT_ne_one (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    unitaryInvT h ≠ 1 := by
  classical
  haveI : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  intro h1
  have := congrArg (fun t : unitarySU p f K 3 =>
    (((t : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp only [coe_unitaryInvT] at this
  rw [show negNegOneDiag K 0 0 = -1 by simp [negNegOneDiag]] at this
  have hneg : (-1 : K) = 1 := by simpa using this
  have hzero : (2 : K) = 0 := by
    have h0 : (0 : K) = 2 := by
      calc (0 : K) = -1 + 1 := by ring
        _ = 1 + 1 := by rw [hneg]
        _ = 2 := by norm_num
    exact h0.symm
  exact h2 hzero


theorem isCoatom_centralizer_unitaryInvT_SU (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    IsCoatom (Subgroup.centralizer ({unitaryInvT h} : Set (unitarySU p f K 3))) := by
  classical
  haveI : CharP K p := h.charP
  let S := unitarySU p f K 3
  let T : S := unitaryInvT h
  let x : Fin 3 → K := stdUnit
  have hx : stdHermForm h 3 x x = 1 := stdUnit_norm h
  have hT2 : T * T = 1 := by
    rw [show T = unitaryInvT h from rfl, ← sq, unitaryInvT_sq]
  have hT1 : T ≠ 1 := by
    rw [show T = unitaryInvT h from rfl]
    exact unitaryInvT_ne_one h hp2
  have hTlin : ∀ v : Fin 3 → K, (((T : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hx v :=
    fun v => unitaryInvT_apply_lineInv h v
  refine ⟨centralizer_unitaryInvT_ne_top h hp2, ?_⟩
  intro H hH
  obtain ⟨u, huH, huC⟩ := SetLike.exists_of_lt hH
  let m : Fin 3 → K := u • x
  have huIso : ∀ a b, stdHermForm h 3 (u • a) (u • b) = stdHermForm h 3 a b := by
    intro a b
    have hu := (mem_unitarySU_iff_isometry h).mp u.2
    rw [show u • a = ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ a from by
      rw [Subgroup.smul_def]; rfl,
      show u • b = ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ b from by
      rw [Subgroup.smul_def]; rfl]
    exact hu.2 a b
  have hm : stdHermForm h 3 m m = 1 := by
    rw [show m = u • x from rfl, huIso x x, hx]
  let U : S := u * T * u⁻¹
  have hUact : ∀ v : Fin 3 → K, (((U : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hm v :=
    fun v => conj_lineInv_apply h hx hm hTlin u rfl v
  have hUC : Subgroup.centralizer ({U} : Set S) ≤ H :=
    conj_centralizer_le h hH.le huH
  by_cases ht0 : h.norm (stdHermForm h 3 x m) = 0
  · have hxm : stdHermForm h 3 x m = 0 := by
      rw [UnitaryFieldData.norm] at ht0
      rcases mul_eq_zero.mp ht0 with h0 | h0
      · exact h0
      · exact h.bar_eq_zero_iff.mp h0
    have hU2 : U * U = 1 := by
      dsimp [U]
      calc (u * T * u⁻¹) * (u * T * u⁻¹) = u * (T * T) * u⁻¹ := by group
        _ = 1 := by rw [hT2]; group
    have hU1 : U ≠ 1 := by
      intro h1
      dsimp [U] at h1
      exact hT1 (conj_eq_one_iff.mp h1)
    have hmx : stdHermForm h 3 m x = 0 := by
      rw [((stdHermForm_isSymm h 3).eq x m).symm, hxm, map_zero]
    have hcomm : U * T = T * U :=
      commute_conj_lineInv h hx hm hmx hTlin u rfl
    have hne : U ≠ T := conj_unitaryInvT_ne_of_perp h hp2 hm hxm u rfl
    exact eq_top_of_two_centralizers h hp2 hT2 hU2 hT1 hU1 hcomm hne hH.le hUC
  · by_cases ht1 : h.norm (stdHermForm h 3 x m) = 1
    · have hspan_ne : Submodule.span K {m} ≠ Submodule.span K {x} := by
        intro hspan
        have hmem : m ∈ Submodule.span K {x} := by
          rw [← hspan]
          exact Submodule.mem_span_singleton_self m
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
        have hcm : m = c • x := hc.symm
        have hxc : stdHermForm h 3 (c • x) (c • x) = 1 := by
          rw [← hcm]
          exact hm
        have hcnorm : h.norm c = 1 := by
          rw [show stdHermForm h 3 (c • x) (c • x) = h.norm c from by
            rw [stdHermForm_smul_smul, hx, mul_one, UnitaryFieldData.norm, mul_comm]]
            at hxc
          exact hxc
        have hline : lineInv h hxc = lineInv h hx :=
          lineInv_smul_eq h hx c hcnorm hxc
        have hline' : lineInv h hm = lineInv h hx := by
          simpa [hcm] using hline
        have hEq : U = T := by
          apply eq_of_mulVecLin_eq
          intro v
          rw [hUact, hTlin, hline']
        have huT : u * T = T * u := by
          calc u * T = U * u := by dsimp [U]; group
            _ = T * u := by rw [hEq]
        exact huC (Subgroup.mem_centralizer_singleton_iff.mpr huT)
      obtain ⟨g0, hg0m, n0, hn0, hg0x, ht0', ht1'⟩ :=
        exists_su_of_eq_one h hp2 hx hm (Ne.symm hspan_ne) ht1
      have hUm_act : ∀ v : Fin 3 → K, (((U : GL (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hm v := hUact
      have hg0U : g0 * U = U * g0 :=
        commute_of_fixes_line h hm hUm_act g0 hg0m
      have hg0H : g0 ∈ H := hUC (Subgroup.mem_centralizer_singleton_iff.mpr hg0U)
      let T0 : S := g0 * T * g0⁻¹
      have hT0act : ∀ v : Fin 3 → K, (((T0 : GL (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hn0 v := by
        intro v
        exact conj_lineInv_apply h hx hn0 hTlin g0 hg0x v
      have hT0C : Subgroup.centralizer ({T0} : Set S) ≤ H :=
        conj_centralizer_le h hH.le hg0H
      obtain ⟨g1, hg1n0, n, hn, hxn, hg1x⟩ :=
        exists_su_of_ne_zero_one h hp2 hx hn0 ht0' ht1'
      have hg1T0 : g1 * T0 = T0 * g1 :=
        commute_of_fixes_line h hn0 hT0act g1 hg1n0
      have hg1H : g1 ∈ H := hT0C (Subgroup.mem_centralizer_singleton_iff.mpr hg1T0)
      let U1 : S := g1 * T * g1⁻¹
      have hU1act : ∀ v : Fin 3 → K, (((U1 : GL (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hn v :=
        fun v => conj_lineInv_apply h hx hn hTlin g1 hg1x v
      have hU1C : Subgroup.centralizer ({U1} : Set S) ≤ H :=
        conj_centralizer_le h hH.le hg1H
      have hU1_2 : U1 * U1 = 1 := by
        dsimp [U1]
        calc (g1 * T * g1⁻¹) * (g1 * T * g1⁻¹) = g1 * (T * T) * g1⁻¹ := by group
          _ = 1 := by rw [hT2]; group

      have hU1_1 : U1 ≠ 1 := by
        intro h1
        dsimp [U1] at h1
        exact hT1 (conj_eq_one_iff.mp h1)
      have hnx : stdHermForm h 3 n x = 0 := by
        rw [((stdHermForm_isSymm h 3).eq x n).symm, hxn, map_zero]
      have hcomm1 : U1 * T = T * U1 :=
        commute_conj_lineInv h hx hn hnx hTlin g1 hg1x
      have hne1 : U1 ≠ T := conj_unitaryInvT_ne_of_perp h hp2 hn hxn g1 hg1x
      exact eq_top_of_two_centralizers h hp2 hT2 hU1_2 hT1 hU1_1 hcomm1 hne1 hH.le hU1C
    · obtain ⟨g, hgm, n, hn, hxn, hgx⟩ :=
        exists_su_of_ne_zero_one h hp2 hx hm ht0 ht1
      have hgU : g * U = U * g :=
        commute_of_fixes_line h hm hUact g hgm
      have hgH : g ∈ H := hUC (Subgroup.mem_centralizer_singleton_iff.mpr hgU)
      let U1 : S := g * T * g⁻¹
      have hU1act : ∀ v : Fin 3 → K, (((U1 : GL (Fin 3) K)) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ v = lineInv h hn v :=
        fun v => conj_lineInv_apply h hx hn hTlin g hgx v
      have hU1C : Subgroup.centralizer ({U1} : Set S) ≤ H :=
        conj_centralizer_le h hH.le hgH
      have hU1_2 : U1 * U1 = 1 := by
        dsimp [U1]
        calc (g * T * g⁻¹) * (g * T * g⁻¹) = g * (T * T) * g⁻¹ := by group
          _ = 1 := by rw [hT2]; group
      have hU1_1 : U1 ≠ 1 := by
        intro h1
        dsimp [U1] at h1
        exact hT1 (conj_eq_one_iff.mp h1)
      have hnx : stdHermForm h 3 n x = 0 := by
        rw [((stdHermForm_isSymm h 3).eq x n).symm, hxn, map_zero]
      have hcomm1 : U1 * T = T * U1 :=
        commute_conj_lineInv h hx hn hnx hTlin g hgx
      have hne1 : U1 ≠ T := conj_unitaryInvT_ne_of_perp h hp2 hn hxn g hgx
      exact eq_top_of_two_centralizers h hp2 hT2 hU1_2 hT1 hU1_1 hcomm1 hne1 hH.le hU1C


theorem isCoatom_centralizer_statedProj_unitaryInvT (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) :
    IsCoatom (Subgroup.centralizer ({CFSG.RankThree.CentralCover.statedProjMk (unitarySU p f K 3) (unitaryInvT h)} : Set (StatedProj (unitarySU p f K 3)))) := by
  classical
  let S := unitarySU p f K 3
  let T : S := unitaryInvT h
  let ρ : S →* StatedProj S := CFSG.RankThree.CentralCover.statedProjMk S
  have hT2 : T * T = 1 := by
    rw [show T = unitaryInvT h from rfl, ← sq, unitaryInvT_sq]
  have hSU := isCoatom_centralizer_unitaryInvT_SU h hp2
  have hmap : (Subgroup.centralizer ({T} : Set S)).map ρ =
      Subgroup.centralizer ({ρ T} : Set (StatedProj S)) :=
    centralizer_statedProj_eq_map h hT2
  have hkerC : ρ.ker ≤ Subgroup.centralizer ({T} : Set S) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp
      (CFSG.RankThree.CentralCover.ker_statedProjMk_le_center S hz) T).symm
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    intro htop
    apply hSU.1
    rw [eq_top_iff]
    intro x _
    have hx : ρ x ∈ (Subgroup.centralizer ({T} : Set S)).map ρ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hker : x * y⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx]
      group
    have hmem := hkerC hker
    rw [show x = (x * y⁻¹) * y by group]
    exact Subgroup.mul_mem _ hmem hy
  · intro L hL
    let L' : Subgroup S := L.comap ρ
    have hCL : Subgroup.centralizer ({T} : Set S) ≤ L' := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hxmap : ρ x ∈ (Subgroup.centralizer ({T} : Set S)).map ρ :=
        Subgroup.mem_map_of_mem ρ hx
      rw [hmap] at hxmap
      exact hL.le hxmap
    have hlt : Subgroup.centralizer ({T} : Set S) < L' := by
      refine lt_of_le_of_ne hCL ?_
      intro heq
      have hEqL : L = Subgroup.centralizer ({ρ T} : Set (StatedProj S)) := by
        calc L = L'.map ρ :=
              (Subgroup.map_comap_eq_self_of_surjective
                (CFSG.RankThree.CentralCover.statedProjMk_surjective S) L).symm
          _ = (Subgroup.centralizer ({T} : Set S)).map ρ := by rw [heq]
          _ = Subgroup.centralizer ({ρ T} : Set (StatedProj S)) := hmap
      exact hL.ne hEqL.symm
    have htop := hSU.2 L' hlt
    calc L = L'.map ρ :=
          (Subgroup.map_comap_eq_self_of_surjective
            (CFSG.RankThree.CentralCover.statedProjMk_surjective S) L).symm
      _ = ⊤ := by
        rw [htop, Subgroup.map_top_of_surjective ρ
          (CFSG.RankThree.CentralCover.statedProjMk_surjective S)]


private theorem orderOf_statedProj_unitaryInvT (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) :
    orderOf (CFSG.RankThree.CentralCover.statedProjMk (unitarySU p f K 3)
      (unitaryInvT h)) = 2 := by
  classical
  let S := unitarySU p f K 3
  let T : S := unitaryInvT h
  let ρ : S →* StatedProj S := CFSG.RankThree.CentralCover.statedProjMk S
  have hT2 : T * T = 1 := by
    rw [show T = unitaryInvT h from rfl, ← sq, unitaryInvT_sq]
  have hT1 : T ≠ 1 := by
    rw [show T = unitaryInvT h from rfl]
    exact unitaryInvT_ne_one h hp2
  have hsq : ρ T * ρ T = 1 := by rw [← map_mul, hT2, map_one]
  have hne : ρ T ≠ 1 := by
    intro h1
    have hker : T ∈ ρ.ker := MonoidHom.mem_ker.mpr h1
    have h3 := CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.ker_pow_three h T hker
    have h31 : T = T ^ 3 := by rw [pow_succ, sq, hT2, one_mul]
    exact hT1 (h31.trans h3)
  exact orderOf_eq_prime (by rwa [sq]) hne

theorem isCoatom_centralizer_statedProj_of_orderOf (h : UnitaryFieldData p f K) (hp2 : p ≠ 2)
    {s : StatedProj (unitarySU p f K 3)} (hs : orderOf s = 2) :
    IsCoatom (Subgroup.centralizer ({s} : Set (StatedProj (unitarySU p f K 3)))) := by
  classical
  let S := unitarySU p f K 3
  let T : S := unitaryInvT h
  let t : StatedProj S := CFSG.RankThree.CentralCover.statedProjMk S T
  have ht : orderOf t = 2 := by
    rw [show t = CFSG.RankThree.CentralCover.statedProjMk S (unitaryInvT h) from rfl]
    exact orderOf_statedProj_unitaryInvT h hp2
  have hbase : IsCoatom (Subgroup.centralizer ({t} : Set (StatedProj S))) := by
    rw [show t = CFSG.RankThree.CentralCover.statedProjMk S (unitaryInvT h) from rfl]
    exact isCoatom_centralizer_statedProj_unitaryInvT h hp2
  obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.Q3.TL4.E3S3Gen.exists_conj_psu3 h hp2
    (a := s) (b := t) hs ht
  refine CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isCoatom_centralizer_of_equiv
    (MulAut.conj g) s ?_
  have hgs : (MulAut.conj g) s = t := by
    rw [MulAut.conj_apply]
    exact hg
  rw [hgs]
  exact hbase


end Unitary
end ClassicalGroups
end CFSG

end
