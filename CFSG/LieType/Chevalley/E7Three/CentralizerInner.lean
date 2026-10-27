module

public import CFSG.LieType.Chevalley.E7Three.CentralizerFour
public import CFSG.LieType.Chevalley.E7Three.Automizer
import CFSG.LieType.Chevalley.E7Three.CentralizerBaseChange

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KA5L CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.FourCube CFSG.LieType.Chevalley.E7Three.Weyl
  CFSG.LieType.Chevalley.E7Three.Product

open scoped MatrixGroups Kronecker

variable {K : Type} [Field K]

theorem exists_sl2_conj_of_intertwiner [IsAlgClosed K] {ψ : SL(2, K) → SL(2, K)}
    {B : Matrix (Fin 2) (Fin 2) K} (hB : B.det ≠ 0)
    (h : ∀ X : SL(2, K), (ψ X : Matrix (Fin 2) (Fin 2) K) * B = B * X) :
    ∃ A : SL(2, K), ∀ X, ψ X = A * X * A⁻¹ := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self B.det
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hB (by rw [hr, mul_zero])
  refine ⟨⟨r⁻¹ • B, ?_⟩, fun X => eq_mul_inv_of_mul_eq (Subtype.ext ?_)⟩
  · rw [Matrix.det_smul, Fintype.card_fin, hr, ← sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr0)]
  · change (ψ X : Matrix (Fin 2) (Fin 2) K) * (r⁻¹ • B) = (r⁻¹ • B) * X
    rw [Matrix.mul_smul, h X, Matrix.smul_mul]

theorem det_ne_zero_of_intertwiner {ψ : SL(2, K) → SL(2, K)} {B : Matrix (Fin 2) (Fin 2) K}
    (hB : B ≠ 0) (h : ∀ X : SL(2, K), B * X = (ψ X : Matrix (Fin 2) (Fin 2) K) * B) :
    B.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have key : ∀ w : Fin 2 → K, B *ᵥ w = 0 → B *ᵥ ![w 1, 0] = 0 ∧ B *ᵥ ![0, w 0] = 0 := by
    intro w hw
    have hu : B *ᵥ ((uSL 1 : SL(2, K)) *ᵥ w) = 0 := by
      rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    have hl : B *ᵥ ((vSL 1 : SL(2, K)) *ᵥ w) = 0 := by
      rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_zero]
    have eu : ![w 1, 0] = ((uSL 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w - w := by
      ext i
      fin_cases i <;> simp [uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have el : ![0, w 0] = ((vSL 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w - w := by
      ext i
      fin_cases i <;> simp [vSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [eu, el, Matrix.mulVec_sub, Matrix.mulVec_sub, hu, hl, hw, sub_zero]
    exact ⟨rfl, rfl⟩
  have hB0 : B *ᵥ ![1, 0] = 0 → B *ᵥ ![0, 1] = 0 → B = 0 := by
    intro h0 h1
    ext i j
    have e0 := congrFun h0 i
    have e1 := congrFun h1 i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e0 e1
    simp at e0 e1
    fin_cases j
    · simpa using e0
    · simpa using e1
  have hscale : ∀ (c : K) (w : Fin 2 → K), c ≠ 0 → B *ᵥ (c • w) = 0 → B *ᵥ w = 0 := by
    intro c w hc hw
    rw [Matrix.mulVec_smul] at hw
    exact (smul_eq_zero.1 hw).resolve_left hc
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      exact hv0 (by ext i; fin_cases i <;> simp [h0, h1])
    have hb1 : B *ᵥ ![0, 1] = 0 :=
      hscale (v 0) _ h0 (by rw [show v 0 • ![(0 : K), 1] = ![0, v 0] by simp]; exact (key v hv).2)
    have hb0 : B *ᵥ ![1, 0] = 0 := by simpa using (key ![0, 1] hb1).1
    exact hB (hB0 hb0 hb1)
  · have hb0 : B *ᵥ ![1, 0] = 0 :=
      hscale (v 1) _ h1 (by rw [show v 1 • ![(1 : K), 0] = ![v 1, 0] by simp]; exact (key v hv).1)
    have hb1 : B *ᵥ ![0, 1] = 0 := by simpa using (key ![1, 0] hb0).2
    exact hB (hB0 hb0 hb1)

variable [CharP K 2]

theorem mul_kronecker_one_apply (N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K)
    (X : Matrix (Fin 2) (Fin 2) K) (i k : Fin 2) (a c : Fin 3) :
    (N * (X ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K))) (i, a) (k, c) = ∑ j, N (i, a) (j, c) * X j k := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem kronecker_one_mul_apply (N : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K)
    (X : Matrix (Fin 2) (Fin 2) K) (i k : Fin 2) (a c : Fin 3) :
    ((X ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) * N) (i, a) (k, c) = ∑ j, X i j * N (j, a) (k, c) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem exists_sl2_conj_of_kronSL2 [IsAlgClosed K] (Y : SL(6, K)) (ψ : SL(2, K) → SL(2, K))
    (h : ∀ X, Y * kronSL2 K X * Y⁻¹ = kronSL2 K (ψ X)) :
    ∃ A : SL(2, K), ∀ X, ψ X = A * X * A⁻¹ := by
  set Yt : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) K :=
    reindex e6.symm e6.symm (Y : Matrix (Fin 6) (Fin 6) K) with hYt
  have hY : (Y : Matrix (Fin 6) (Fin 6) K) = reindex e6 e6 Yt := by
    ext p q
    simp [hYt]
  have hm : ∀ X : SL(2, K), Yt * ((X : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) =
      ((ψ X : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) K)) * Yt := by
    intro X
    have e := congrArg (fun g : SL(6, K) => (g : Matrix (Fin 6) (Fin 6) K))
      (mul_inv_eq_iff_eq_mul.1 (h X))
    change (Y : Matrix (Fin 6) (Fin 6) K) * (kronSL2 K X : Matrix (Fin 6) (Fin 6) K) =
      (kronSL2 K (ψ X) : Matrix (Fin 6) (Fin 6) K) * Y at e
    rw [coe_kronSL2, coe_kronSL2, hY, reindex_e6_mul, reindex_e6_mul] at e
    exact (reindex e6 e6).injective e
  have hslice : ∀ (a c : Fin 3) (X : SL(2, K)),
      (Matrix.of fun i j => Yt (i, a) (j, c)) * (X : Matrix (Fin 2) (Fin 2) K) =
        (ψ X : Matrix (Fin 2) (Fin 2) K) * Matrix.of fun i j => Yt (i, a) (j, c) := by
    intro a c X
    ext i k
    have e := congrFun (congrFun (hm X) (i, a)) (k, c)
    rw [mul_kronecker_one_apply, kronecker_one_mul_apply] at e
    simpa [Matrix.mul_apply] using e
  obtain ⟨a, c, hne⟩ : ∃ a c : Fin 3, (Matrix.of fun i j => Yt (i, a) (j, c)) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ a c : Fin 3, (Matrix.of fun i j => Yt (i, a) (j, c)) = 0 := fun a c => by
      by_contra h'
      exact hcon ⟨a, c, h'⟩
    have h0 : Yt = 0 := by
      ext ⟨i, a⟩ ⟨j, c⟩
      exact congrFun (congrFun (hcon' a c) i) j
    have hdet : (Y : Matrix (Fin 6) (Fin 6) K).det = 1 := Y.2
    rw [hY, Matrix.det_reindex_self, h0, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  exact exists_sl2_conj_of_intertwiner (det_ne_zero_of_intertwiner hne (hslice a c))
    fun X => (hslice a c X).symm

theorem HSL_inv_eq (r : Kˣ) : (HSL r : SL(2, K))⁻¹ = HSL r⁻¹ := ((diagSL2 K).map_inv r).symm

theorem coe_HSL_conj (r : Kˣ) (x : SL(2, K)) :
    ((HSL r * x * (HSL r)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![(x : Matrix (Fin 2) (Fin 2) K) 0 0, (r : K) ^ 2 * (x : Matrix (Fin 2) (Fin 2) K) 0 1;
        (r : K)⁻¹ ^ 2 * (x : Matrix (Fin 2) (Fin 2) K) 1 0, (x : Matrix (Fin 2) (Fin 2) K) 1 1] := by
  rw [HSL_inv_eq]
  have hr : (r : K) ≠ 0 := r.ne_zero
  change (HSL r : Matrix (Fin 2) (Fin 2) K) * (x : Matrix (Fin 2) (Fin 2) K) *
    (HSL r⁻¹ : Matrix (Fin 2) (Fin 2) K) = _
  rw [Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K)]
  simp only [HSL, Matrix.mul_fin_two, Units.val_inv_eq_inv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem HSL_conj_uSL_eq (r : Kˣ) (t : K) : HSL r * uSL t * (HSL r)⁻¹ = uSL ((r : K) ^ 2 * t) := by
  apply Subtype.ext
  rw [coe_HSL_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL]

theorem HSL_conj_vSL_eq (r : Kˣ) (t : K) :
    HSL r * vSL t * (HSL r)⁻¹ = vSL ((r : K)⁻¹ ^ 2 * t) := by
  apply Subtype.ext
  rw [coe_HSL_conj]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vSL]

theorem cube_root_values [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    (ζ : K) ≠ 0 ∧ (ζ : K) ≠ 1 ∧ (ζ : K) ^ 2 ≠ 0 ∧ (ζ : K) ^ 2 ≠ 1 ∧ (ζ : K) ≠ (ζ : K) ^ 2 ∧
      ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ t ^ 2 + t + 1 ≠ 0 := by
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hz0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have hz1 : (ζ : K) ≠ 1 := hζK.ne_one (by norm_num)
  have hz2 : (ζ : K) ^ 2 ≠ 1 := hζK.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hzz : (ζ : K) ^ 2 + ζ + 1 = 0 := by
    have := hζK.geom_sum_eq_zero (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at this
    linear_combination this
  have hroot : ∀ t : K, t ^ 2 + t + 1 = 0 → t = ζ ∨ t = (ζ : K) ^ 2 := by
    intro t ht
    have h3 : (ζ : K) ^ 3 = 1 := hζK.pow_eq_one
    have : (t - ζ) * (t - (ζ : K) ^ 2) = 0 := by linear_combination ht - t * hzz + h3
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (sub_eq_zero.1 h)
  refine ⟨hz0, hz1, pow_ne_zero 2 hz0, hz2, fun h => hz1 ?_, ?_⟩
  · have h' : (ζ : K) * (ζ - 1) = 0 := by linear_combination -h
    exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_left hz0)
  · classical
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({0, 1, (ζ : K), (ζ : K) ^ 2} : Finset K)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    obtain ⟨h0, h1, h2, h3⟩ := ht
    exact ⟨t, h0, h1, fun h => (hroot t h).elim h2 h3⟩

theorem exists_unit_sq [IsAlgClosed K] {t : K} (ht : t ≠ 0) : ∃ r : Kˣ, (r : K) ^ 2 = t := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq t (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact ht (by rw [← hz]; ring)
  exact ⟨Units.mk0 z hz0, hz⟩

theorem exists_uSL_of_fix_HSL [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (ψ : SL(2, K) →* SL(2, K)) (hinj : Function.Injective ψ)
    (hT : ∀ r : Kˣ, ψ (HSL r) = HSL r) : ∃ b : K, b ≠ 0 ∧ ∀ t, ψ (uSL t) = uSL (b * t) := by
  obtain ⟨hz0, hz1, hz20, hz21, hzz, t₀, ht₀0, ht₀1, ht₀q⟩ := cube_root_values hζ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set x := ψ (uSL 1) with hx
  set a := (x : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (x : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (x : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (x : Matrix (Fin 2) (Fin 2) K) 1 1
  have hent : ∀ t : K, t ≠ 0 → ((ψ (uSL t) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![a, t * b; t⁻¹ * c, d] := by
    intro t ht
    obtain ⟨r, hr⟩ := exists_unit_sq ht
    rw [← hr, ← mul_one ((r : K) ^ 2), ← HSL_conj_uSL_eq, map_mul, map_mul, map_inv, hT,
      coe_HSL_conj, mul_one, inv_pow]
  have hmul : ∀ t : K, t ≠ 0 → t ≠ 1 →
      !![a, b; c, d] * !![a, t * b; t⁻¹ * c, d] = !![a, (1 + t) * b; (1 + t)⁻¹ * c, d] := by
    intro t ht0 ht1
    have h1t : 1 + t ≠ 0 := fun h => ht1 (by linear_combination h2 * t - h)
    have e := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K))
      (show ψ (uSL 1) * ψ (uSL t) = ψ (uSL (1 + t)) by
        rw [← map_mul, CFSG.RankThree.PartOne.KLAY.uSL_mul_uSL])
    change (ψ (uSL 1) : Matrix (Fin 2) (Fin 2) K) * (ψ (uSL t) : Matrix (Fin 2) (Fin 2) K) = _ at e
    rw [hent t ht0, hent (1 + t) h1t, ← hx, Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K)] at e
    exact e
  have e00 : ∀ t : K, t ≠ 0 → t ≠ 1 → a * a + b * (t⁻¹ * c) = a := fun t h0 h1 => by
    simpa using congrFun (congrFun (hmul t h0 h1) 0) 0
  have e10 : ∀ t : K, t ≠ 0 → t ≠ 1 → c * a + d * (t⁻¹ * c) = (1 + t)⁻¹ * c := fun t h0 h1 => by
    simpa using congrFun (congrFun (hmul t h0 h1) 1) 0
  have hdet : a * d - b * c = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  have hbc : b * c = 0 := by
    have h1 := e00 _ hz0 hz1
    have h2' := e00 _ hz20 hz21
    have : b * c * (((ζ : K))⁻¹ - ((ζ : K) ^ 2)⁻¹) = 0 := by linear_combination h1 - h2'
    refine (mul_eq_zero.1 this).resolve_right fun h => hzz ?_
    have := sub_eq_zero.1 h
    exact inv_injective this
  have had : a * d = 1 := by linear_combination hdet + hbc
  have ha : a = 1 := by
    have h1 := e00 _ hz0 hz1
    have : a * (a - 1) = 0 := by linear_combination h1 - (ζ : K)⁻¹ * hbc
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (left_ne_zero_of_mul_eq_one had))
  have hd : d = 1 := by rw [ha, one_mul] at had; exact had
  have hc : c = 0 := by
    have h1 := e10 t₀ ht₀0 ht₀1
    rw [ha, hd] at h1
    have h1t : 1 + t₀ ≠ 0 := fun h => ht₀1 (by linear_combination h2 * t₀ - h)
    have hu : t₀⁻¹ * t₀ = 1 := inv_mul_cancel₀ ht₀0
    have hv : (1 + t₀)⁻¹ * (1 + t₀) = 1 := inv_mul_cancel₀ h1t
    have key : c * (t₀ ^ 2 + t₀ + 1) = 0 := by
      linear_combination (t₀ * (1 + t₀)) * h1 - (c * (1 + t₀)) * hu + (c * t₀) * hv
    exact (mul_eq_zero.1 key).resolve_right ht₀q
  have hb : b ≠ 0 := by
    intro hb0
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K)]
      change !![a, b; c, d] = (1 : Matrix (Fin 2) (Fin 2) K)
      rw [ha, hb0, hc, hd]
      exact Matrix.one_fin_two.symm
    have : uSL (1 : K) = 1 := hinj (by rw [← hx, hx1, map_one])
    have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) this) 0) 1
    simp [uSL] at this
  refine ⟨b, hb, fun t => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht
  · rw [mul_zero, CFSG.RankThree.PartOne.KLAY.uSL_zero', map_one]
  · apply Subtype.ext
    rw [hent t ht, ha, hc, hd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uSL, mul_comm]

theorem exists_vSL_of_fix_HSL [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (ψ : SL(2, K) →* SL(2, K)) (hinj : Function.Injective ψ)
    (hT : ∀ r : Kˣ, ψ (HSL r) = HSL r) : ∃ c : K, c ≠ 0 ∧ ∀ t, ψ (vSL t) = vSL (c * t) := by
  obtain ⟨hz0, hz1, hz20, hz21, hzz, t₀, ht₀0, ht₀1, ht₀q⟩ := cube_root_values hζ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set x := ψ (vSL 1) with hx
  set a := (x : Matrix (Fin 2) (Fin 2) K) 0 0
  set b := (x : Matrix (Fin 2) (Fin 2) K) 0 1
  set c := (x : Matrix (Fin 2) (Fin 2) K) 1 0
  set d := (x : Matrix (Fin 2) (Fin 2) K) 1 1
  have hent : ∀ t : K, t ≠ 0 → ((ψ (vSL t) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![a, t⁻¹ * b; t * c, d] := by
    intro t ht
    obtain ⟨r, hr⟩ := exists_unit_sq (inv_ne_zero ht)
    have hvt : vSL t = HSL r * vSL 1 * (HSL r)⁻¹ := by
      rw [HSL_conj_vSL_eq, inv_pow, hr, inv_inv, mul_one]
    rw [hvt, map_mul, map_mul, map_inv, hT, coe_HSL_conj, inv_pow, hr, inv_inv]
  have hmul : ∀ t : K, t ≠ 0 → t ≠ 1 →
      !![a, b; c, d] * !![a, t⁻¹ * b; t * c, d] = !![a, (1 + t)⁻¹ * b; (1 + t) * c, d] := by
    intro t ht0 ht1
    have h1t : 1 + t ≠ 0 := fun h => ht1 (by linear_combination h2 * t - h)
    have e := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K))
      (show ψ (vSL 1) * ψ (vSL t) = ψ (vSL (1 + t)) by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        change ((vSL (1 : K) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          ((vSL t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
        simp only [vSL, Matrix.mul_fin_two]
        ext i j
        fin_cases i <;> fin_cases j <;> simp)
    change (ψ (vSL 1) : Matrix (Fin 2) (Fin 2) K) * (ψ (vSL t) : Matrix (Fin 2) (Fin 2) K) = _ at e
    rw [hent t ht0, hent (1 + t) h1t, ← hx, Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K)] at e
    exact e
  have e00 : ∀ t : K, t ≠ 0 → t ≠ 1 → a * a + b * (t * c) = a := fun t h0 h1 => by
    simpa using congrFun (congrFun (hmul t h0 h1) 0) 0
  have e01 : ∀ t : K, t ≠ 0 → t ≠ 1 → a * (t⁻¹ * b) + b * d = (1 + t)⁻¹ * b := fun t h0 h1 => by
    simpa using congrFun (congrFun (hmul t h0 h1) 0) 1
  have hdet : a * d - b * c = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  have hbc : b * c = 0 := by
    have h1 := e00 _ hz0 hz1
    have h2' := e00 _ hz20 hz21
    have : b * c * ((ζ : K) - (ζ : K) ^ 2) = 0 := by linear_combination h1 - h2'
    exact (mul_eq_zero.1 this).resolve_right fun h => hzz (sub_eq_zero.1 h)
  have had : a * d = 1 := by linear_combination hdet + hbc
  have ha : a = 1 := by
    have h1 := e00 _ hz0 hz1
    have : a * (a - 1) = 0 := by linear_combination h1 - (ζ : K) * hbc
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (left_ne_zero_of_mul_eq_one had))
  have hd : d = 1 := by rw [ha, one_mul] at had; exact had
  have hb : b = 0 := by
    have h1 := e01 t₀ ht₀0 ht₀1
    rw [ha, hd] at h1
    have h1t : 1 + t₀ ≠ 0 := fun h => ht₀1 (by linear_combination h2 * t₀ - h)
    have hu : t₀⁻¹ * t₀ = 1 := inv_mul_cancel₀ ht₀0
    have hv : (1 + t₀)⁻¹ * (1 + t₀) = 1 := inv_mul_cancel₀ h1t
    have key : b * (t₀ ^ 2 + t₀ + 1) = 0 := by
      linear_combination (t₀ * (1 + t₀)) * h1 - (b * (1 + t₀)) * hu + (b * t₀) * hv
    exact (mul_eq_zero.1 key).resolve_right ht₀q
  have hc : c ≠ 0 := by
    intro hc0
    have hx1 : x = 1 := by
      apply Subtype.ext
      rw [Matrix.eta_fin_two (x : Matrix (Fin 2) (Fin 2) K)]
      change !![a, b; c, d] = (1 : Matrix (Fin 2) (Fin 2) K)
      rw [ha, hb, hc0, hd]
      exact Matrix.one_fin_two.symm
    have : vSL (1 : K) = 1 := hinj (by rw [← hx, hx1, map_one])
    have := congrFun (congrFun (congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) this) 1) 0
    simp [vSL] at this
  refine ⟨c, hc, fun t => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht
  · have h0 : (vSL (0 : K) : SL(2, K)) = 1 := Subtype.ext (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vSL])
    rw [mul_zero, h0, map_one]
  · apply Subtype.ext
    rw [hent t ht, ha, hb, hd]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vSL, mul_comm]

theorem exists_sl2_conj_of_fix_HSL [IsAlgClosed K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    (ψ : SL(2, K) →* SL(2, K)) (hinj : Function.Injective ψ) (hT : ∀ r : Kˣ, ψ (HSL r) = HSL r) :
    ∃ A : SL(2, K), ∀ X, ψ X = A * X * A⁻¹ := by
  obtain ⟨b, hb, hu⟩ := exists_uSL_of_fix_HSL hζ ψ hinj hT
  obtain ⟨c, hc, hl⟩ := exists_vSL_of_fix_HSL hζ ψ hinj hT
  obtain ⟨-, M, hM, hMψ⟩ := CFSG.RankThree.Classical.sl2_semilinear_root_compatibility
    (RingEquiv.refl K) (Units.mk0 b hb) (Units.mk0 c hc) ψ (fun t => hu t) (fun t => hl t)
  refine exists_sl2_conj_of_intertwiner (B := (M : Matrix (Fin 2) (Fin 2) K)) ?_ fun X => ?_
  · rw [hM, Matrix.det_fin_two_of]
    simpa using hb
  · have hmap : (Matrix.SpecialLinearGroup.map ((RingEquiv.refl K) : K →+* K) X :
        Matrix (Fin 2) (Fin 2) K) = X := by
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe]
    rw [hMψ X, hmap, Matrix.mul_assoc, M.inv_mul, Matrix.mul_one]

theorem mem_normalizer_centralizer_of_mem_normalizer {G : Type*} [Group G] {E : Subgroup G}
    {h : G} (hN : h ∈ Subgroup.normalizer (E : Set G)) :
    h ∈ Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro g
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg e he
    have he' : h⁻¹ * e * h ∈ E :=
      (hN _).2 (by rwa [show h * (h⁻¹ * e * h) * h⁻¹ = e by group])
    have := hg _ he'
    calc e * (h * g * h⁻¹) = h * ((h⁻¹ * e * h) * g) * h⁻¹ := by group
      _ = h * (g * (h⁻¹ * e * h)) * h⁻¹ := by rw [this]
      _ = h * g * h⁻¹ * e := by group
  · intro hg e he
    have := hg _ ((hN e).1 he)
    have h' : h * (e * g) * h⁻¹ = h * (g * e) * h⁻¹ := by
      calc h * (e * g) * h⁻¹ = h * e * h⁻¹ * (h * g * h⁻¹) := by group
        _ = h * g * h⁻¹ * (h * e * h⁻¹) := this
        _ = h * (g * e) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')


@[expose] def IsInnerOnCubeSL2 (g : ModGL .E7 K) : Prop :=
  ∃ M : SL(2, K), ∀ X : SL(2, K), g * cubeSL2 K X * g⁻¹ = cubeSL2 K (M * X * M⁻¹)

theorem isInnerOnCubeSL2_one : IsInnerOnCubeSL2 (1 : ModGL .E7 K) :=
  ⟨1, fun X => by simp⟩

theorem IsInnerOnCubeSL2.mul {g g' : ModGL .E7 K} (hg : IsInnerOnCubeSL2 g)
    (hg' : IsInnerOnCubeSL2 g') : IsInnerOnCubeSL2 (g * g') := by
  obtain ⟨M, hM⟩ := hg
  obtain ⟨M', hM'⟩ := hg'
  refine ⟨M * M', fun X => ?_⟩
  rw [show g * g' * cubeSL2 K X * (g * g')⁻¹ = g * (g' * cubeSL2 K X * g'⁻¹) * g⁻¹ by group,
    hM', hM]
  congr 1
  group

theorem IsInnerOnCubeSL2.inv {g : ModGL .E7 K} (hg : IsInnerOnCubeSL2 g) :
    IsInnerOnCubeSL2 g⁻¹ := by
  obtain ⟨M, hM⟩ := hg
  refine ⟨M⁻¹, fun X => ?_⟩
  have h := hM (M⁻¹ * X * M)
  rw [show M * (M⁻¹ * X * M) * M⁻¹ = X by group] at h
  rw [← h, inv_inv, inv_inv]
  group

theorem coe_mem_normalizer_cubeE {ζ : Kˣ} {hζ : ζ ^ 3 = 1} {n : adjointGroup .E7 K}
    (hn : n ∈ Subgroup.normalizer ((cubeHom ζ hζ).range : Set (adjointGroup .E7 K))) :
    (n : ModGL .E7 K) ∈ Subgroup.normalizer (cubeE ζ hζ : Set (ModGL .E7 K)) := by
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨n * y * n⁻¹, (hn y).1 hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨n⁻¹ * z * n, (hn _).2 (by rwa [show n * (n⁻¹ * z * n) * n⁻¹ = z by group]), ?_⟩
    change (n : ModGL .E7 K)⁻¹ * (z : ModGL .E7 K) * n = x
    rw [show (z : ModGL .E7 K) = n * x * (n : ModGL .E7 K)⁻¹ from hzx]
    group

section Steinberg

variable [IsAlgClosed K]

theorem mem_normalizer_range_cubeSL2 {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {h : ModGL .E7 K}
    (hG : h ∈ adjointGroup .E7 K)
    (hN : h ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K))) :
    h ∈ Subgroup.normalizer ((cubeSL2 K).range : Set (ModGL .E7 K)) := by
  have hC : h ∈ Subgroup.normalizer (cubeCent ζ hζ.pow_eq_one : Set (ModGL .E7 K)) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hG, mem_normalizer_centralizer_of_mem_normalizer hN⟩
  have h' := normalizer_le_normalizer_closedIdentityComponent _ hC
  rwa [closedIdentityComponent_cubeCent hζ] at h'

theorem isInnerOnCubeSL2_of_commute_scalarWord {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {g : ModGL .E7 K} (hG : g ∈ adjointGroup .E7 K) (hs : Commute g (scalarWord ζ : ModGL .E7 K))
    (hN : g ∈ Subgroup.normalizer ((cubeSL2 K).range : Set (ModGL .E7 K))) :
    IsInnerOnCubeSL2 g := by
  obtain ⟨fr⟩ := nativeFrame_exists (K := K)
  have hgT : g ∈ toralCentralizer .E7 K (cubeChar ζ scalarExp) := by
    rw [mem_toralCentralizer, ← scalarWord_val ζ hζ.pow_eq_one]
    exact ⟨hG, by rw [← hs.eq, mul_inv_cancel_right]⟩
  have hgR := toralCentralizer_scalar_le fr ζ hζ hgT
  rw [← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (range_theta_two_le_normalizer fr)] at hgR
  obtain ⟨_, ⟨A, rfl⟩, _, ⟨B, rfl⟩, hAB⟩ := hgR
  dsimp only at hAB
  have hconj : ∀ X : SL(2, K), g * cubeSL2 K X * g⁻¹ = a5Frame K (A * kronSL2 K X * A⁻¹) := by
    intro X
    rw [← hAB, map_mul, map_mul, map_inv]
    change a5Frame K A * theta fr 2 B * a5Frame K (kronSL2 K X) *
      (a5Frame K A * theta fr 2 B)⁻¹ = _
    have hc := (a5Frame_commute_theta_two fr (kronSL2 K X) B).eq
    rw [_root_.mul_inv_rev, mul_assoc (a5Frame K A), ← hc]
    group
  have hmem : ∀ X : SL(2, K), g * cubeSL2 K X * g⁻¹ ∈ (cubeSL2 K).range := fun X =>
    (Subgroup.mem_normalizer_iff.1 hN _).1 ⟨X, rfl⟩
  choose ψ hψ using hmem
  have hk : ∀ X, A * kronSL2 K X * A⁻¹ = kronSL2 K (ψ X) := fun X =>
    a5Frame_injective hζ (by rw [← hconj X, ← hψ X]; rfl)
  obtain ⟨M, hM⟩ := exists_sl2_conj_of_kronSL2 A ψ hk
  exact ⟨M, fun X => by rw [← hψ X, hM X]⟩

theorem isInnerOnCubeSL2_of_fix_fourTorus {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) {g : ModGL .E7 K}
    (hN : g ∈ Subgroup.normalizer ((cubeSL2 K).range : Set (ModGL .E7 K)))
    (hT : ∀ r : Kˣ, g * fourTorus K r * g⁻¹ = fourTorus K r) : IsInnerOnCubeSL2 g := by
  have hmem : ∀ X : SL(2, K), g * cubeSL2 K X * g⁻¹ ∈ (cubeSL2 K).range := fun X =>
    (Subgroup.mem_normalizer_iff.1 hN _).1 ⟨X, rfl⟩
  let e := MonoidHom.ofInjective (cubeSL2_injective (K := K) hζ)
  let c : SL(2, K) →* (cubeSL2 K).range :=
    { toFun := fun X => ⟨g * cubeSL2 K X * g⁻¹, hmem X⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun X Y => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }
  let ψ : SL(2, K) →* SL(2, K) := e.symm.toMonoidHom.comp c
  have hψ : ∀ X, cubeSL2 K (ψ X) = g * cubeSL2 K X * g⁻¹ := fun X =>
    congrArg Subtype.val (e.apply_symm_apply (c X))
  have hinj : Function.Injective ψ := fun X Y hXY => by
    have h := congrArg (cubeSL2 K) hXY
    rw [hψ, hψ] at h
    exact cubeSL2_injective hζ (mul_right_cancel (mul_left_cancel h))
  have hfix : ∀ r : Kˣ, ψ (HSL r) = HSL r := fun r =>
    cubeSL2_injective hζ (by rw [hψ]; exact hT r)
  obtain ⟨M, hM⟩ := exists_sl2_conj_of_fix_HSL hζ ψ hinj hfix
  exact ⟨M, fun X => by rw [← hψ, hM]⟩

end Steinberg

theorem moveElement_conj_fourTorus (r : Kˣ) :
    ((moveElement (K := K) : adjointGroup .E7 K) : ModGL .E7 K) * fourTorus K r *
      ((moveElement (K := K) : adjointGroup .E7 K) : ModGL .E7 K)⁻¹ = fourTorus K r := by
  rw [fourTorus_eq_rootDiagUnit]
  change canonicalRep (coxeterSystem .E7) K move * rootDiagUnit .E7 _ *
    (canonicalRep (coxeterSystem .E7) K move)⁻¹ = _
  rw [CFSG.LieType.Chevalley.canonicalRep_conj_rootDiagUnit]
  congr 1
  funext j
  change rootChar (fun i => r ^ fourTorusExp i)
    (move⁻¹ • (Pi.single j 1 : Fin Tag.E7.rank → ℤ)) = r ^ fourTorusExp j
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootChar_zpow_tuple]
  congr 1
  simp only [move_inv, ← CFSG.RankThree.E6.weylMatrix_apply, weylMatrix_move]
  fin_cases j <;> decide +kernel

theorem conj_cubeHom_of_eq_ggConjAut {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {φ : MulAut CoordinateActions.D} {n : adjointGroup .E7 K}
    (hn : n ∈ Subgroup.normalizer ((cubeHom ζ hζ.pow_eq_one).range : Set (adjointGroup .E7 K)))
    (h : MulAut.congr (Automizer.cubeEquiv ζ hζ) φ =
      CFSG.StandardType.ggConjAut (cubeHom ζ hζ.pow_eq_one).range hn)
    (d : CoordinateActions.D) :
    (n : ModGL .E7 K) * cubeHom ζ hζ.pow_eq_one d * (n : ModGL .E7 K)⁻¹ =
      cubeHom ζ hζ.pow_eq_one (φ d) := by
  have e := congrArg (fun f : MulAut (cubeHom ζ hζ.pow_eq_one).range =>
    (((f (Automizer.cubeEquiv ζ hζ d) : (cubeHom ζ hζ.pow_eq_one).range) :
      adjointGroup .E7 K) : ModGL .E7 K)) h
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at e
  exact e.symm

@[expose] def stepD (l : List CoordinateActions.D) : List CoordinateActions.D :=
  (l ++ l.flatMap fun d =>
    [CoordinateActions.u d, CoordinateActions.v d, CoordinateActions.w d]).dedup

theorem mem_stepD_seven : ∀ d : CoordinateActions.D, d ≠ 1 →
    d ∈ stepD^[7] [CoordinateActions.basis 0] := by
  decide +kernel

section Steinberg

variable [IsAlgClosed K]

theorem exists_inner_conj_cubeHom_eq_scalar {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {d : CoordinateActions.D} (hd : d ≠ 1) :
    ∃ n : ModGL .E7 K, n ∈ adjointGroup .E7 K ∧
      n ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) ∧
        IsInnerOnCubeSL2 n ∧ n * (cubeHom ζ hζ.pow_eq_one d : ModGL .E7 K) * n⁻¹ =
          cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0) := by
  let P : CoordinateActions.D → Prop := fun d => ∃ n : ModGL .E7 K, n ∈ adjointGroup .E7 K ∧
    n ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) ∧
      IsInnerOnCubeSL2 n ∧ n * (cubeHom ζ hζ.pow_eq_one d : ModGL .E7 K) * n⁻¹ =
        cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0)
  have hstep : ∀ (R : ModGL .E7 K) (φ : MulAut CoordinateActions.D), R ∈ adjointGroup .E7 K →
      R ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) → IsInnerOnCubeSL2 R →
        (∀ d, R * cubeHom ζ hζ.pow_eq_one d * R⁻¹ = cubeHom ζ hζ.pow_eq_one (φ d)) →
          ∀ d, P d → P (φ d) := by
    rintro R φ hRG hRN hRI hR d ⟨n, hnG, hnN, hnI, hn⟩
    refine ⟨n * R⁻¹, (adjointGroup .E7 K).mul_mem hnG ((adjointGroup .E7 K).inv_mem hRG),
      Subgroup.mul_mem _ hnN (Subgroup.inv_mem _ hRN), hnI.mul hRI.inv, ?_⟩
    rw [← hR d, ← hn]
    group
  have hs0 : (cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0) : ModGL .E7 K) =
      scalarWord ζ := by
    rw [Automizer.cubeHom_basis]
    rfl
  have hcomm : ∀ (R : ModGL .E7 K) (φ : MulAut CoordinateActions.D),
      φ (CoordinateActions.basis 0) = CoordinateActions.basis 0 →
        (∀ d, R * cubeHom ζ hζ.pow_eq_one d * R⁻¹ = cubeHom ζ hζ.pow_eq_one (φ d)) →
          Commute R (scalarWord ζ : ModGL .E7 K) := fun R φ hφ hR => by
    have h := hR (CoordinateActions.basis 0)
    rw [hφ, hs0] at h
    exact (mul_inv_eq_iff_eq_mul.1 h)
  have hU := (a5CycleElement_mem_normalizer (K := K) ζ hζ.pow_eq_one)
  have hUc := conj_cubeHom_of_eq_ggConjAut hζ hU (Automizer.u_eq_conj_a5Cycle ζ hζ)
  have hUN := coe_mem_normalizer_cubeE hU
  have hUI := isInnerOnCubeSL2_of_commute_scalarWord hζ (a5CycleElement (K := K)).2
    (hcomm _ _ BasisActions.u_basis_zero hUc) (mem_normalizer_range_cubeSL2 hζ
      (a5CycleElement (K := K)).2 hUN)
  obtain ⟨nF, hF, hFc', -, -⟩ := Automizer.exists_fourier_eq_conj (K := K) ζ hζ
  have hFc := conj_cubeHom_of_eq_ggConjAut hζ hF hFc'
  have hFN := coe_mem_normalizer_cubeE hF
  have hFI := isInnerOnCubeSL2_of_commute_scalarWord hζ nF.2
    (hcomm _ _ BasisActions.v_basis_zero hFc) (mem_normalizer_range_cubeSL2 hζ nF.2 hFN)
  have hW := (moveElement_mem_normalizer (K := K) ζ hζ.pow_eq_one)
  have hWc := conj_cubeHom_of_eq_ggConjAut hζ hW (Automizer.w_eq_conj_move ζ hζ)
  have hWN := coe_mem_normalizer_cubeE hW
  have hWI := isInnerOnCubeSL2_of_fix_fourTorus hζ
    (mem_normalizer_range_cubeSL2 hζ (moveElement (K := K)).2 hWN) moveElement_conj_fourTorus
  have hclosed : ∀ l : List CoordinateActions.D, (∀ d ∈ l, P d) → ∀ d ∈ stepD l, P d := by
    intro l hl d hd
    simp only [stepD, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    rcases hd with hd | ⟨d', hd', rfl | rfl | rfl⟩
    · exact hl d hd
    · exact hstep _ _ (a5CycleElement (K := K)).2 hUN hUI hUc d' (hl d' hd')
    · exact hstep _ _ nF.2 hFN hFI hFc d' (hl d' hd')
    · exact hstep _ _ (moveElement (K := K)).2 hWN hWI hWc d' (hl d' hd')
  have hiter : ∀ (k : ℕ) (l : List CoordinateActions.D), (∀ d ∈ l, P d) →
      ∀ d ∈ stepD^[k] l, P d := by
    intro k
    induction k with
    | zero => exact fun l hl => hl
    | succ k ih =>
      intro l hl
      rw [Function.iterate_succ_apply]
      exact ih _ (hclosed l hl)
  refine hiter 7 [CoordinateActions.basis 0] ?_ d (mem_stepD_seven d hd)
  intro d' hd'
  rw [List.mem_singleton] at hd'
  subst hd'
  exact ⟨1, (adjointGroup .E7 K).one_mem, Subgroup.one_mem _, isInnerOnCubeSL2_one, by group⟩

theorem exists_inner_of_mem_normalizer_cubeE {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {h : ModGL .E7 K} (hG : h ∈ adjointGroup .E7 K)
    (hN : h ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K))) :
    ∃ M : SL(2, K), ∀ X : SL(2, K), h * cubeSL2 K X * h⁻¹ = cubeSL2 K (M * X * M⁻¹) := by
  have hs0 : (cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0) : ModGL .E7 K) =
      scalarWord ζ := by
    rw [Automizer.cubeHom_basis]
    rfl
  have hs : (scalarWord ζ : ModGL .E7 K) ∈ cubeE ζ hζ.pow_eq_one := generators_mem_cubeE ζ _ 0
  obtain ⟨d, hd⟩ := mem_cubeE.1 ((Subgroup.mem_normalizer_iff.1 hN _).1 hs)
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [map_one, Subgroup.coe_one] at hd
    have h1 : (scalarWord ζ : ModGL .E7 K) = 1 := by
      rw [show (scalarWord ζ : ModGL .E7 K) = h⁻¹ * (h * scalarWord ζ * h⁻¹) * h by group, hd]
      group
    have h2 : cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0) = 1 :=
      Subtype.ext (by rw [hs0, h1]; rfl)
    have h3 := cubeHom_injective ζ hζ (h2.trans (map_one _).symm)
    exact absurd h3 (by decide +kernel)
  obtain ⟨n, hnG, hnN, hnI, hn⟩ := exists_inner_conj_cubeHom_eq_scalar hζ hd1
  have hnh : Commute (n * h) (scalarWord ζ : ModGL .E7 K) := by
    have : n * h * scalarWord ζ * (n * h)⁻¹ = scalarWord ζ :=
      calc n * h * scalarWord ζ * (n * h)⁻¹ = n * (h * scalarWord ζ * h⁻¹) * n⁻¹ := by group
        _ = n * (cubeHom ζ hζ.pow_eq_one d : ModGL .E7 K) * n⁻¹ := by rw [hd]
        _ = cubeHom ζ hζ.pow_eq_one (CoordinateActions.basis 0) := hn
        _ = scalarWord ζ := hs0
    exact mul_inv_eq_iff_eq_mul.1 this
  have hI := isInnerOnCubeSL2_of_commute_scalarWord hζ
    ((adjointGroup .E7 K).mul_mem hnG hG) hnh
    (mem_normalizer_range_cubeSL2 hζ ((adjointGroup .E7 K).mul_mem hnG hG)
      (Subgroup.mul_mem _ hnN hN))
  have := hnI.inv.mul hI
  rwa [inv_mul_cancel_left] at this

theorem exists_inner_of_mem_normalizer_cubeHom_range {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3)
    {h : adjointGroup .E7 K}
    (hN : h ∈ Subgroup.normalizer ((cubeHom ζ hζ.pow_eq_one).range : Set (adjointGroup .E7 K))) :
    ∃ M : SL(2, K), ∀ X : SL(2, K),
      (h : ModGL .E7 K) * cubeSL2 K X * (h : ModGL .E7 K)⁻¹ = cubeSL2 K (M * X * M⁻¹) :=
  exists_inner_of_mem_normalizer_cubeE hζ h.2 (coe_mem_normalizer_cubeE hN)

theorem exists_inner_baseChangeGL_conj_cubeSL2 {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) (σ : K →+* K)
    {g : ModGL .E7 K} (hg : g ∈ adjointGroup .E7 K)
    (hfix : ∀ e ∈ cubeE ζ hζ.pow_eq_one, baseChangeGL σ (g * e * g⁻¹) = g * e * g⁻¹) :
    ∃ M : SL(2, K), ∀ X : SL(2, K), baseChangeGL σ (g * cubeSL2 K X * g⁻¹) =
      g * cubeSL2 K (M * Matrix.SpecialLinearGroup.map σ X * M⁻¹) * g⁻¹ := by
  set h := g⁻¹ * baseChangeGL σ g with hh
  have hG : h ∈ adjointGroup .E7 K := (adjointGroup .E7 K).mul_mem
    ((adjointGroup .E7 K).inv_mem hg) (baseChangeGL_mem_adjointGroup σ hg)
  have key : ∀ e ∈ cubeE ζ hζ.pow_eq_one, h * baseChangeGL σ e * h⁻¹ = e := by
    intro e he
    have h1 := hfix e he
    rw [map_mul, map_mul, map_inv] at h1
    rw [hh]
    calc g⁻¹ * baseChangeGL σ g * baseChangeGL σ e * (g⁻¹ * baseChangeGL σ g)⁻¹ =
        g⁻¹ * (baseChangeGL σ g * baseChangeGL σ e * (baseChangeGL σ g)⁻¹) * g := by group
      _ = g⁻¹ * (g * e * g⁻¹) * g := by rw [h1]
      _ = e := by group
  have hmap := map_baseChangeGL_cubeE_self σ hζ
  have hN : h ∈ Subgroup.normalizer (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hmap] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [key e he]
      exact he
    · intro hx
      have hx' : x = baseChangeGL σ (h * x * h⁻¹) := by
        have := key _ hx
        calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
          _ = h⁻¹ * (h * baseChangeGL σ (h * x * h⁻¹) * h⁻¹) * h := by rw [this]
          _ = baseChangeGL σ (h * x * h⁻¹) := by group
      rw [hx', ← SetLike.mem_coe, ← hmap]
      exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨M, hM⟩ := exists_inner_of_mem_normalizer_cubeE hζ hG hN
  refine ⟨M, fun X => ?_⟩
  have hgh : baseChangeGL σ g = g * h := by rw [hh]; group
  rw [map_mul, map_mul, map_inv, baseChangeGL_cubeSL2, hgh, ← hM]
  group

end Steinberg

end CFSG.LieType.Chevalley.E7Three.Centralizer
