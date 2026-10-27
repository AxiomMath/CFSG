module

public import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open Matrix
open scoped commutatorElement

section FiniteGeometry

theorem plane_four_of_frame : ∀ x4 y4 z4 x5 y5 z5 : ZMod 3, ∃ a b c t : ZMod 3,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
    4 ≤ (Finset.univ.filter fun j : Fin 6 => a * ![0, 1, 0, 0, x4, x5] j +
      b * ![0, 0, 1, 0, y4, y5] j + c * ![0, 0, 0, 1, z4, z5] j = t).card := by
  decide +kernel

theorem exists_plane_four (v₁ v₂ v₃ : Fin 6 → ZMod 3) :
    ∃ a b c t : ZMod 3, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      4 ≤ (Finset.univ.filter fun j : Fin 6 => a * v₁ j + b * v₂ j + c * v₃ j = t).card := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set M : Matrix (Fin 3) (Fin 3) (ZMod 3) :=
    !![v₁ 1 - v₁ 0, v₁ 2 - v₁ 0, v₁ 3 - v₁ 0;
       v₂ 1 - v₂ 0, v₂ 2 - v₂ 0, v₂ 3 - v₂ 0;
       v₃ 1 - v₃ 0, v₃ 2 - v₃ 0, v₃ 3 - v₃ 0] with hM
  by_cases hdet : M.det = 0
  · obtain ⟨w, hw, hwM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      apply hw
      ext i
      fin_cases i <;> simp [hcon]
    refine ⟨w 0, w 1, w 2, w 0 * v₁ 0 + w 1 * v₂ 0 + w 2 * v₃ 0, hw', ?_⟩
    have h1 := congrFun hwM 0
    have h2 := congrFun hwM 1
    have h3 := congrFun hwM 2
    simp [hM, Matrix.vecMul, dotProduct, Fin.sum_univ_three] at h1 h2 h3
    have hsub : ({0, 1, 2, 3} : Finset (Fin 6)) ⊆ Finset.univ.filter fun j : Fin 6 =>
        w 0 * v₁ j + w 1 * v₂ j + w 2 * v₃ j = w 0 * v₁ 0 + w 1 * v₂ 0 + w 2 * v₃ 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hj with rfl | rfl | rfl | rfl
      · rfl
      · linear_combination h1
      · linear_combination h2
      · linear_combination h3
    exact le_trans (by decide) (Finset.card_le_card hsub)
  · have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
    set N : Matrix (Fin 3) (Fin 3) (ZMod 3) := M⁻¹ with hN
    have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hunit
    have hcol : ∀ k : Fin 3, N *ᵥ (fun i => M i k) = Pi.single k 1 := by
      intro k
      have h1 : (fun i => M i k) = M *ᵥ Pi.single k 1 := by
        rw [Matrix.mulVec_single_one]
        rfl
      rw [h1, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    set d : Fin 6 → Fin 3 → ZMod 3 := fun j => ![v₁ j - v₁ 0, v₂ j - v₂ 0, v₃ j - v₃ 0] with hd
    set q : Fin 6 → Fin 3 → ZMod 3 := fun j => N *ᵥ d j with hq
    have hq0 : q 0 = 0 := by
      have : d 0 = 0 := by
        ext i; fin_cases i <;> simp [hd]
      simp [hq, this]
    have hq1 : q 1 = Pi.single 0 1 := by
      have : d 1 = fun i => M i 0 := by
        ext i; fin_cases i <;> simp [hd, hM]
      rw [hq]; simp only [this]; exact hcol 0
    have hq2 : q 2 = Pi.single 1 1 := by
      have : d 2 = fun i => M i 1 := by
        ext i; fin_cases i <;> simp [hd, hM]
      rw [hq]; simp only [this]; exact hcol 1
    have hq3 : q 3 = Pi.single 2 1 := by
      have : d 3 = fun i => M i 2 := by
        ext i; fin_cases i <;> simp [hd, hM]
      rw [hq]; simp only [this]; exact hcol 2
    obtain ⟨a, b, c, t, habc, hcnt⟩ :=
      plane_four_of_frame (q 4 0) (q 4 1) (q 4 2) (q 5 0) (q 5 1) (q 5 2)
    set w : Fin 3 → ZMod 3 := ![a, b, c] ᵥ* N with hw
    have hwd : ∀ j, a * q j 0 + b * q j 1 + c * q j 2 =
        (w 0 * v₁ j + w 1 * v₂ j + w 2 * v₃ j) - (w 0 * v₁ 0 + w 1 * v₂ 0 + w 2 * v₃ 0) := by
      intro j
      have : ![a, b, c] ⬝ᵥ q j = w ⬝ᵥ d j := by
        rw [hq]; simp only [hw]
        rw [Matrix.dotProduct_mulVec]
      simp only [dotProduct, Fin.sum_univ_three] at this
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at this
      simp [hd] at this
      linear_combination this
    have hwne : w ≠ 0 := by
      intro h0
      have : w ᵥ* M = ![a, b, c] := by
        rw [hw, Matrix.vecMul_vecMul, hNM, Matrix.vecMul_one]
      rw [h0, Matrix.zero_vecMul] at this
      rcases habc with h | h | h
      · exact h (by simpa using (congrFun this 0).symm)
      · exact h (by simpa using (congrFun this 1).symm)
      · exact h (by simpa using (congrFun this 2).symm)
    refine ⟨w 0, w 1, w 2, t + (w 0 * v₁ 0 + w 1 * v₂ 0 + w 2 * v₃ 0), ?_, ?_⟩
    · by_contra hcon
      simp only [not_or, not_not] at hcon
      apply hwne
      ext i
      fin_cases i <;> simp [hcon]
    · have hcoord : ∀ j : Fin 6, a * ![0, 1, 0, 0, q 4 0, q 5 0] j +
          b * ![0, 0, 1, 0, q 4 1, q 5 1] j + c * ![0, 0, 0, 1, q 4 2, q 5 2] j =
          a * q j 0 + b * q j 1 + c * q j 2 := by
        intro j
        fin_cases j
        · simp [hq0]
        · simp [hq1]
        · simp [hq2]
        · simp [hq3]
        · rfl
        · rfl
      convert hcnt using 2
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcoord j, hwd j]
      constructor <;> intro h <;> linear_combination h

end FiniteGeometry

section EigenDim

@[expose] noncomputable def eigenDim {n : ℕ} {K : Type*} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (c : K) : ℕ :=
  Module.finrank K
    (LinearMap.ker (Matrix.toLin' M - c • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))))

theorem eigenDim_smul {n : ℕ} {K : Type*} [Field K] (M : Matrix (Fin n) (Fin n) K) {s : K}
    (hs : s ≠ 0) (t : K) : eigenDim (s • M) (s * t) = eigenDim M t := by
  unfold eigenDim
  have : Matrix.toLin' (s • M) - (s * t) • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K)) =
      s • (Matrix.toLin' M - t • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))) := by
    ext v i
    simp [smul_sub, mul_smul]
  rw [this, LinearMap.ker_smul _ _ hs]

theorem card_le_eigenDim {n : ℕ} {K : Type*} [Field K] [DecidableEq K]
    (X P : Matrix (Fin n) (Fin n) K) (hP : IsUnit P.det) (d : Fin n → K)
    (hXP : X * P = P * diagonal d) (c : K) :
    (Finset.univ.filter fun j => d j = c).card ≤ eigenDim X c := by
  set J : Finset (Fin n) := Finset.univ.filter fun j => d j = c with hJ
  let u : J → (Fin n → K) := fun j => P *ᵥ Pi.single (j : Fin n) 1
  have hker : LinearMap.ker (Matrix.toLin' P) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : P⁻¹ *ᵥ (P *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hP, Matrix.one_mulVec]
    rw [← h1]
    simpa using congrArg (fun y => P⁻¹ *ᵥ y) hx
  have hli : LinearIndependent K u := by
    have h0 : LinearIndependent K (fun j : Fin n => (Pi.single j 1 : Fin n → K)) := by
      have := (Pi.basisFun K (Fin n)).linearIndependent
      convert this using 1
      funext j
      rw [Pi.basisFun_apply]
    have h1 : LinearIndependent K (fun j : J => (Pi.single (j : Fin n) 1 : Fin n → K)) :=
      h0.comp (fun j : J => (j : Fin n)) Subtype.val_injective
    exact h1.map' (Matrix.toLin' P) hker
  have hmem : ∀ j : J, u j ∈ LinearMap.ker (Matrix.toLin' X - c • (LinearMap.id :
      (Fin n → K) →ₗ[K] (Fin n → K))) := by
    intro j
    have hj : d (j : Fin n) = c := (Finset.mem_filter.1 j.2).2
    rw [LinearMap.mem_ker]
    simp only [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply, LinearMap.id_apply]
    show X *ᵥ (P *ᵥ Pi.single (j : Fin n) 1) - c • (P *ᵥ Pi.single (j : Fin n) 1) = 0
    rw [Matrix.mulVec_mulVec, hXP, ← Matrix.mulVec_mulVec]
    have : diagonal d *ᵥ (Pi.single (j : Fin n) (1 : K)) = c • Pi.single (j : Fin n) (1 : K) := by
      rw [Matrix.mulVec_single_one]
      ext i
      by_cases hi : i = j
      · subst hi; simp [Matrix.diagonal_apply_eq, hj]
      · simp [Matrix.diagonal_apply_ne _ hi, Pi.single_apply, hi]
    rw [this, Matrix.mulVec_smul, sub_self]
  have hspan : Submodule.span K (Set.range u) ≤ LinearMap.ker (Matrix.toLin' X - c •
      (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hmem j
  calc J.card = Fintype.card J := (Fintype.card_coe J).symm
    _ = Module.finrank K (Submodule.span K (Set.range u)) := (finrank_span_eq_card hli).symm
    _ ≤ eigenDim X c := Submodule.finrank_mono hspan

theorem zeta_pow_eq_iff {K : Type*} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (m n : ℕ) :
    ζ ^ m = ζ ^ n ↔ (m : ZMod 3) = (n : ZMod 3) := by
  have key : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 3) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 3, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [ZMod.natCast_eq_natCast_iff', key m, key n]
  constructor
  · intro h
    exact hζ.pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h
  · intro h
    rw [h]

theorem exists_pow_mul_eigenDim_ge_four {K : Type*} [Field K] [DecidableEq K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 3) (g : Fin 3 → GL (Fin 6) K) (P : GL (Fin 6) K)
    (hg3 : ∀ i, g i ^ 3 = 1)
    (hdiag : ∀ i, ((P⁻¹ * g i * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) :
    ∃ a b c : ℕ, ¬ (3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c) ∧ ∃ t : K,
      4 ≤ eigenDim ((g 0 ^ a * g 1 ^ b * g 2 ^ c : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) t := by
  set d : Fin 3 → Fin 6 → K := fun i j =>
    ((P⁻¹ * g i * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) j j with hd
  have hdiag' : ∀ i, ((P⁻¹ * g i * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal (d i) := fun i => ((hdiag i).diagonal_diag).symm
  have hPP : (P : Matrix (Fin 6) (Fin 6) K) * ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hgP : ∀ i, (P : Matrix (Fin 6) (Fin 6) K) * diagonal (d i) =
      (g i : Matrix (Fin 6) (Fin 6) K) * P := by
    intro i
    rw [← hdiag' i]
    simp only [Units.val_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hd3 : ∀ i j, d i j ^ 3 = 1 := by
    intro i j
    have h1 : ((P⁻¹ * g i * P : GL (Fin 6) K)) ^ 3 = 1 := by
      have : P⁻¹ * g i * P = P⁻¹ * g i * P⁻¹⁻¹ := by rw [inv_inv]
      rw [this, conj_pow, hg3 i, mul_one, mul_inv_cancel]
    have h2 := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) h1
    simp only [Units.val_pow_eq_pow_val, hdiag' i, Matrix.diagonal_pow, Units.val_one] at h2
    have h3 := congrFun (congrFun h2 j) j
    simpa [Matrix.diagonal_apply_eq] using h3
  have hlog : ∀ i j, ∃ s : ZMod 3, d i j = ζ ^ s.val := by
    intro i j
    obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one (hd3 i j)
    exact ⟨(k : ZMod 3), by rw [ZMod.val_cast_of_lt hk, hk']⟩
  choose v hv using hlog
  obtain ⟨a, b, c, t, habc, hcnt⟩ := exists_plane_four (v 0) (v 1) (v 2)
  have hP : IsUnit (P : Matrix (Fin 6) (Fin 6) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  set e : Fin 6 → K := fun j => d 0 j ^ a.val * d 1 j ^ b.val * d 2 j ^ c.val with he
  have hXP : ((g 0 ^ a.val * g 1 ^ b.val * g 2 ^ c.val : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) * P = (P : Matrix (Fin 6) (Fin 6) K) * diagonal e := by
    have h0 : SemiconjBy (P : Matrix (Fin 6) (Fin 6) K) (diagonal (d 0)) (g 0 : Matrix _ _ K) :=
      hgP 0
    have h1 : SemiconjBy (P : Matrix (Fin 6) (Fin 6) K) (diagonal (d 1)) (g 1 : Matrix _ _ K) :=
      hgP 1
    have h2 : SemiconjBy (P : Matrix (Fin 6) (Fin 6) K) (diagonal (d 2)) (g 2 : Matrix _ _ K) :=
      hgP 2
    have h := ((h0.pow_right a.val).mul_right (h1.pow_right b.val)).mul_right
      (h2.pow_right c.val)
    have hdiagprod : diagonal (d 0) ^ a.val * diagonal (d 1) ^ b.val * diagonal (d 2) ^ c.val =
        diagonal e := by
      simp only [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, he]
      rfl
    rw [hdiagprod] at h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    exact h.symm
  have he' : ∀ j, e j = ζ ^ ((v 0 j).val * a.val + (v 1 j).val * b.val + (v 2 j).val * c.val) := by
    intro j
    simp only [he, hv, ← pow_mul, ← pow_add]
  refine ⟨a.val, b.val, c.val, ?_, ζ ^ t.val, ?_⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := (ZMod.natCast_eq_zero_iff a.val 3).2 h1
    have h2' := (ZMod.natCast_eq_zero_iff b.val 3).2 h2
    have h3' := (ZMod.natCast_eq_zero_iff c.val 3).2 h3
    rw [ZMod.natCast_zmod_val] at h1' h2' h3'
    rcases habc with h | h | h
    · exact h h1'
    · exact h h2'
    · exact h h3'
  · refine le_trans ?_ (card_le_eigenDim _ P hP e hXP (ζ ^ t.val))
    refine le_of_le_of_eq hcnt ?_
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he' j, zeta_pow_eq_iff hζ]
    push_cast
    simp only [ZMod.natCast_zmod_val]
    constructor <;> intro h <;> linear_combination h

theorem three_dvd_eigenDim {K : Type*} [Field K] {n : ℕ} (g₁ g₂ g₃ : GL (Fin n) K) (κ : Kˣ)
    (hκ3 : κ ^ 3 = 1) (hκ1 : κ ≠ 1)
    (hcomm : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) κ)
    (h13 : g₁ * g₃ = g₃ * g₁) (h23 : g₂ * g₃ = g₃ * g₂) (c : K) :
    3 ∣ eigenDim (g₃ : Matrix (Fin n) (Fin n) K) c := by
  set W : Submodule K (Fin n → K) := LinearMap.ker (Matrix.toLin' (g₃ : Matrix (Fin n) (Fin n) K) -
    c • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))) with hW
  have hmem : ∀ w, w ∈ W ↔ (g₃ : Matrix (Fin n) (Fin n) K) *ᵥ w = c • w := by
    intro w
    simp [hW, LinearMap.mem_ker, sub_eq_zero]
  have hinv : ∀ h : GL (Fin n) K, h * g₃ = g₃ * h → ∀ w ∈ W,
      (h : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
    intro h hh w hw
    rw [hmem] at hw ⊢
    have h1 : (g₃ : Matrix (Fin n) (Fin n) K) * (h : Matrix (Fin n) (Fin n) K) =
        (h : Matrix (Fin n) (Fin n) K) * g₃ := by
      have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hh.symm
      simpa only [Units.val_mul] using this
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  set a : W →ₗ[K] W := (Matrix.toLin' (g₁ : Matrix (Fin n) (Fin n) K)).restrict
    (fun w hw => hinv g₁ h13 w hw) with ha
  set b : W →ₗ[K] W := (Matrix.toLin' (g₂ : Matrix (Fin n) (Fin n) K)).restrict
    (fun w hw => hinv g₂ h23 w hw) with hb
  have hscal : ∀ x : Fin n → K, ((Matrix.GeneralLinearGroup.scalar (Fin n) κ : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ x = (κ : K) • x := by
    intro x
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i
    simp [Matrix.mulVec_diagonal]
  have hg12 : g₁ * g₂ = Matrix.GeneralLinearGroup.scalar (Fin n) κ * (g₂ * g₁) := by
    rw [← hcomm]
    group
  have hab : a * b = (κ : K) • (b * a) := by
    ext w : 2
    have h1 := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K))
      hg12
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1
    rw [hscal] at h1
    simp only [Module.End.mul_apply, LinearMap.smul_apply, ha, hb, LinearMap.coe_restrict_apply,
      Matrix.toLin'_apply, Submodule.coe_smul]
    exact h1
  have hinj : ∀ (h : GL (Fin n) K) (hh : ∀ w ∈ W, (h : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W),
      LinearMap.det ((Matrix.toLin' (h : Matrix (Fin n) (Fin n) K)).restrict hh) ≠ 0 := by
    intro h hh
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot']
    intro w hw
    have h0 : (h : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K) = 0 := by
      have := congrArg (fun x : W => (x : Fin n → K)) hw
      exact this
    have h1 : ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        ((h : Matrix (Fin n) (Fin n) K) *ᵥ (w : Fin n → K)) = (w : Fin n → K) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact Subtype.ext h1.symm
  have hda := hinj g₁ (fun w hw => hinv g₁ h13 w hw)
  have hdb := hinj g₂ (fun w hw => hinv g₂ h23 w hw)
  have hdet := congrArg LinearMap.det hab
  rw [Module.End.mul_eq_comp, LinearMap.det_comp, LinearMap.det_smul, Module.End.mul_eq_comp,
    LinearMap.det_comp] at hdet
  have hpow : (κ : K) ^ Module.finrank K W = 1 := by
    have hne : LinearMap.det a * LinearMap.det b ≠ 0 := mul_ne_zero hda hdb
    rw [mul_comm (LinearMap.det b)] at hdet
    exact (mul_eq_right₀ hne).1 hdet.symm
  have hpowU : κ ^ Module.finrank K W = 1 := by
    apply Units.ext
    simpa using hpow
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf κ = 3 := orderOf_eq_prime hκ3 hκ1
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hpowU

end EigenDim

section Groups

open scoped IsMulCommutative

theorem exists_independent_triple_of_elemAbelian {G : Type*} [Group G] (E : Subgroup G) [Finite E]
    [IsMulCommutative E] (hexp : ∀ x ∈ E, x ^ 3 = 1) (h27 : 27 ≤ Nat.card E) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, ∃ e₃ ∈ E, ∀ a b c : ℕ, e₁ ^ a * e₂ ^ b * e₃ ^ c = 1 →
      3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c := by
  have hexpA : ∀ x : Additive E, 3 • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective x
    rw [← ofMul_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using hexp y y.2)
    rw [this]
    rfl
  letI : Module (ZMod 3) (Additive E) := AddCommGroup.zmodModule hexpA
  haveI : Module.Finite (ZMod 3) (Additive E) := Module.Finite.of_finite
  have hcard : Nat.card (Additive E) = 3 ^ Module.finrank (ZMod 3) (Additive E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
  have hrank : 3 ≤ Module.finrank (ZMod 3) (Additive E) := by
    by_contra hlt
    have hle : Module.finrank (ZMod 3) (Additive E) ≤ 2 := by omega
    have : Nat.card (Additive E) ≤ 3 ^ 2 := by
      rw [hcard]; exact Nat.pow_le_pow_right (by norm_num) hle
    have h27' : 27 ≤ Nat.card (Additive E) := by
      simpa [Nat.card_congr (Additive.ofMul : E ≃ Additive E)] using h27
    omega
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hrank
  rw [Fintype.linearIndependent_iff] at hf
  refine ⟨((Additive.toMul (f 0) : E) : G), (Additive.toMul (f 0)).2,
    ((Additive.toMul (f 1) : E) : G), (Additive.toMul (f 1)).2,
    ((Additive.toMul (f 2) : E) : G), (Additive.toMul (f 2)).2, ?_⟩
  intro a b c habc
  have h1 : (Additive.toMul (f 0)) ^ a * (Additive.toMul (f 1)) ^ b * (Additive.toMul (f 2)) ^ c
      = 1 := by
    apply Subtype.ext
    simpa using habc
  have h2 : a • f 0 + b • f 1 + c • f 2 = 0 := by
    apply Additive.toMul.injective
    simpa [toMul_add, toMul_nsmul] using h1
  have h3 := hf ![(a : ZMod 3), (b : ZMod 3), (c : ZMod 3)] (by
    simpa [Fin.sum_univ_three, Nat.cast_smul_eq_nsmul] using h2)
  refine ⟨?_, ?_, ?_⟩
  · exact (ZMod.natCast_eq_zero_iff a 3).1 (by simpa using h3 0)
  · exact (ZMod.natCast_eq_zero_iff b 3).1 (by simpa using h3 1)
  · exact (ZMod.natCast_eq_zero_iff c 3).1 (by simpa using h3 2)

theorem exists_commuting_not_mem {Γ : Type*} [Group Γ] [Finite Γ] (T H : Subgroup Γ)
    (hTc : T ≤ Subgroup.center Γ) (hT3 : Nat.card T ≤ 3)
    (hH : 27 * Nat.card T ≤ Nat.card H) (g₁ g₂ : Γ)
    (h1 : ∀ x ∈ H, ⁅x, g₁⁆ ∈ T) (h2 : ∀ x ∈ H, ⁅x, g₂⁆ ∈ T) :
    ∃ y ∈ H, y ∉ T ∧ y * g₁ = g₁ * y ∧ y * g₂ = g₂ * y := by
  have hcomm : ∀ g : Γ, (∀ x ∈ H, ⁅x, g⁆ ∈ T) →
      ∃ φ : H →* T, ∀ x : H, (φ x : Γ) = ⁅(x : Γ), g⁆ := by
    intro g hg
    refine ⟨MonoidHom.mk' (fun x => ⟨⁅(x : Γ), g⁆, hg x x.2⟩) ?_, fun x => rfl⟩
    intro x y
    apply Subtype.ext
    have hy : ⁅(y : Γ), g⁆ ∈ Subgroup.center Γ := hTc (hg y y.2)
    have hx : ⁅(x : Γ), g⁆ ∈ Subgroup.center Γ := hTc (hg x x.2)
    have e : ⁅(x : Γ) * y, g⁆ = (x : Γ) * ⁅(y : Γ), g⁆ * (x : Γ)⁻¹ * ⁅(x : Γ), g⁆ := by
      simp only [commutatorElement_def]; group
    have hxy : (x : Γ) * ⁅(y : Γ), g⁆ * (x : Γ)⁻¹ = ⁅(y : Γ), g⁆ := by
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_center_iff.1 hy (x : Γ)
    show ⁅(x : Γ) * y, g⁆ = ⁅(x : Γ), g⁆ * ⁅(y : Γ), g⁆
    rw [e, hxy]
    exact Subgroup.mem_center_iff.1 hx ⁅(y : Γ), g⁆
  obtain ⟨φ₁, hφ₁⟩ := hcomm g₁ h1
  obtain ⟨φ₂, hφ₂⟩ := hcomm g₂ h2
  by_contra hno
  have hker : ∀ x : H, x ∈ (φ₁.prod φ₂).ker → (x : Γ) ∈ T := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hx
    have e1 : ⁅(x : Γ), g₁⁆ = 1 := by rw [← hφ₁]; exact congrArg Subtype.val hx.1
    have e2 : ⁅(x : Γ), g₂⁆ = 1 := by rw [← hφ₂]; exact congrArg Subtype.val hx.2
    by_contra hxT
    apply hno
    refine ⟨x, x.2, hxT, ?_, ?_⟩
    · exact commutatorElement_eq_one_iff_mul_comm.1 e1
    · exact commutatorElement_eq_one_iff_mul_comm.1 e2
  have hkT : Nat.card (φ₁.prod φ₂).ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : Γ), hker x.1 x.2⟩) ?_
    intro x y hxy
    have h' := congrArg (fun z : T => (z : Γ)) hxy
    exact Subtype.ext (Subtype.ext h')
  have hcard := Subgroup.card_ker_mul_card_range (φ₁.prod φ₂)
  have hr : Nat.card (φ₁.prod φ₂).range ≤ Nat.card T * Nat.card T := by
    calc Nat.card (φ₁.prod φ₂).range ≤ Nat.card (T × T) := Subgroup.card_le_card_group _
      _ = Nat.card T * Nat.card T := Nat.card_prod _ _
  have hpos : 0 < Nat.card T := Nat.card_pos
  have : Nat.card H ≤ Nat.card T * (Nat.card T * Nat.card T) := by
    rw [← hcard]; exact Nat.mul_le_mul hkT hr
  nlinarith

end Groups

section SU6

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj

variable {K0 : Type} [Field K0]

theorem cube_eq_one_of_scalar_mem_statedSU (h : UnitaryFieldData 2 3 K0) {c : K0ˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ StatedSU 6 (2 ^ 3) K0) : c ^ 3 = 1 := by
  obtain ⟨h6, h9⟩ := ((CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq
    (by norm_num : 1 ≤ 6)).2.1 c).1 hc
  have h9' : c ^ 9 = c ^ 6 * c ^ 3 := by rw [← pow_add]
  rw [h6, one_mul] at h9'
  rw [← h9']
  exact h9

theorem exists_scalar_of_projH_eq_one (h : UnitaryFieldData 2 3 K0) {x : StatedSU 6 (2 ^ 3) K0}
    (hx : projH (StatedSU 6 (2 ^ 3) K0) x = 1) :
    ∃ c : K0ˣ, c ^ 3 = 1 ∧
      (x : GL (Fin 6) K0) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  have hx' : x ∈ (StatedScalars (Fin 6) K0).subgroupOf (StatedSU 6 (2 ^ 3) K0) :=
    (QuotientGroup.eq_one_iff x).1 hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx'
  exact ⟨c, cube_eq_one_of_scalar_mem_statedSU h (hc ▸ x.2), hc.symm⟩

theorem exists_cube_of_pow_three_eq_one_of_card_eq_64 {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 64) {μ : Kˣ} (hμ : μ ^ 3 = 1) : ∃ l : Kˣ, l ^ 3 = μ := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = 63 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_units, hK]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hγ μ)
  have h3 : γ ^ (k * 3) = 1 := by
    rw [_root_.zpow_mul, hk]
    exact_mod_cast hμ
  have hdvd : ((orderOf γ : ℕ) : ℤ) ∣ k * 3 := (orderOf_dvd_iff_zpow_eq_one).2 h3
  rw [hord] at hdvd
  obtain ⟨m, hm⟩ : (21 : ℤ) ∣ k := by omega
  refine ⟨γ ^ (7 * m), ?_⟩
  rw [← zpow_natCast, ← _root_.zpow_mul, ← hk]
  congr 1
  push_cast
  omega

theorem scalar_mem_uU_of_pow_nine_eq_one (h : UnitaryFieldData 2 3 K0) {c : K0ˣ} (hc : c ^ 9 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈ uU h 6 := by
  rw [mem_uU]
  have h1 : h.bar (c : K0) * (c : K0) = 1 := by
    rw [h.bar_apply, ← pow_succ]
    simpa using congrArg Units.val hc
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.transpose_apply,
    Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply, Units.val_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp [h1]
  · simp [hij, Ne.symm hij]

theorem val_scalar_mul_eq_smul {n : ℕ} (s : K0ˣ) (X : GL (Fin n) K0) :
    ((Matrix.GeneralLinearGroup.scalar (Fin n) s * X : GL (Fin n) K0) : Matrix (Fin n) (Fin n) K0) =
      (s : K0) • (X : Matrix (Fin n) (Fin n) K0) := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]

theorem exists_pow_mul_eigenDim_ge_four_of_commute (h : UnitaryFieldData 2 3 K0)
    (g : Fin 3 → StatedSU 6 (2 ^ 3) K0) (hcomm : ∀ i j, g i * g j = g j * g i)
    (hz : ∀ i, projH (StatedSU 6 (2 ^ 3) K0) (g i) ^ 3 = 1) :
    ∃ a b c : ℕ, ¬ (3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c) ∧ ∃ t : K0,
      4 ≤ eigenDim (((g 0 ^ a * g 1 ^ b * g 2 ^ c : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) :
        Matrix (Fin 6) (Fin 6) K0) t := by
  classical
  haveI := h.finite
  have hK : Nat.card K0 = 64 := by simpa using h.card
  have hscal : ∀ i, ∃ l : K0ˣ, l ^ 9 = 1 ∧
      ((g i : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (l ^ 3) := by
    intro i
    have h1 : projH (StatedSU 6 (2 ^ 3) K0) (g i ^ 3) = 1 := by rw [map_pow]; exact hz i
    obtain ⟨μ, hμ3, hμ⟩ := exists_scalar_of_projH_eq_one h h1
    obtain ⟨l, hl⟩ := exists_cube_of_pow_three_eq_one_of_card_eq_64 hK hμ3
    refine ⟨l, ?_, ?_⟩
    · calc l ^ 9 = (l ^ 3) ^ 3 := by rw [← pow_mul]
        _ = 1 := by rw [hl]; exact hμ3
    · rw [hl, ← hμ]
      rfl
  choose l hl9 hl3 using hscal
  set g' : Fin 3 → GL (Fin 6) K0 := fun i =>
    Matrix.GeneralLinearGroup.scalar (Fin 6) (l i)⁻¹ * (g i : GL (Fin 6) K0) with hg'
  have hgg' : ∀ i, (g i : GL (Fin 6) K0) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) (l i) * g' i := by
    intro i
    simp only [hg', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hg'3 : ∀ i, g' i ^ 3 = 1 := by
    intro i
    have hc : Commute (Matrix.GeneralLinearGroup.scalar (Fin 6) (l i)⁻¹) (g i : GL (Fin 6) K0) :=
      (commute_scalar _ _).symm
    simp only [hg']
    rw [hc.mul_pow, hl3 i, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hg'U : ∀ i, g' i ∈ uU h 6 := by
    intro i
    refine mul_mem (scalar_mem_uU_of_pow_nine_eq_one h ?_) (statedSU_le_uU h (g i).2)
    rw [inv_pow, hl9 i, inv_one]
  have hg'c : ∀ i j, g' i * g' j = g' j * g' i := by
    intro i j
    have hij : (g i : GL (Fin 6) K0) * (g j : GL (Fin 6) K0) =
        (g j : GL (Fin 6) K0) * (g i : GL (Fin 6) K0) := by
      have := congrArg (fun x : StatedSU 6 (2 ^ 3) K0 => (x : GL (Fin 6) K0)) (hcomm i j)
      simpa only [Subgroup.coe_mul] using this
    have hs : ∀ (a b : K0ˣ) (x y : GL (Fin 6) K0), x * y = y * x →
        (Matrix.GeneralLinearGroup.scalar (Fin 6) a * x) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) b * y) =
        (Matrix.GeneralLinearGroup.scalar (Fin 6) b * y) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) a * x) := by
      intro a b x y hxy
      rw [Commute.mul_mul_mul_comm (commute_scalar b x),
        Commute.mul_mul_mul_comm (commute_scalar a y), hxy,
        (commute_scalar b (Matrix.GeneralLinearGroup.scalar (Fin 6) a)).eq]
    exact hs _ _ _ _ hij
  obtain ⟨ω, hω3, hω1, -⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_cube_root_bar
    h (by norm_num : 3 ∣ 2 ^ 3 + 1)
  have hζ : IsPrimitiveRoot ω 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    exact hord ▸ IsPrimitiveRoot.orderOf ω
  obtain ⟨P, -, hPd⟩ := CFSG.HardMathSupport.Dickson.Bal207.FirstClaim.exists_unitary_isDiag_conj
    h (by norm_num : 3 ∣ 2 ^ 3 + 1) (Set.range g')
    (by rintro _ ⟨i, rfl⟩; exact hg'U i)
    (by rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact hg'c i j)
    (by rintro _ ⟨i, rfl⟩; exact hg'3 i)
  obtain ⟨a, b, c, hnd, t, ht⟩ :=
    exists_pow_mul_eigenDim_ge_four hζ g' P hg'3 (fun i => hPd _ ⟨i, rfl⟩)
  refine ⟨a, b, c, hnd, ((l 0 ^ a * l 1 ^ b * l 2 ^ c : K0ˣ) : K0) * t, ?_⟩
  have hmat : ∀ i, ((g i : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) =
      ((l i : K0ˣ) : K0) • ((g' i : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
    intro i
    rw [← val_scalar_mul_eq_smul, ← hgg' i]
  have hG : (((g 0 ^ a * g 1 ^ b * g 2 ^ c : StatedSU 6 (2 ^ 3) K0) : GL (Fin 6) K0) :
      Matrix (Fin 6) (Fin 6) K0) =
      ((l 0 ^ a * l 1 ^ b * l 2 ^ c : K0ˣ) : K0) •
        ((g' 0 ^ a * g' 1 ^ b * g' 2 ^ c : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [hmat 0, hmat 1, hmat 2]
    simp only [smul_pow, smul_mul_smul_comm, smul_smul]
  rw [hG, eigenDim_smul _ (Units.ne_zero _)]
  exact ht

theorem exists_toral_good (h : UnitaryFieldData 2 3 K0)
    (E : Subgroup (StatedProj (StatedSU 6 (2 ^ 3) K0))) (hE : CFSG.Open.IsElemAbelian 3 E)
    (h27 : 27 ≤ Nat.card E)
    (hcomm : ∀ g₁ g₂ : StatedSU 6 (2 ^ 3) K0, projH _ g₁ ∈ E → projH _ g₂ ∈ E →
      g₁ * g₂ = g₂ * g₁) :
    ∃ g : StatedSU 6 (2 ^ 3) K0, projH _ g ∈ E ∧ projH _ g ≠ 1 ∧ ∃ t : K0,
      4 ≤ eigenDim ((g : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) t := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K0) := Finite.of_injective
    (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0)) Units.val_injective
  haveI : IsMulCommutative E := hE.1
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, hind⟩ := exists_independent_triple_of_elemAbelian E hE.2 h27
  obtain ⟨g₁, hg₁⟩ := projH_surjective (H := StatedSU 6 (2 ^ 3) K0) e₁
  obtain ⟨g₂, hg₂⟩ := projH_surjective (H := StatedSU 6 (2 ^ 3) K0) e₂
  obtain ⟨g₃, hg₃⟩ := projH_surjective (H := StatedSU 6 (2 ^ 3) K0) e₃
  subst hg₁ hg₂ hg₃
  have hm : ∀ i, projH (StatedSU 6 (2 ^ 3) K0) (![g₁, g₂, g₃] i) ∈ E := by
    intro i
    fin_cases i
    · exact he₁
    · exact he₂
    · exact he₃
  obtain ⟨a, b, c, hnd, t, ht⟩ := exists_pow_mul_eigenDim_ge_four_of_commute h ![g₁, g₂, g₃]
    (fun i j => hcomm _ _ (hm i) (hm j))
    (fun i => hE.2 _ (hm i))
  refine ⟨g₁ ^ a * g₂ ^ b * g₃ ^ c, ?_, ?_, t, ht⟩
  · simp only [map_mul, map_pow]
    exact mul_mem (mul_mem (pow_mem he₁ a) (pow_mem he₂ b)) (pow_mem he₃ c)
  · intro h1
    apply hnd
    apply hind a b c
    simpa only [map_mul, map_pow] using h1

theorem exists_heis_triple (h : UnitaryFieldData 2 3 K0)
    (E : Subgroup (StatedProj (StatedSU 6 (2 ^ 3) K0))) (hE : CFSG.Open.IsElemAbelian 3 E)
    (h27 : 27 ≤ Nat.card E)
    (hnc : ¬ ∀ g₁ g₂ : StatedSU 6 (2 ^ 3) K0, projH _ g₁ ∈ E → projH _ g₂ ∈ E →
      g₁ * g₂ = g₂ * g₁) :
    ∃ g₁ g₂ g₃ : StatedSU 6 (2 ^ 3) K0, projH _ g₁ ∈ E ∧ projH _ g₂ ∈ E ∧ projH _ g₃ ∈ E ∧
      projH _ g₃ ≠ 1 ∧
      (∃ κ : K0ˣ, κ ≠ 1 ∧ (g₁ : GL (Fin 6) K0) * g₂ * (g₁ : GL (Fin 6) K0)⁻¹ *
        (g₂ : GL (Fin 6) K0)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ) ∧
      (g₁ : GL (Fin 6) K0) * g₃ = g₃ * g₁ ∧ (g₂ : GL (Fin 6) K0) * g₃ = g₃ * g₂ ∧
      ∀ c : K0, 3 ∣ eigenDim ((g₃ : GL (Fin 6) K0) : Matrix (Fin 6) (Fin 6) K0) c := by
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K0) := Finite.of_injective
    (fun g : GL (Fin 6) K0 => (g : Matrix (Fin 6) (Fin 6) K0)) Units.val_injective
  haveI : IsMulCommutative E := hE.1
  obtain ⟨g₁, g₂, h1, h2, hne⟩ : ∃ g₁ g₂ : StatedSU 6 (2 ^ 3) K0, projH _ g₁ ∈ E ∧
      projH _ g₂ ∈ E ∧ g₁ * g₂ ≠ g₂ * g₁ := by
    by_contra hcon
    apply hnc
    intro g₁ g₂ h1 h2
    by_contra hne
    exact hcon ⟨g₁, g₂, h1, h2, hne⟩
  set π := projH (StatedSU 6 (2 ^ 3) K0) with hπ
  set Z : Subgroup (StatedSU 6 (2 ^ 3) K0) :=
    (StatedScalars (Fin 6) K0).subgroupOf (StatedSU 6 (2 ^ 3) K0) with hZ
  set H : Subgroup (StatedSU 6 (2 ^ 3) K0) := E.comap π with hH
  have hker : π.ker = Z := QuotientGroup.ker_mk' _
  have hZmem : ∀ x : StatedSU 6 (2 ^ 3) K0, x ∈ Z ↔ π x = 1 := fun x => by
    rw [← hker, MonoidHom.mem_ker]
  have hZcenter : Z ≤ Subgroup.center (StatedSU 6 (2 ^ 3) K0) := scalars_subgroupOf_le_center
  have hZcard : Nat.card Z = 3 := by
    have := (CFSG.LinearGroups.unitary_scalar_kernel h.prime h.card_eq_sq
      (by norm_num : 1 ≤ 6)).2.2
    rw [this]
    norm_num
  have hcomm : ∀ x y : StatedSU 6 (2 ^ 3) K0, x ∈ H → π y ∈ E → ⁅x, y⁆ ∈ Z := by
    intro x y hx hy
    rw [hZmem, map_commutatorElement]
    have hx' : π x ∈ E := hx
    have : π x * π y = π y * π x := by
      have := mul_comm' (⟨π x, hx'⟩ : E) ⟨π y, hy⟩
      exact congrArg Subtype.val this
    exact commutatorElement_eq_one_iff_mul_comm.2 this
  have hHcard : 27 * Nat.card Z ≤ Nat.card H := by
    set ψ : H →* StatedProj (StatedSU 6 (2 ^ 3) K0) := π.comp H.subtype with hψ
    have hrange : ψ.range = E := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype, hH]
      exact Subgroup.map_comap_eq_self_of_surjective (projH_surjective) E
    have hkerψ : Nat.card Z ≤ Nat.card ψ.ker := by
      refine Nat.card_le_card_of_injective
        (fun z : Z => (⟨⟨(z : StatedSU 6 (2 ^ 3) K0), ?_⟩, ?_⟩ : ψ.ker)) ?_
      · show π z ∈ E
        rw [(hZmem z).1 z.2]
        exact E.one_mem
      · rw [MonoidHom.mem_ker]
        exact (hZmem z).1 z.2
      · intro x y hxy
        have := congrArg (fun w : ψ.ker => ((w : H) : StatedSU 6 (2 ^ 3) K0)) hxy
        exact Subtype.ext this
    have hcard := Subgroup.card_ker_mul_card_range ψ
    rw [hrange] at hcard
    calc 27 * Nat.card Z ≤ Nat.card E * Nat.card Z := Nat.mul_le_mul_right _ h27
      _ ≤ Nat.card E * Nat.card ψ.ker := Nat.mul_le_mul_left _ hkerψ
      _ = Nat.card H := by rw [← hcard]; ring
  obtain ⟨g₃, hg₃H, hg₃Z, hc1, hc2⟩ := exists_commuting_not_mem Z H hZcenter
    (by rw [hZcard]) hHcard g₁ g₂ (fun x hx => hcomm x g₁ hx h1) (fun x hx => hcomm x g₂ hx h2)
  have hg₃E : π g₃ ∈ E := hg₃H
  have hg₃1 : π g₃ ≠ 1 := fun h' => hg₃Z ((hZmem g₃).2 h')
  have hg₁H : g₁ ∈ H := h1
  obtain ⟨κ, hκ3, hκ⟩ := exists_scalar_of_projH_eq_one h ((hZmem _).1 (hcomm g₁ g₂ hg₁H h2))
  have hκ' : (g₁ : GL (Fin 6) K0) * g₂ * (g₁ : GL (Fin 6) K0)⁻¹ * (g₂ : GL (Fin 6) K0)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 6) κ := by
    rw [← hκ]
    simp [commutatorElement_def]
  have hκ1 : κ ≠ 1 := by
    rintro rfl
    apply hne
    rw [map_one] at hκ'
    have h12 : (g₁ : GL (Fin 6) K0) * g₂ = (g₂ : GL (Fin 6) K0) * g₁ := by
      have := commutatorElement_eq_one_iff_mul_comm.1
        (show ⁅(g₁ : GL (Fin 6) K0), (g₂ : GL (Fin 6) K0)⁆ = 1 by
          simpa [commutatorElement_def] using hκ')
      exact this
    exact Subtype.ext h12
  have h13 : (g₁ : GL (Fin 6) K0) * g₃ = g₃ * g₁ :=
    (congrArg (fun x : StatedSU 6 (2 ^ 3) K0 => (x : GL (Fin 6) K0)) hc1).symm
  have h23 : (g₂ : GL (Fin 6) K0) * g₃ = g₃ * g₂ :=
    (congrArg (fun x : StatedSU 6 (2 ^ 3) K0 => (x : GL (Fin 6) K0)) hc2).symm
  exact ⟨g₁, g₂, g₃, h1, h2, hg₃E, hg₃1, ⟨κ, hκ1, hκ'⟩, h13, h23,
    fun c => three_dvd_eigenDim _ _ _ κ hκ3 hκ1 hκ' h13 h23 c⟩

end SU6

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
