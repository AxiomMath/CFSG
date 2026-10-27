module

public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylowInner
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphSymm

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

section ConjOp

variable (h : UnitaryFieldData p f K)

@[expose] noncomputable def conjOp (A : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    (HypIndex r ε → K) →ₛₗ[h.bar] (HypIndex r ε → K) where
  toFun v := A *ᵥ fun a => h.bar (v a)
  map_add' v w := by
    rw [← mulVec_add]
    congr 1
    funext a
    simp
  map_smul' c v := by
    rw [← mulVec_smul]
    congr 1
    funext a
    simp

theorem conjOp_apply (A : Matrix (HypIndex r ε) (HypIndex r ε) K) (v : HypIndex r ε → K) :
    conjOp h A v = A *ᵥ fun a => h.bar (v a) :=
  rfl

variable {h}

theorem conjOp_conjOp {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : K}
    (hAA : A * A.map h.bar = c • 1) (v : HypIndex r ε → K) :
    conjOp h A (conjOp h A v) = c • v := by
  have hbar : (fun a => h.bar ((A *ᵥ fun a => h.bar (v a)) a)) = A.map h.bar *ᵥ v := by
    funext a
    rw [RingHom.map_mulVec]
    simp only [Function.comp_def, h.bar_bar]
  rw [conjOp_apply, conjOp_apply, hbar, mulVec_mulVec, hAA, smul_mulVec, one_mulVec]

theorem hypForm_conjOp {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (v w : HypIndex r ε → K) :
    hypForm h r ε (conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v)
      (conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) w) = h.bar (hypForm h r ε v w) := by
  rw [conjOp_apply, conjOp_apply, gramForm_mulVec, mem_hypUnitary.mp hA, hypForm_apply,
    hypForm_apply, map_sum]
  simp [h.bar_bar]

theorem conjOp_bijective {A : Matrix (HypIndex r ε) (HypIndex r ε) K} {c : K} (hc : c ≠ 0)
    (hAA : A * A.map h.bar = c • 1) : Function.Bijective (conjOp h A) := by
  refine ⟨fun v w hvw => ?_, fun v => ⟨conjOp h A (c⁻¹ • v), ?_⟩⟩
  · have h1 := congrArg (conjOp h A) hvw
    rw [conjOp_conjOp hAA, conjOp_conjOp hAA] at h1
    exact smul_right_injective _ hc h1
  · rw [conjOp_conjOp hAA, smul_smul, mul_inv_cancel₀ hc, one_smul]

end ConjOp

section Comm

theorem exists_comm_conj_of_cols (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) {c : K} (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (v : κ → HypIndex r ε → K) {b : K}
    (hv : ∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (v i a)) =
      b⁻¹ • v i)
    {Gi : Matrix κ κ K}
    (hGi : Gi * (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) = 1)
    (hGi' : (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) * Gi = 1)
    (hGbar : (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v).map h.bar =
      c • (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v))
    {H : Type*} [Group H] (Y : H →* Matrix κ κ K) (hYbar : ∀ x, (Y x).map h.bar = Y x)
    (hY : ∀ x, ((Y x).map h.bar)ᵀ * (((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v) * Y x =
      ((colMat v).map h.bar)ᵀ * hypGram r ε K * colMat v)
    (hYd : ∀ x, (Y x).det = 1) {x₀ : H} (hx₀ : ∀ c' : K, Y x₀ ≠ c' • 1) :
    ∃ ψ : H →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c' : K, ((ψ x₀ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) ≠
        c' • 1 := by
  set E := colMat v with hE
  obtain ⟨ψ, hψ⟩ := exists_hypSU_hom h hGi hGi' Y hY hYd
  have hFE : Gi * (E.map h.bar)ᵀ * hypGram r ε K * E = 1 := by
    rw [← hGi]
    simp only [Matrix.mul_assoc]
  have hAE : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) * E.map h.bar =
      E * (b⁻¹ • (1 : Matrix κ κ K)) := by
    rw [hE, map_colMat, mul_colMat, colMat_mul_smul_one]
    congr 1
    funext i
    exact hv i
  have hD : (b⁻¹ • (1 : Matrix κ κ K))ᵀ * ((E.map h.bar)ᵀ * hypGram r ε K * E).map h.bar =
      c • (((E.map h.bar)ᵀ * hypGram r ε K * E) * (b⁻¹ • (1 : Matrix κ κ K))) := by
    rw [hGbar, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_comm]
  have hFA := suppF_mul_of_semilinear h.bar_bar hc (hypGram_map h.bar) (mem_hypUnitary.mp hA)
    hAA hAE hD hGi hGi'
  refine ⟨ψ, fun x => ?_, fun c' hc' => ?_⟩
  · rw [hψ, suppMat_map]
    refine mul_suppMat hAE hFA ?_
    rw [hYbar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · rw [hψ] at hc'
    exact hx₀ c' (eq_smul_one_of_suppMat hFE hc')

end Comm

section Tern

variable (h : UnitaryFieldData p f K)

theorem ringChar_fixedField_ne_two (hp : p ≠ 2) : ringChar h.fixedField ≠ 2 := by
  intro h2
  have h3 : ((2 : ℕ) : h.fixedField) = 0 := (ringChar.spec h.fixedField 2).mpr (by rw [h2])
  have h4 : ((2 : ℕ) : K) = 0 := by
    rw [← map_natCast h.fixedField.subtype 2, h3, map_zero]
  exact two_ne_zero_of_odd h hp (by exact_mod_cast h4)

theorem exists_ternHom (hp : p ≠ 2) (d : Fin 3 → h.fixedField) (hd : ∀ i, d i ≠ 0) :
    ∃ Y : SpecialLinearGroup (Fin 2) h.fixedField →* Matrix (Fin 3) (Fin 3) K,
      (∀ x, (Y x).map h.bar = Y x) ∧
      (∀ x, (Y x)ᵀ * diagonal (fun i => (d i : K)) * Y x = diagonal fun i => (d i : K)) ∧
      (∀ x, (Y x).det = 1) ∧
      ∀ c : K, Y (QuaternionMatrices.slQuatI h.fixedField) ≠ c • 1 := by
  have := h.finite
  obtain ⟨ζ, hζ, hζs⟩ :=
    LinearFlag.exists_ternary_isometry_hom (ringChar_fixedField_ne_two h hp) d hd
  set ι : h.fixedField →+* K := h.fixedField.subtype with hι
  have hdet2 : ∀ x, ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).det ^ 2
      = 1 := fun x => by
    have h1 := congrArg det (hζ x)
    rw [det_mul, det_mul, det_transpose] at h1
    have hD0 : (diagonal d).det ≠ 0 := by
      rw [det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
    have h2 : ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).det ^ 2 *
        (diagonal d).det = 1 * (diagonal d).det := by
      linear_combination h1
    exact mul_right_cancel₀ hD0 h2
  set ζ' : SpecialLinearGroup (Fin 2) h.fixedField →* Matrix (Fin 3) (Fin 3) h.fixedField :=
    { toFun := fun x => ((ζ x : GL (Fin 3) h.fixedField) :
          Matrix (Fin 3) (Fin 3) h.fixedField).det •
        ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, Units.val_mul, det_mul]
        rw [smul_mul_smul_comm] } with hζ'
  have hζ'x : ∀ x, ζ' x = ((ζ x : GL (Fin 3) h.fixedField) :
      Matrix (Fin 3) (Fin 3) h.fixedField).det •
      ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) := fun _ => rfl
  refine ⟨(RingHom.mapMatrix ι).toMonoidHom.comp ζ', fun x => ?_, fun x => ?_, fun x => ?_,
    fun c hc => ?_⟩
  · ext i j
    exact h.mem_fixedField.mp ((ζ' x) i j).2
  · have h1 : (diagonal fun i => (d i : K)) = (diagonal d).map ι := by
      rw [diagonal_map (map_zero ι)]
      rfl
    change ((ζ' x).map ι)ᵀ * diagonal (fun i => (d i : K)) * (ζ' x).map ι = _
    rw [h1, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hζ'x, transpose_smul,
      Matrix.smul_mul, smul_mul_smul_comm, hζ x, ← sq, hdet2, one_smul]
  · change ((ζ' x).map ι).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hζ'x, det_smul, Fintype.card_fin,
      show ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).det ^ 3 *
        ((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).det =
        (((ζ x : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField).det ^ 2) ^ 2 by
          ring, hdet2, one_pow, map_one]
  · change (ζ' (QuaternionMatrices.slQuatI h.fixedField)).map ι = c • 1 at hc
    set q := QuaternionMatrices.slQuatI h.fixedField
    set Z := ((ζ q : GL (Fin 3) h.fixedField) : Matrix (Fin 3) (Fin 3) h.fixedField) with hZ
    have hZ0 : Z.det ≠ 0 := fun h0 => by
      have := hdet2 q
      rw [← hZ, h0] at this
      simp at this
    have h00 : ι ((ζ' q) 0 0) = c := by
      have := congrFun (congrFun hc 0) 0
      simpa using this
    have hζq : ζ' q = (ζ' q) 0 0 • (1 : Matrix (Fin 3) (Fin 3) h.fixedField) := by
      ext i j
      have hij := congrFun (congrFun hc i) j
      change ι ((ζ' q) i j) = (c • (1 : Matrix (Fin 3) (Fin 3) K)) i j at hij
      change ι ((ζ' q) i j) = ι (((ζ' q) 0 0 • (1 : Matrix (Fin 3) (Fin 3) h.fixedField)) i j)
      rw [hij, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, h00,
        one_apply, one_apply]
      split_ifs <;> simp
    obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ = (ζ' q) 0 0 := ⟨_, rfl⟩
    rw [← hs₀] at hζq
    obtain ⟨z, hz⟩ : ∃ z, z = Z.det := ⟨_, rfl⟩
    rw [← hz] at hZ0
    apply hζs (z⁻¹ * s₀)
    calc Z = z⁻¹ • ζ' q := by rw [hζ'x, ← hZ, ← hz, smul_smul, inv_mul_cancel₀ hZ0, one_smul]
      _ = scalar (Fin 3) (z⁻¹ * s₀) := by
        rw [hζq, smul_smul, scalar_apply, smul_one_eq_diagonal]

end Tern

section Forms

theorem exists_comm_conj_of_alt_pair (h : UnitaryFieldData p f K) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = (-1 : K) • 1)
    {w₁ w₂ : HypIndex r ε → K} {b : K}
    (hw₁ : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w₁ a)) = b⁻¹ • w₁)
    (hw₂ : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w₂ a)) = b⁻¹ • w₂)
    {g : K} (hg0 : g ≠ 0) (hgbar : h.bar g = -g) (h11 : hypForm h r ε w₁ w₁ = 0)
    (h22 : hypForm h r ε w₂ w₂ = 0) (h12 : hypForm h r ε w₁ w₂ = g)
    (h21 : hypForm h r ε w₂ w₁ = -g) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c' : K, ((ψ (QuaternionMatrices.slQuatI h.fixedField) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c' • 1 := by
  have hG : ((colMat ![w₁, w₂]).map h.bar)ᵀ * hypGram r ε K * colMat ![w₁, w₂] =
      g • QuaternionMatrices.quatI K := by
    rw [gram_colMat_eq_hypForm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuaternionMatrices.quatI, h11, h22, h12, h21]
  refine exists_comm_conj_of_cols h hA (neg_ne_zero.mpr one_ne_zero) hAA ![w₁, w₂] (b := b) ?_
    (Gi := -g⁻¹ • QuaternionMatrices.quatI K) ?_ ?_ ?_ (planeHom h) (map_planeHom h) ?_
    (det_planeHom h) (x₀ := QuaternionMatrices.slQuatI h.fixedField) ?_
  · intro i
    fin_cases i
    · exact hw₁
    · exact hw₂
  · rw [hG, smul_mul_smul_comm, QuaternionMatrices.quatI_mul_self, neg_mul,
      inv_mul_cancel₀ hg0, neg_smul, one_smul, neg_neg]
  · rw [hG, smul_mul_smul_comm, QuaternionMatrices.quatI_mul_self, mul_neg,
      mul_inv_cancel₀ hg0, neg_smul, one_smul, neg_neg]
  · rw [hG, Matrix.map_smul' _ _ _ (map_mul h.bar), hgbar]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [QuaternionMatrices.quatI]
  · intro x
    rw [hG]
    exact planeHom_isometry h g x
  · intro c' hc'
    rw [planeHom_slQuatI] at hc'
    exact quatI_ne_smul_one c' hc'

theorem exists_comm_conj_of_orth_triple (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = (1 : K) • 1)
    {w : Fin 3 → HypIndex r ε → K} {b : K}
    (hw : ∀ i, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w i a)) =
      b⁻¹ • w i)
    (d : Fin 3 → h.fixedField) (hd : ∀ i, d i ≠ 0)
    (hww : ∀ i j, hypForm h r ε (w i) (w j) = if i = j then (d i : K) else 0) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c' : K, ((ψ (QuaternionMatrices.slQuatI h.fixedField) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c' • 1 := by
  have hG : ((colMat w).map h.bar)ᵀ * hypGram r ε K * colMat w = diagonal fun i => (d i : K) := by
    rw [gram_colMat_eq_hypForm]
    ext i j
    rw [of_apply, diagonal_apply, hww]
  have hd0' : ∀ i, (d i : K) ≠ 0 := fun i h0 => hd i (Subtype.ext h0)
  obtain ⟨Y, hYbar, hYiso, hYd, hYs⟩ := exists_ternHom h hp d hd
  refine exists_comm_conj_of_cols h hA one_ne_zero hAA w hw
    (Gi := diagonal fun i => (d i : K)⁻¹) ?_ ?_ ?_ Y hYbar ?_ hYd hYs
  · rw [hG, diagonal_mul_diagonal]
    simp [inv_mul_cancel₀ (hd0' _)]
  · rw [hG, diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ (hd0' _)]
  · rw [hG, one_smul, diagonal_map (map_zero _)]
    simp [h.mem_fixedField.mp (d _).2]
  · intro x
    rw [hYbar, hG, hYiso]

end Forms

section Bar

theorem exists_comm_conj_of_bar (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (hn : 4 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) {c : K}
    (hc : c ≠ 0)
    (hAA : (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar = c • 1) :
    ∃ ψ : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
      (∀ x, (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *
        ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar =
          ((ψ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
            (A : Matrix (HypIndex r ε) (HypIndex r ε) K)) ∧
      ∀ c' : K, ((ψ (QuaternionMatrices.slQuatI h.fixedField) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) ≠ c' • 1 := by
  have := h.finite
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have hn1 : 1 ≤ finrank K (HypIndex r ε → K) := by
    rw [finrank_hypIndex_fun]
    omega
  have hμ : ∀ v, conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K) v) =
        ((Units.mk0 c hc : Kˣ) : K) • v := conjOp_conjOp hAA
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd hn1 (hypForm_isSymm h) (hypForm_separatingLeft h) _ (conjOp_bijective hc hAA)
    (hypForm_conjOp hA) (Units.mk0 c hc) hμ
  obtain ⟨-, hfin, -, hsym, halt⟩ := hall b t hb ht
  rw [finrank_hypIndex_fun] at hfin
  have hfix : ∀ w ∈ conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K)),
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ (fun a => h.bar (w a)) =
        ((b : K))⁻¹ • w := fun w hw => by
    have h1 : (b : K) • ((A : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        fun a => h.bar (w a)) = w := mem_conjFixed.mp hw
    rw [← h1, smul_smul, inv_mul_cancel₀ b.ne_zero, one_smul, h1]
  rcases hμ1 with hμ1 | hμ1
  ·
    have hc1 : c = 1 := by
      have := congrArg Units.val hμ1
      simpa using this
    subst hc1
    obtain ⟨B, hBH, hBs, hBnd, -⟩ := hsym hμ1
    have h2k : (2 : h.fixedField) ≠ 0 := fun h0 => two_ne_zero_of_odd h hp (by
      rw [← map_ofNat h.fixedField.subtype 2, h0, map_zero])
    have : Invertible (2 : h.fixedField) := invertibleOfNonzero h2k
    obtain ⟨vb, hvb⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
      ⟨fun x y => hBs.eq x y⟩
    have hbo : B.iIsOrtho vb := hvb
    have hd0 := hbo.not_isOrtho_basis_self_of_nondegenerate hBnd
    have h3 : 3 ≤ finrank h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) := by
      omega
    refine exists_comm_conj_of_orth_triple h hp hA hAA
      (w := fun i => (vb (Fin.castLE h3 i) : HypIndex r ε → K)) (fun i => hfix _ (vb _).2)
      (fun i => B (vb (Fin.castLE h3 i)) (vb (Fin.castLE h3 i))) (fun i => hd0 _)
      fun i j => ?_
    rw [← hBH]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [hvb (fun h0 => hij (Fin.castLE_inj.mp h0))]
      simp [hij]
  ·
    have hc1 : c = -1 := by
      have := congrArg Units.val hμ1
      simpa using this
    subst hc1
    obtain ⟨B, hBH, hBalt, hBnd, -, -⟩ := halt hμ1
    have : FiniteDimensional h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
      Module.Finite.of_finite
    obtain ⟨w₁, hw₁⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := h.fixedField)).mp
      (by omega : 0 < finrank h.fixedField
        (conjFixed h ((b : K) • conjOp h (A : Matrix (HypIndex r ε) (HypIndex r ε) K))))
    obtain ⟨w₂, hw₂⟩ : ∃ w₂, B w₁ w₂ ≠ 0 := by
      by_contra! h0
      exact hw₁ (hBnd.1 w₁ h0)
    have ht0 : (t : K) ≠ 0 := t.ne_zero
    obtain ⟨g, hg⟩ : ∃ g, hypForm h r ε (w₁ : HypIndex r ε → K) w₂ = g := ⟨_, rfl⟩
    have hg0 : g ≠ 0 := fun h0 => hw₂ (Subtype.ext (by rw [hBH, hg, h0, mul_zero]; rfl))
    have h11 : hypForm h r ε (w₁ : HypIndex r ε → K) w₁ = 0 := by
      have h1 := hBH w₁ w₁
      rw [hBalt w₁] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (inv_ne_zero ht0)
    have h22 : hypForm h r ε (w₂ : HypIndex r ε → K) w₂ = 0 := by
      have h1 := hBH w₂ w₂
      rw [hBalt w₂] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left (inv_ne_zero ht0)
    have h21 : hypForm h r ε (w₂ : HypIndex r ε → K) w₁ = -g := by
      have h1 := congrArg (fun x : h.fixedField => (x : K)) (hBalt.neg_eq w₁ w₂)
      simp only [Subfield.coe_neg, hBH, hg] at h1
      have h2 : (t : K)⁻¹ * (hypForm h r ε (w₂ : HypIndex r ε → K) w₁ + g) = 0 := by
        linear_combination -h1
      linear_combination (mul_eq_zero.mp h2).resolve_left (inv_ne_zero ht0)
    have hgbar : h.bar g = -g := by
      have h1 := (hypForm_isSymm h).eq (w₁ : HypIndex r ε → K) w₂
      rwa [hg, h21] at h1
    exact exists_comm_conj_of_alt_pair h hA hAA (hfix _ w₁.2) (hfix _ w₂.2) hg0 hgbar h11 h22
      hg h21

end Bar

end CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
