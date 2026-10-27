module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearInnerSupply

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear.Lagrangian

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem smul_semilin_eq_of_fix [Finite K] (hn : 3 ≤ n) {A : GL (Fin n) K} {φ : K ≃+* K}
    {x a : Fin n → K} (h : a ⬝ᵥ x = 0)
    (hfix : (conjAut n K A * fieldAut n K φ) (proj n K (rankOne x a h)) =
      proj n K (rankOne x a h)) (v : Fin n → K) :
    φ (a ⬝ᵥ v) • semilin A φ x = (a ⬝ᵥ semilin A φ v) • x := by
  have h' : (A : Matrix (Fin n) (Fin n) K) *
      ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).map φ *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg Units.val (conj_map_eq_of_apply_eq hn (rankOne_sub_one_sq x a h) hfix)
  have h1 := conj_mulVec_semilin (A := A) (φ := φ)
    ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) v
  rw [h', rankOne_mulVec, rankOne_mulVec, semilin_add, semilin_smul] at h1
  exact (add_left_cancel h1).symm

theorem exists_mulVec_eq_smul_of_fix_dualAut [Finite K] (hn : 3 ≤ n) {A : GL (Fin n) K}
    {φ : K ≃+* K} {x a : Fin n → K} (h : a ⬝ᵥ x = 0) (hx0 : x ≠ 0)
    (hfix : (conjAut n K A * fieldAut n K φ * dualAut n K) (proj n K (rankOne x a h)) =
      proj n K (rankOne x a h)) :
    ∃ c : K, (A : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (a i)) = c • x := by
  set φa : Fin n → K := fun i => φ (a i) with hφa
  have h' := congrArg Units.val (conj_map_inverseTranspose_eq_of_apply_eq hn
    (rankOne_sub_one_sq x a h) (inverseTranspose_rankOne_sub_one_sq x a h) hfix)
  set φx : Fin n → K := fun i => φ (x i) with hφx
  have hmap : ((GeneralLinearGroup.map (φ : K →+* K) (GeneralLinearGroup.inverseTranspose
      (SpecialLinearGroup.toGL (rankOne x a h))) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = 1 - vecMulVec φa φx := by
    change (((GeneralLinearGroup.inverseTranspose
      (SpecialLinearGroup.toGL (rankOne x a h))) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).map φ = _
    rw [coe_inverseTranspose_rankOne]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hφa, hφx]
    split_ifs <;> simp
  rw [Units.val_mul, Units.val_mul, hmap] at h'
  have h2 : (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) =
      (1 + vecMulVec x a) * A := by
    calc (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx)
        = (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) *
          (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
          rw [inv_mul_self_val, Matrix.mul_one]
      _ = (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A := by
          simp only [Matrix.mul_assoc]
      _ = (1 + vecMulVec x a) * A := by rw [h']; rfl
  have h3 : vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ φa) φx =
      vecMulVec (-x) (a ᵥ* (A : Matrix (Fin n) (Fin n) K)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h2
    rw [← mul_vecMulVec, neg_vecMulVec, ← vecMulVec_mul]
    have h4 := congrArg (fun M => (A : Matrix (Fin n) (Fin n) K) - M) h2
    simp only [sub_sub_cancel, sub_add_cancel_left] at h4
    exact h4
  have hφx0 : φx ≠ 0 := by
    intro h0
    apply hx0
    funext i
    have := congrFun h0 i
    simp only [hφx, Pi.zero_apply, map_eq_zero_iff φ φ.injective] at this
    exact this
  obtain ⟨c, hc⟩ := exists_smul_eq_of_vecMulVec_eq h3 hφx0
  exact ⟨-c, by rw [hc, smul_neg, neg_smul]⟩

section Basis

variable {ℓ : ℕ} (b : Module.Basis (Fin ℓ ⊕ (Fin ℓ ⊕ Fin 0)) K (Fin n → K))

theorem dualVec_inl_dotProduct_inl (i j : Fin ℓ) :
    dualVec b (.inl i) ⬝ᵥ b (.inl j) = if j = i then 1 else 0 := by
  classical
  rw [dualVec_dotProduct_basis]
  simp only [Sum.inl.injEq]

theorem dualVec_inl_dotProduct_inr (i j : Fin ℓ) :
    dualVec b (.inl i) ⬝ᵥ b (.inr (.inl j)) = 0 := by
  classical
  rw [dualVec_dotProduct_basis]
  simp

theorem dualVec_inr_dotProduct_inl (i j : Fin ℓ) :
    dualVec b (.inr (.inl i)) ⬝ᵥ b (.inl j) = 0 := by
  classical
  rw [dualVec_dotProduct_basis]
  simp

theorem dualVec_inr_dotProduct_inr (i j : Fin ℓ) :
    dualVec b (.inr (.inl i)) ⬝ᵥ b (.inr (.inl j)) = if j = i then 1 else 0 := by
  classical
  rw [dualVec_dotProduct_basis]
  simp only [Sum.inr.injEq, Sum.inl.injEq]

theorem eq_sum_of_dualVec_inl_eq_zero {y : Fin n → K}
    (hy : ∀ i, dualVec b (.inl i) ⬝ᵥ y = 0) :
    y = ∑ i, (dualVec b (.inr (.inl i)) ⬝ᵥ y) • b (.inr (.inl i)) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_zero, add_zero]
  simp only [← dualVec_dotProduct, hy, zero_smul, Finset.sum_const_zero, zero_add]

theorem mulVec_eq_smul_of_dualVec_inl_eq_zero {A : Matrix (Fin n) (Fin n) K} {κ : K}
    (hA : ∀ i, A *ᵥ b (.inr (.inl i)) = κ • b (.inr (.inl i))) {y : Fin n → K}
    (hy : ∀ i, dualVec b (.inl i) ⬝ᵥ y = 0) : A *ᵥ y = κ • y := by
  rw [eq_sum_of_dualVec_inl_eq_zero b hy, mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_smul, hA, smul_comm]

theorem conjAut_sq_eq_one_of_mulVec [CharP K 2] {A : GL (Fin n) K} {κ : K} (hκ : κ ≠ 0)
    (hW : ∀ j, (A : Matrix (Fin n) (Fin n) K) *ᵥ b (.inr (.inl j)) = κ • b (.inr (.inl j)))
    (hX : ∀ v i, dualVec b (.inl i) ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - κ • v) = 0) :
    conjAut n K A ^ 2 = 1 := by
  have hAA : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (κ * κ) • v := by
    intro v
    have h1 : (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - κ • v) =
        κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - κ • v) :=
      mulVec_eq_smul_of_dualVec_inl_eq_zero b hW fun i => hX v i
    rw [mulVec_sub, mulVec_smul, sub_eq_iff_eq_add] at h1
    rw [h1, smul_sub, smul_smul]
    have h2 : κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) +
        κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) = 0 := by
      rw [← two_smul K, CharTwo.two_eq_zero, zero_smul]
    calc κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) - (κ * κ) • v +
          κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = (κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) +
            κ • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)) - (κ * κ) • v := by abel
      _ = (κ * κ) • v := by rw [h2, zero_sub, ← neg_smul, CharTwo.neg_eq]
  set u : Kˣ := Units.mk0 κ hκ with hu
  have hAsq : A * A = GeneralLinearGroup.scalar (Fin n) (u * u) := by
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, ← mulVec_mulVec, hAA,
      GeneralLinearGroup.coe_scalar, scalar_apply]
    ext i
    simp [mulVec_diagonal, hu]
  rw [pow_two, ← map_mul, hAsq, conjAut_scalar]

theorem semilinear_rigid_of_fix [Finite K] (hn : 3 ≤ n) {i₀ i₁ : Fin ℓ} (h01 : i₀ ≠ i₁)
    {A : GL (Fin n) K} {φ : K ≃+* K}
    (hoff : ∀ i j : Fin ℓ, i ≠ j → ∀ (c : K)
      (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
      (conjAut n K A * fieldAut n K φ)
          (proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h)) =
        proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h))
    (hext : ∀ h : (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ
        (b (.inr (.inl i₀)) + b (.inr (.inl i₁))) = 0,
      (conjAut n K A * fieldAut n K φ) (proj n K (rankOne (b (.inr (.inl i₀)) +
          b (.inr (.inl i₁))) (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h)) =
        proj n K (rankOne (b (.inr (.inl i₀)) + b (.inr (.inl i₁)))
          (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h)) :
    φ = 1 ∧ ∃ κ : K, κ ≠ 0 ∧
      (∀ j, (A : Matrix (Fin n) (Fin n) K) *ᵥ b (.inr (.inl j)) = κ • b (.inr (.inl j))) ∧
      ∀ v i, dualVec b (.inl i) ⬝ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - κ • v) = 0 := by
  classical
  set κ : Fin ℓ → K := fun i => dualVec b (.inl i) ⬝ᵥ semilin A φ (b (.inl i)) with hκdef
  have hdot : ∀ i j : Fin ℓ, ∀ c : K, dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0 :=
    fun i j c => by rw [dotProduct_smul, dualVec_inl_dotProduct_inr, smul_zero]
  have hrel : ∀ i j : Fin ℓ, i ≠ j → ∀ (c : K) (v : Fin n → K),
      φ (dualVec b (.inl i) ⬝ᵥ v) • semilin A φ (c • b (.inr (.inl j))) =
        (dualVec b (.inl i) ⬝ᵥ semilin A φ v) • (c • b (.inr (.inl j))) :=
    fun i j hij c v => smul_semilin_eq_of_fix hn (hdot i j c) (hoff i j hij c (hdot i j c)) v
  have hTW : ∀ i j : Fin ℓ, i ≠ j → ∀ c : K,
      semilin A φ (c • b (.inr (.inl j))) = (κ i * c) • b (.inr (.inl j)) := by
    intro i j hij c
    have h := hrel i j hij c (b (.inl i))
    rwa [dualVec_inl_dotProduct_inl, ite_eq_left rfl, map_one, one_smul, smul_smul] at h
  have hTW1 : ∀ i j : Fin ℓ, i ≠ j →
      semilin A φ (b (.inr (.inl j))) = κ i • b (.inr (.inl j)) := by
    intro i j hij
    have h := hTW i j hij 1
    rwa [one_smul, mul_one] at h
  have hdotE : (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ
      (b (.inr (.inl i₀)) + b (.inr (.inl i₁))) = 0 := by
    simp only [sub_dotProduct, dotProduct_add, dualVec_inl_dotProduct_inr, add_zero, sub_zero]
  have hE := smul_semilin_eq_of_fix hn hdotE (hext hdotE) (b (.inl i₁))
  rw [sub_dotProduct, dualVec_inl_dotProduct_inl, dualVec_inl_dotProduct_inl, ite_eq_left rfl,
    ite_eq_right h01.symm, sub_zero, map_one, one_smul, semilin_add, hTW1 i₁ i₀ h01.symm,
    hTW1 i₀ i₁ h01] at hE
  set μ := (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ semilin A φ (b (.inl i₁)) with hμ
  have hκ₁ : κ i₁ = μ := by
    have h := congrArg (dualVec b (.inr (.inl i₀)) ⬝ᵥ ·) hE
    simpa [dotProduct_add, dotProduct_smul, dualVec_inr_dotProduct_inr, h01, h01.symm] using h
  have hκ₀ : κ i₀ = μ := by
    have h := congrArg (dualVec b (.inr (.inl i₁)) ⬝ᵥ ·) hE
    simpa [dotProduct_add, dotProduct_smul, dualVec_inr_dotProduct_inr, h01, h01.symm] using h
  have hTWall : ∀ (j : Fin ℓ) (c : K),
      semilin A φ (c • b (.inr (.inl j))) = (κ i₀ * c) • b (.inr (.inl j)) := by
    intro j c
    by_cases hj : j = i₀
    · subst hj
      rw [hTW i₁ j h01.symm c, hκ₁, hκ₀]
    · exact hTW i₀ j (Ne.symm hj) c
  have hκ0 : κ i₀ ≠ 0 := by
    intro h0
    apply semilin_ne_zero (A := A) (φ := φ) (b.ne_zero (.inr (.inl i₁)))
    have h := hTWall i₁ 1
    rwa [one_smul, mul_one, h0, zero_smul] at h
  have hφ : φ = 1 := by
    apply RingEquiv.ext
    intro c
    have h := hTWall i₁ c
    rw [semilin_smul, ← one_smul K (b (.inr (.inl i₁))), hTWall i₁ 1, one_smul, mul_one,
      smul_smul] at h
    have h2 : φ c * κ i₀ = κ i₀ * c := smul_left_injective K (b.ne_zero _) h
    rw [mul_comm (κ i₀) c] at h2
    exact mul_right_cancel₀ hκ0 h2
  subst hφ
  have hsemi : ∀ v, semilin A 1 v = (A : Matrix (Fin n) (Fin n) K) *ᵥ v := fun v => rfl
  refine ⟨rfl, κ i₀, hκ0, fun j => ?_, fun v i => ?_⟩
  · have h := hTWall j 1
    rwa [one_smul, mul_one, hsemi] at h
  ·
    obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by
      by_cases hi : i = i₀
      · exact ⟨i₁, hi ▸ h01⟩
      · exact ⟨i₀, hi⟩
    have h := hrel i j hij 1 v
    rw [hTWall j 1, one_smul, mul_one, smul_smul] at h
    have h2 : (1 : K ≃+* K) (dualVec b (.inl i) ⬝ᵥ v) * κ i₀ =
        dualVec b (.inl i) ⬝ᵥ semilin A 1 v := smul_left_injective K (b.ne_zero _) h
    rw [hsemi] at h2
    change dualVec b (.inl i) ⬝ᵥ v * κ i₀ = _ at h2
    rw [dotProduct_sub, dotProduct_smul, ← h2, smul_eq_mul, mul_comm, sub_self]

theorem sq_eq_one_of_fix_conjAut_mul_fieldAut [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {i₀ i₁ : Fin ℓ} (h01 : i₀ ≠ i₁) {A : GL (Fin n) K} {φ : K ≃+* K}
    (hoff : ∀ i j : Fin ℓ, i ≠ j → ∀ (c : K)
      (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
      (conjAut n K A * fieldAut n K φ)
          (proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h)) =
        proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h))
    (hext : ∀ h : (dualVec b (.inl i₁) - dualVec b (.inl i₀)) ⬝ᵥ
        (b (.inr (.inl i₀)) + b (.inr (.inl i₁))) = 0,
      (conjAut n K A * fieldAut n K φ) (proj n K (rankOne (b (.inr (.inl i₀)) +
          b (.inr (.inl i₁))) (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h)) =
        proj n K (rankOne (b (.inr (.inl i₀)) + b (.inr (.inl i₁)))
          (dualVec b (.inl i₁) - dualVec b (.inl i₀)) h)) :
    (conjAut n K A * fieldAut n K φ) ^ 2 = 1 := by
  obtain ⟨rfl, κ, hκ, hW, hX⟩ := semilinear_rigid_of_fix b hn h01 hoff hext
  rw [map_one, mul_one]
  exact conjAut_sq_eq_one_of_mulVec b hκ hW hX

theorem false_of_fix_dualAut [Finite K] (hn : 3 ≤ n) {i j k : Fin ℓ} (hjk : j ≠ k)
    {A : GL (Fin n) K} {φ : K ≃+* K}
    (hj : ∀ h : dualVec b (.inl i) ⬝ᵥ b (.inr (.inl j)) = 0,
      (conjAut n K A * fieldAut n K φ * dualAut n K)
          (proj n K (rankOne (b (.inr (.inl j))) (dualVec b (.inl i)) h)) =
        proj n K (rankOne (b (.inr (.inl j))) (dualVec b (.inl i)) h))
    (hk : ∀ h : dualVec b (.inl i) ⬝ᵥ b (.inr (.inl k)) = 0,
      (conjAut n K A * fieldAut n K φ * dualAut n K)
          (proj n K (rankOne (b (.inr (.inl k))) (dualVec b (.inl i)) h)) =
        proj n K (rankOne (b (.inr (.inl k))) (dualVec b (.inl i)) h)) :
    False := by
  classical
  obtain ⟨c₁, hc₁⟩ := exists_mulVec_eq_smul_of_fix_dualAut hn (dualVec_inl_dotProduct_inr b i j)
    (b.ne_zero _) (hj _)
  obtain ⟨c₂, hc₂⟩ := exists_mulVec_eq_smul_of_fix_dualAut hn (dualVec_inl_dotProduct_inr b i k)
    (b.ne_zero _) (hk _)
  have hc : c₁ = 0 := by
    have h := congrArg (dualVec b (.inr (.inl j)) ⬝ᵥ ·) (hc₁.symm.trans hc₂)
    simpa [dotProduct_smul, dualVec_inr_dotProduct_inr, hjk, hjk.symm] using h
  rw [hc, zero_smul] at hc₁
  have hφa : (fun l => φ (dualVec b (.inl i) l)) = 0 := by
    have := congrArg (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) hc₁
    simpa only [mulVec_mulVec, inv_mul_self_val, one_mulVec, mulVec_zero] using this
  have ha0 : dualVec b (.inl i) = 0 := by
    funext l
    have := congrFun hφa l
    simp only [Pi.zero_apply, map_eq_zero_iff φ φ.injective] at this
    exact this
  have h1 := dualVec_inl_dotProduct_inl b i i
  rw [ha0, zero_dotProduct, ite_eq_left rfl] at h1
  exact zero_ne_one h1

end Basis

end CFSG.SeitzReduction.ClassicalLinear.Lagrangian
