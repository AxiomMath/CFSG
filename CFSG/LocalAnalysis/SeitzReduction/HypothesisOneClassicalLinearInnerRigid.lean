module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLFlagKernel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneInnerBasic

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem coe_rankOne (x a : Fin n → K) (h : a ⬝ᵥ x = 0) :
    ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec x a :=
  rfl

theorem rankOne_sub_one_sq (x a : Fin n → K) (h : a ⬝ᵥ x = 0) :
    (((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  rw [coe_rankOne, add_sub_cancel_left, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]

theorem coe_inv_eq_of_mul_eq_one {g : SpecialLinearGroup (Fin n) K}
    {B : Matrix (Fin n) (Fin n) K} (h : (g : Matrix (Fin n) (Fin n) K) * B = 1) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = B := by
  have h1 : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 :=
    congrArg Subtype.val (inv_mul_cancel g)
  calc ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g : Matrix (Fin n) (Fin n) K) * B) := by rw [h, Matrix.mul_one]
    _ = B := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem coe_rankOne_inv (x a : Fin n → K) (h : a ⬝ᵥ x = 0) :
    (((rankOne x a h)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 - vecMulVec x a := by
  have h1 : ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (1 - vecMulVec x a) = 1 := by
    rw [coe_rankOne, Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero, sub_zero, sub_add_cancel]
  exact coe_inv_eq_of_mul_eq_one h1

theorem coe_inverseTranspose_rankOne (x a : Fin n → K) (h : a ⬝ᵥ x = 0) :
    ((GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL (rankOne x a h)) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - vecMulVec a x := by
  rw [GeneralLinearGroup.coe_inverseTranspose, ← map_inv]
  change ((((rankOne x a h)⁻¹ : SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K))ᵀ = _
  rw [coe_rankOne_inv, transpose_sub, transpose_one, transpose_vecMulVec]

theorem inverseTranspose_rankOne_sub_one_sq (x a : Fin n → K) (h : a ⬝ᵥ x = 0) :
    (((GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL (rankOne x a h)) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL (rankOne x a h)) :
        GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := by
  rw [coe_inverseTranspose_rankOne, sub_sub_cancel_left, neg_mul_neg, vecMulVec_mul_vecMulVec,
    dotProduct_comm, h, zero_smul, vecMulVec_zero]

theorem exists_smul_eq_of_vecMulVec_eq {x y a b : Fin n → K} (hab : vecMulVec x a = vecMulVec y b)
    (ha : a ≠ 0) : ∃ c : K, x = c • y := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  refine ⟨b j / a j, funext fun i => ?_⟩
  have h := congrFun (congrFun hab i) j
  rw [vecMulVec_apply, vecMulVec_apply] at h
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hj, h]
  ring

theorem conj_map_eq_of_apply_eq [Finite K] (hn : 3 ≤ n) {A : GL (Fin n) K} {φ : K ≃+* K}
    {u : SpecialLinearGroup (Fin n) K}
    (hu : ((u : Matrix (Fin n) (Fin n) K) - 1) * ((u : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hfix : (conjAut n K A * fieldAut n K φ) (proj n K u) = proj n K u) :
    A * GeneralLinearGroup.map (φ : K →+* K) (SpecialLinearGroup.toGL u) * A⁻¹ =
      SpecialLinearGroup.toGL u := by
  have hu' : (((SpecialLinearGroup.toGL u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((SpecialLinearGroup.toGL u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := hu
  refine eq_of_conjAut_eq_of_unipotent hn (unipotent_conj (unipotent_map _ hu')) hu' ?_
  rw [← conj_conjAut_fieldAut, conjAut_toGL, mul_conj_mul_inv_eq_conj, hfix]

theorem conj_map_inverseTranspose_eq_of_apply_eq [Finite K] (hn : 3 ≤ n) {A : GL (Fin n) K}
    {φ : K ≃+* K} {u : SpecialLinearGroup (Fin n) K}
    (hu : ((u : Matrix (Fin n) (Fin n) K) - 1) * ((u : Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hu' : (((GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL u) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1) *
      (((GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL u) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) - 1) = 0)
    (hfix : (conjAut n K A * fieldAut n K φ * dualAut n K) (proj n K u) = proj n K u) :
    A * GeneralLinearGroup.map (φ : K →+* K)
        (GeneralLinearGroup.inverseTranspose (SpecialLinearGroup.toGL u)) * A⁻¹ =
      SpecialLinearGroup.toGL u := by
  have hu₀ : (((SpecialLinearGroup.toGL u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) *
      (((SpecialLinearGroup.toGL u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) = 0 := hu
  refine eq_of_conjAut_eq_of_unipotent hn (unipotent_conj (unipotent_map _ hu')) hu₀ ?_
  rw [← conj_conjAut_fieldAut_dualAut, conjAut_toGL, mul_conj_mul_inv_eq_conj, hfix]

theorem conjAut_sq_eq_one_of_forall_fix [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {W L : Submodule K (Fin n → K)} (hWL : W ≤ L) {a₀ v₀ w₀ : Fin n → K}
    (ha₀ : a₀ ∈ dotOrth L) (hav₀ : a₀ ⬝ᵥ v₀ = 1) (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0)
    {A : GL (Fin n) K} {φ : K ≃+* K}
    (hL : ∀ x ∈ L, ∀ h : a₀ ⬝ᵥ x = 0,
      (conjAut n K A * fieldAut n K φ) (proj n K (rankOne x a₀ h)) = proj n K (rankOne x a₀ h))
    (hW : ∀ m ∈ dotOrth W, ∀ h : m ⬝ᵥ w₀ = 0,
      (conjAut n K A * fieldAut n K φ) (proj n K (rankOne w₀ m h)) = proj n K (rankOne w₀ m h)) :
    (conjAut n K A * fieldAut n K φ) ^ 2 = 1 := by
  have : NeZero n := ⟨by omega⟩
  have hrank : ∀ (x a : Fin n → K) (h : a ⬝ᵥ x = 0),
      (conjAut n K A * fieldAut n K φ) (proj n K (rankOne x a h)) = proj n K (rankOne x a h) →
      ∀ v, φ (a ⬝ᵥ v) • semilin A φ x = (a ⬝ᵥ semilin A φ v) • x := by
    intro x a h hfix v
    set u := rankOne x a h with hu
    have h' : (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (u : Matrix (Fin n) (Fin n) K) :=
      congrArg Units.val (conj_map_eq_of_apply_eq hn (rankOne_sub_one_sq x a h) hfix)
    have hmat : (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ =
        (u : Matrix (Fin n) (Fin n) K) * A := by
      calc (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ
          = (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
            rw [inv_mul_self_val, Matrix.mul_one]
        _ = (A : Matrix (Fin n) (Fin n) K) * (u : Matrix (Fin n) (Fin n) K).map φ *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A := by
            simp only [Matrix.mul_assoc]
        _ = (u : Matrix (Fin n) (Fin n) K) * A := by rw [h']
    have h1 : semilin A φ ((u : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (u : Matrix (Fin n) (Fin n) K) *ᵥ semilin A φ v := by
      rw [semilin_mulVec, hmat, semilin, mulVec_mulVec]
    rw [hu, rankOne_mulVec, rankOne_mulVec, semilin_add, semilin_smul] at h1
    exact add_left_cancel h1
  set c := a₀ ⬝ᵥ semilin A φ v₀ with hcdef
  have hTL : ∀ x ∈ L, semilin A φ x = c • x := by
    intro x hx
    have h := hrank x a₀ (mem_dotOrth.mp ha₀ x hx) (hL x hx _) v₀
    rwa [hav₀, map_one, one_smul] at h
  have hc0 : c ≠ 0 := by
    intro hc
    apply semilin_ne_zero (A := A) (φ := φ) hw₀0
    rw [hTL w₀ (hWL hw₀), hc, zero_smul]
  have hφ : φ = 1 := by
    apply RingEquiv.ext
    intro t
    have h := hTL (t • w₀) (L.smul_mem t (hWL hw₀))
    rw [semilin_smul, hTL w₀ (hWL hw₀), smul_smul, smul_smul] at h
    have h2 : φ t * c = c * t := smul_left_injective K hw₀0 h
    rw [mul_comm c t] at h2
    exact mul_right_cancel₀ hc0 h2
  subst hφ
  have hsemi : ∀ v, semilin A 1 v = (A : Matrix (Fin n) (Fin n) K) *ᵥ v := fun v => rfl
  have hAL : ∀ x ∈ L, (A : Matrix (Fin n) (Fin n) K) *ᵥ x = c • x := fun x hx =>
    (hsemi x).symm.trans (hTL x hx)
  have hAW : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v ∈ W := by
    intro v
    apply mem_of_forall_dotOrth
    intro m hm
    have hdot : m ⬝ᵥ w₀ = 0 := mem_dotOrth.mp hm w₀ hw₀
    have h := hrank w₀ m hdot (hW m hm hdot) v
    rw [hTL w₀ (hWL hw₀), smul_smul] at h
    have h2 : (1 : K ≃+* K) (m ⬝ᵥ v) * c = m ⬝ᵥ semilin A 1 v :=
      smul_left_injective K hw₀0 h
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ← hsemi, ← h2]
    change m ⬝ᵥ v * c - c * (m ⬝ᵥ v) = 0
    ring
  have hAA : ∀ v, (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (c * c) • v := by
    intro v
    have hw := hAW v
    have h1 : (A : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v) =
        c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v - c • v) := hAL _ (hWL hw)
    rw [mulVec_sub, mulVec_smul, sub_eq_iff_eq_add] at h1
    rw [h1, smul_sub, smul_smul]
    have h2 : c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) + c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = 0 := CharTwo.add_self_eq_zero _
    calc c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) - (c * c) • v +
          c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)
        = (c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) +
            c • ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)) - (c * c) • v := by abel
      _ = (c * c) • v := by rw [h2, zero_sub, CharTwo.neg_eq]
  set u : Kˣ := Units.mk0 c hc0 with hu
  have hAsq : A * A = GeneralLinearGroup.scalar (Fin n) (u * u) := by
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Units.val_mul, ← mulVec_mulVec, hAA,
      GeneralLinearGroup.coe_scalar, scalar_apply]
    ext i
    simp [mulVec_diagonal, hu]
  rw [map_one, mul_one, pow_two, ← map_mul, hAsq, conjAut_scalar]

theorem not_forall_fix_rankOne_dualAut [Finite K] (hn : 3 ≤ n) {W L : Submodule K (Fin n → K)}
    (hWL : W ≤ L) {a₀ v₀ w₀ x₂ : Fin n → K} (ha₀ : a₀ ∈ dotOrth L) (hav₀ : a₀ ⬝ᵥ v₀ = 1)
    (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0) (hx₂L : x₂ ∈ L) (hx₂W : x₂ ∉ W) (A : GL (Fin n) K)
    (φ : K ≃+* K)
    (hL : ∀ x ∈ L, ∀ h : a₀ ⬝ᵥ x = 0,
      (conjAut n K A * fieldAut n K φ * dualAut n K) (proj n K (rankOne x a₀ h)) =
        proj n K (rankOne x a₀ h)) :
    False := by
  set φa : Fin n → K := fun i => φ (a₀ i) with hφa
  have key : ∀ x ∈ L, x ≠ 0 → ∃ c : K, (A : Matrix (Fin n) (Fin n) K) *ᵥ φa = c • x := by
    intro x hx hx0
    have hdot : a₀ ⬝ᵥ x = 0 := mem_dotOrth.mp ha₀ x hx
    have h' := congrArg Units.val (conj_map_inverseTranspose_eq_of_apply_eq hn
      (rankOne_sub_one_sq x a₀ hdot) (inverseTranspose_rankOne_sub_one_sq x a₀ hdot)
      (hL x hx hdot))
    set φx : Fin n → K := fun i => φ (x i) with hφx
    have hmap : ((GeneralLinearGroup.map (φ : K →+* K) (GeneralLinearGroup.inverseTranspose
        (SpecialLinearGroup.toGL (rankOne x a₀ hdot))) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = 1 - vecMulVec φa φx := by
      change (((GeneralLinearGroup.inverseTranspose
        (SpecialLinearGroup.toGL (rankOne x a₀ hdot))) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map φ = _
      rw [coe_inverseTranspose_rankOne]
      ext i j
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, hφa, hφx]
      split_ifs <;> simp
    rw [Units.val_mul, Units.val_mul, hmap] at h'
    have h2 : (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) =
        (1 + vecMulVec x a₀) * A := by
      calc (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx)
          = (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) *
            (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A) := by
            rw [inv_mul_self_val, Matrix.mul_one]
        _ = (A : Matrix (Fin n) (Fin n) K) * (1 - vecMulVec φa φx) *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A := by
            simp only [Matrix.mul_assoc]
        _ = (1 + vecMulVec x a₀) * A := by rw [h']; rfl
    have h3 : vecMulVec ((A : Matrix (Fin n) (Fin n) K) *ᵥ φa) φx =
        vecMulVec (-x) (a₀ ᵥ* (A : Matrix (Fin n) (Fin n) K)) := by
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
  obtain ⟨c₁, hc₁⟩ := key w₀ (hWL hw₀) hw₀0
  have hx₂0 : x₂ ≠ 0 := fun h => hx₂W (h ▸ W.zero_mem)
  obtain ⟨c₂, hc₂⟩ := key x₂ hx₂L hx₂0
  by_cases hc : c₂ = 0
  · rw [hc, zero_smul] at hc₂
    have hφa0 : φa = 0 := by
      have := congrArg (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) hc₂
      simpa only [mulVec_mulVec, inv_mul_self_val, one_mulVec, mulVec_zero] using this
    have ha0 : a₀ = 0 := by
      funext i
      have := congrFun hφa0 i
      simp only [hφa, Pi.zero_apply, map_eq_zero_iff φ φ.injective] at this
      exact this
    rw [ha0, zero_dotProduct] at hav₀
    exact zero_ne_one hav₀
  · apply hx₂W
    have hx₂ : x₂ = (c₂⁻¹ * c₁) • w₀ := by
      rw [hc₁] at hc₂
      calc x₂ = c₂⁻¹ • (c₂ • x₂) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c₂⁻¹ • (c₁ • w₀) := by rw [hc₂]
        _ = (c₂⁻¹ * c₁) • w₀ := by rw [smul_smul]
    rw [hx₂]
    exact W.smul_mem _ hw₀

theorem sq_eq_one_of_forall_fix_rankOne [Finite K] [CharP K 2] (hn : 3 ≤ n)
    {W L : Submodule K (Fin n → K)} (hWL : W ≤ L) {a₀ v₀ w₀ x₂ : Fin n → K}
    (ha₀ : a₀ ∈ dotOrth L) (hav₀ : a₀ ⬝ᵥ v₀ = 1) (hw₀ : w₀ ∈ W) (hw₀0 : w₀ ≠ 0)
    (hx₂L : x₂ ∈ L) (hx₂W : x₂ ∉ W) {β : MulAut (projectiveSL n K)}
    (hL : ∀ x ∈ L, ∀ h : a₀ ⬝ᵥ x = 0, β (proj n K (rankOne x a₀ h)) = proj n K (rankOne x a₀ h))
    (hW : ∀ m ∈ dotOrth W, ∀ h : m ⬝ᵥ w₀ = 0,
      β (proj n K (rankOne w₀ m h)) = proj n K (rankOne w₀ m h)) :
    β ^ 2 = 1 := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, φ, ε, hε, rfl⟩ := hform β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hL hW ⊢
    exact conjAut_sq_eq_one_of_forall_fix hn hWL ha₀ hav₀ hw₀ hw₀0 hL hW
  · rw [pow_one] at hL
    exact (not_forall_fix_rankOne_dualAut hn hWL ha₀ hav₀ hw₀ hw₀0 hx₂L hx₂W A φ hL).elim

end CFSG.SeitzReduction.ClassicalLinear
