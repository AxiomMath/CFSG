module

public import CFSG.LieType.SeitzGeneration.OuterLinearRoot
public import CFSG.LieType.SeitzGeneration.OuterLinearDescent

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.RankThree.PartOne.CTP
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

section Conj

variable {n : ℕ} {K : Type} [Field K]

theorem slConjugation_tv_free (A : GL (Fin n) K) {v φ : Fin n → K} (h : φ ⬝ᵥ v = 0) :
    slConjugation n K A (tv v φ h) = tv ((A : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (φ ᵥ* ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (by rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, h]) := by
  apply Subtype.ext
  rw [slConjugation_matrix, tv_coe, tv_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Units.mul_inv]

theorem one_add_pow_of_sq_zero {R : Type*} [Ring R] (N : R) (hN : N * N = 0) (m : ℕ) :
    (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (1 + m • N) * (1 + N) = 1 + (m + 1) • N + m • (N * N) := by
      rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_assoc, add_smul, one_smul]
      abel
    rw [pow_succ, ih, e, hN, smul_zero, add_zero]

theorem map_inv_eq_mul_of_fixed {σ : K ≃+* K} {g : Matrix (Fin n) (Fin n) K} {M : GL (Fin n) K}
    (hgM : g * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * g := by
  have hMN : (M : Matrix (Fin n) (Fin n) K) * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (M : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h1 : (M : Matrix (Fin n) (Fin n) K).map σ *
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h2 : g = (M : Matrix (Fin n) (Fin n) K) *
      ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ := by
    calc g = g * ((M : Matrix (Fin n) (Fin n) K).map σ *
          ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ) := by rw [h1, mul_one]
      _ = (g * (M : Matrix (Fin n) (Fin n) K).map σ) *
          ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ := by rw [Matrix.mul_assoc]
      _ = (M : Matrix (Fin n) (Fin n) K) *
          ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ := by rw [hgM]
  rw [h2, ← Matrix.mul_assoc, hNM, Matrix.one_mul]

end Conj

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_top_of_fixed_matrix {k : Subfield K} (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    {p : ℕ} (hp : p.Prime) (hK : Nat.card K = Nat.card k ^ p) (hpK : (p : K) ≠ 0) (hn : 3 ≤ n)
    {H : Subgroup (SpecialLinearGroup (Fin n) K)} (hkH : slSub n k ≤ H)
    (g : Matrix (Fin n) (Fin n) K) (hgp : g ^ p = 1) (hg1 : g ≠ 1)
    (M : GL (Fin n) K) (hgM : g * (M : Matrix (Fin n) (Fin n) K).map σ = M)
    (hw : ∀ i, ((M : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single (⟨0, by omega⟩ : Fin n) 1) i ∈ k)
    (hMH : ∀ B ∈ slSub n k, slConjugation n K M B ∈ H) : H = ⊤ := by
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set N : Matrix (Fin n) (Fin n) K := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hMN : (M : Matrix (Fin n) (Fin n) K) * N = 1 := by
    rw [hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : N * (M : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [hN, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hσN : N.map σ = N * g := map_inv_eq_mul_of_fixed hgM
  set e : Fin n → K := Pi.single i₀ 1 with he
  set w₁ : Fin n → K := (M : Matrix (Fin n) (Fin n) K) *ᵥ e with hw₁
  have hw₁σ : ∀ i, σ (w₁ i) = w₁ i := fun i => (hk _).mp (hw i)
  have hw₁0 : w₁ ≠ 0 := by
    intro h0
    have h1 : e = N *ᵥ w₁ := by rw [hw₁, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    have h2 := congrFun h1 i₀
    simp [he] at h2
  have hσe : (⇑σ ∘ e) = e := by
    funext j
    by_cases hj : j = i₀ <;> simp [he, hj]
  have hgw : g *ᵥ w₁ = w₁ := by
    have h1 : (M : Matrix (Fin n) (Fin n) K).map σ *ᵥ e = w₁ := by
      funext i
      have h2 := RingHom.map_mulVec σ.toRingHom (M : Matrix (Fin n) (Fin n) K) e i
      have h3 : (σ.toRingHom ∘ e) = e := hσe
      rw [h3] at h2
      exact h2.symm.trans (hw₁σ i)
    calc g *ᵥ w₁ = g *ᵥ ((M : Matrix (Fin n) (Fin n) K).map σ *ᵥ e) := by rw [h1]
      _ = (g * (M : Matrix (Fin n) (Fin n) K).map σ) *ᵥ e := by rw [Matrix.mulVec_mulVec]
      _ = w₁ := by rw [hgM]
  by_cases hrat : ∀ i, i ≠ i₀ → ∀ j, N i j ∈ k
  · exfalso
    apply hg1
    set Ng : Matrix (Fin n) (Fin n) K := g - 1 with hNg
    have hY : ∀ i, i ≠ i₀ → ∀ j, (N * Ng) i j = 0 := by
      intro i hi j
      have h1 : (N * g) i j = N i j := by
        rw [← hσN]
        exact (hk _).mp (hrat i hi j)
      rw [hNg, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, h1, sub_self]
    have hNgM : Ng = vecMulVec w₁ ((N * Ng) i₀) := by
      have h1 : Ng = (M : Matrix (Fin n) (Fin n) K) * (N * Ng) := by
        rw [← Matrix.mul_assoc, hMN, Matrix.one_mul]
      conv_lhs => rw [h1]
      ext a b
      rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
      · rw [vecMulVec_apply, hw₁, he, Matrix.mulVec_single_one]
        rfl
      · intro c _ hc
        rw [hY c hc b, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hNgw : Ng *ᵥ w₁ = 0 := by
      rw [hNg, Matrix.sub_mulVec, hgw, Matrix.one_mulVec, sub_self]
    have hlamw : ((N * Ng) i₀) ⬝ᵥ w₁ = 0 := by
      rw [hNgM, vecMulVec_mulVec] at hNgw
      rcases smul_eq_zero.mp hNgw with h | h
      · simpa using congrArg MulOpposite.unop h
      · exact absurd h hw₁0
    have hNg2 : Ng * Ng = 0 := by
      conv_lhs => rw [hNgM]
      rw [vecMulVec_mul_vecMulVec, hlamw, zero_smul, vecMulVec_zero]
    have hg' : g = 1 + Ng := by rw [hNg]; abel
    have hpow := one_add_pow_of_sq_zero Ng hNg2 p
    rw [← hg', hgp] at hpow
    have h0 : p • Ng = 0 := add_eq_left.mp hpow.symm
    rw [← Nat.cast_smul_eq_nsmul K] at h0
    rcases smul_eq_zero.mp h0 with h | h
    · exact absurd h hpK
    · rw [hg', h, add_zero]
  · push Not at hrat
    obtain ⟨i, hi, j, hj⟩ := hrat
    have hB : (Pi.single i 1 : Fin n → K) ⬝ᵥ e = 0 := by simp [he, hi]
    have hrat1 : ∀ m : Fin n, ∀ x, (Pi.single m 1 : Fin n → K) x ∈ k := by
      intro m x
      by_cases h : x = m
      · subst h
        simp [k.one_mem]
      · simp [h, k.zero_mem]
    have hBk : tv e (Pi.single i 1) hB ∈ slSub n k := tv_mem_slSub hB (hrat1 i₀) (hrat1 i)
    have hconj := hMH _ hBk
    rw [slConjugation_tv_free] at hconj
    have hφ : (Pi.single i 1 : Fin n → K) ᵥ* ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        N i := by
      funext x
      simp [hN, Matrix.vecMul, dotProduct, Pi.single_apply]
    have hdot : N i ⬝ᵥ w₁ = 0 := by
      rw [← hφ, hw₁, dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, hB]
    have hmem : tv w₁ (N i) hdot ∈ H := (tv_eq_of_eq rfl hφ _ hdot) ▸ hconj
    exact eq_top_of_tv_irrational hkH hn hp hK hw hw₁0 _ ⟨j, hj⟩ hmem

theorem exists_fixed_matrix_rational_column {k : Subfield K} {ℓ e : ℕ} (σ : K ≃+* K)
    (hk : ∀ x, x ∈ k ↔ σ x = x) {p : ℕ} (hp : p.Prime) (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hK : Nat.card K = ℓ ^ e) (hσ : orderOf σ = p) (g : Matrix (Fin n) (Fin n) K)
    (hg : g.map σ = g) (hgp : g ^ p = 1) {w : Fin n → K} (hwk : ∀ i, w i ∈ k) (hw0 : w ≠ 0)
    (hgw : g *ᵥ w = w) (i₀ : Fin n) :
    ∃ M : GL (Fin n) K, g * (M : Matrix (Fin n) (Fin n) K).map σ = M ∧
      ∀ i, ((M : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i₀ 1) i ∈ k := by
  obtain ⟨M₀, hM₀det, hM₀⟩ := exists_fixed_matrix hp hℓ he hK σ hσ g hg hgp
  have hM₀M : M₀ * M₀⁻¹ = 1 := Matrix.mul_nonsing_inv M₀ hM₀det
  have hM₀M' : M₀⁻¹ * M₀ = 1 := Matrix.nonsing_inv_mul M₀ hM₀det
  set c : Fin n → K := M₀⁻¹ *ᵥ w with hc
  have hMc : M₀ *ᵥ c = w := by rw [hc, Matrix.mulVec_mulVec, hM₀M, Matrix.one_mulVec]
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hMc
    exact hw0 hMc.symm
  have hσc : ∀ i, σ (c i) = c i := by
    have h1 : M₀.map σ *ᵥ (σ ∘ c) = w := by
      funext i
      have h2 := RingHom.map_mulVec σ.toRingHom M₀ c i
      rw [hMc] at h2
      exact h2.symm.trans ((hk _).mp (hwk i))
    have h2 : M₀ *ᵥ (σ ∘ c) = w := by
      calc M₀ *ᵥ (σ ∘ c) = (g * M₀.map σ) *ᵥ (σ ∘ c) := by rw [hM₀]
        _ = g *ᵥ (M₀.map σ *ᵥ (σ ∘ c)) := by rw [Matrix.mulVec_mulVec]
        _ = g *ᵥ w := by rw [h1]
        _ = w := hgw
    have h3 : σ ∘ c = c := by
      calc σ ∘ c = M₀⁻¹ *ᵥ (M₀ *ᵥ (σ ∘ c)) := by
            rw [Matrix.mulVec_mulVec, hM₀M', Matrix.one_mulVec]
        _ = c := by rw [h2]
    exact fun i => congrFun h3 i
  have hck : ∀ i, c i ∈ k := fun i => (hk _).mpr (hσc i)
  obtain ⟨P, hP, lam, hlamk, hlam0, hPc⟩ := exists_slSub_mulVec_eq_smul_single hck hc0 i₀
  set Pinv : Matrix (Fin n) (Fin n) K :=
    ((P⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) with hPinv
  have hPinvk : ∀ a b, Pinv a b ∈ k := fun a b => (mem_slSub.mp ((slSub n k).inv_mem hP)) a b
  have hPinvσ : Pinv.map σ = Pinv := by
    ext a b
    exact (hk _).mp (hPinvk a b)
  have hPinvP : Pinv * (P : Matrix (Fin n) (Fin n) K) = 1 := coe_inv_mul_self P
  have hdetM : IsUnit (M₀ * Pinv).det := by
    rw [Matrix.det_mul]
    exact hM₀det.mul (by rw [hPinv, Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one)
  refine ⟨Matrix.nonsingInvUnit (M₀ * Pinv) hdetM, ?_, ?_⟩
  · show g * (M₀ * Pinv).map σ = M₀ * Pinv
    rw [Matrix.map_mul, hPinvσ, ← Matrix.mul_assoc, hM₀]
  · intro i
    show ((M₀ * Pinv) *ᵥ Pi.single i₀ 1) i ∈ k
    have h1 : Pinv *ᵥ (Pi.single i₀ 1 : Fin n → K) = lam⁻¹ • c := by
      calc Pinv *ᵥ (Pi.single i₀ 1 : Fin n → K) = Pinv *ᵥ (lam⁻¹ • ((P : Matrix _ _ K) *ᵥ c)) := by
            rw [hPc, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
        _ = lam⁻¹ • (Pinv *ᵥ ((P : Matrix _ _ K) *ᵥ c)) := by rw [Matrix.mulVec_smul]
        _ = lam⁻¹ • c := by rw [Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, hMc]
    exact k.mul_mem (k.inv_mem hlamk) (hwk i)

omit [Finite K] in
theorem slConjugation_map_ne {k : Subfield K} (σ : K ≃+* K) (hk : ∀ x, x ∈ k ↔ σ x = x)
    {p : ℕ} (hp : 0 < p) (g : Matrix (Fin n) (Fin n) K) (hgp : g ^ p = 1)
    (hg : ∀ c : K, g ≠ c • 1) (M : GL (Fin n) K)
    (hgM : g * (M : Matrix (Fin n) (Fin n) K).map σ = M) :
    (slSub n k).map (slConjugation n K M).toMonoidHom ≠ slSub n k := by
  intro heq
  set N : Matrix (Fin n) (Fin n) K := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hN
  have hσN : N.map σ = N * g := map_inv_eq_mul_of_fixed hgM
  have hσM : (M : Matrix (Fin n) (Fin n) K).map σ = g ^ (p - 1) * M := by
    have h1 : g ^ (p - 1) * g = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp, hgp]
    calc (M : Matrix (Fin n) (Fin n) K).map σ
        = (g ^ (p - 1) * g) * (M : Matrix (Fin n) (Fin n) K).map σ := by rw [h1, Matrix.one_mul]
      _ = g ^ (p - 1) * (g * (M : Matrix (Fin n) (Fin n) K).map σ) := by rw [Matrix.mul_assoc]
      _ = g ^ (p - 1) * M := by rw [hgM]
  have hcomm : ∀ X ∈ slSub n k, g * (X : Matrix (Fin n) (Fin n) K) = X * g := by
    intro X hX
    have hX' : X ∈ (slSub n k).map (slConjugation n K M).toMonoidHom := by rw [heq]; exact hX
    obtain ⟨B, hB, rfl⟩ := hX'
    have hBσ : (B : Matrix (Fin n) (Fin n) K).map σ = B := by
      ext i j
      exact (hk _).mp ((mem_slSub.mp hB) i j)
    have hXσ : ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K).map σ = slConjugation n K M B := by
      ext i j
      exact (hk _).mp ((mem_slSub.mp (by rw [← heq]; exact ⟨B, hB, rfl⟩ : slConjugation n K M B ∈
        slSub n k)) i j)
    have hXM : ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = M * B * N := slConjugation_matrix n K M B
    have h1 : (M * (B : Matrix (Fin n) (Fin n) K) * N).map σ =
        g ^ (p - 1) * (M * B * N) * g := by
      rw [Matrix.map_mul, Matrix.map_mul, hσM, hBσ, hσN]
      simp only [Matrix.mul_assoc]
    change g * ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((slConjugation n K M B : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * g
    rw [hXM] at hXσ ⊢
    rw [h1] at hXσ
    calc g * (M * B * N) = g * (g ^ (p - 1) * (M * B * N) * g) := by rw [hXσ]
      _ = (g * g ^ (p - 1)) * (M * B * N) * g := by simp only [Matrix.mul_assoc]
      _ = (M * B * N) * g := by rw [← pow_succ', Nat.sub_add_cancel hp, hgp, Matrix.one_mul]
  have hsingle : Pairwise fun i j : Fin n => Commute (Matrix.single i j (1 : K)) g := by
    intro i j hij
    have h1 := hcomm _ (transvection_mem_slSub hij k.one_mem)
    rw [SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul] at h1
    exact (add_left_cancel h1).symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single hsingle
  apply hg c
  rw [← hc]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]

end Main

end CFSG.LieType.SeitzGeneration
