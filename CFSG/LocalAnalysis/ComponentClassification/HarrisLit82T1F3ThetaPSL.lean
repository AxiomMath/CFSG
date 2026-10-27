module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit CFSG.Blueprint
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem blockScalarGL_pow (J : Finset (Fin n)) (α β : Kˣ) (k : ℕ) :
    blockScalarGL J α β ^ k = blockScalarGL J (α ^ k) (β ^ k) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_blockScalarGL, coe_blockScalarGL, diagonal_pow]
  congr 1
  funext i
  by_cases hi : i ∈ J <;> simp [hi]

theorem blockScalarGL_one (J : Finset (Fin n)) : blockScalarGL J (1 : Kˣ) 1 = 1 := by
  apply Units.ext
  rw [coe_blockScalarGL]
  simp

theorem units_pow_card_sub_one [Finite K] (α : Kˣ) : α ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one _ α.ne_zero

theorem card_sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  refine ⟨q + 1, ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

theorem split_pow_card_sub_one [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {J : Finset (Fin n)} {a b : Fin n} (ha : a ∈ J) (hb : b ∉ J) {y : MulAut (projectiveSL n K)}
    (hy : y ∈ oddCoreIn B (conjAut n K (signGL K J))) : y ^ (Nat.card K - 1) = 1 := by
  obtain ⟨α, β, rfl⟩ := split_oddCoreIn hK hn hinj hB ha hb hy
  rw [← map_pow, blockScalarGL_pow, units_pow_card_sub_one, units_pow_card_sub_one,
    blockScalarGL_one, map_one]

theorem nonsplit_pow_card_sq_sub_one [Finite K] {l : K} (hl : ¬ IsSquare l) {m : ℕ}
    (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (m * 2) K →*
      MulAut (projectiveSL (m * 2) K)))
    {B : Subgroup (MulAut (projectiveSL (m * 2) K))}
    (hB : (MulAut.conj : projectiveSL (m * 2) K →* MulAut (projectiveSL (m * 2) K)).range ≤ B)
    {y : MulAut (projectiveSL (m * 2) K)}
    (hy : y ∈ oddCoreIn B (conjAut (m * 2) K (quadGL l m hl))) :
    y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  obtain ⟨D, x, rfl, hD⟩ := nonsplit_oddCoreIn hl hm hinj hB hy
  have : Module.Finite K (QuadExt l) := (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C l
    two_ne_zero)).finite
  have : Finite (QuadExt l) := Module.finite_of_finite K
  have : Fintype (QuadExt l) := Fintype.ofFinite _
  have : Fintype K := Fintype.ofFinite K
  have hcardE : Fintype.card (QuadExt l) = Nat.card K ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := QuadExt l),
      (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C l two_ne_zero)).finrank,
      ← Nat.card_eq_fintype_card]
    change Nat.card K ^ (quadPoly l).natDegree = Nat.card K ^ 2
    rw [Polynomial.natDegree_X_pow_sub_C]
  have hx : x ≠ 0 := by
    rintro rfl
    have hdet := D.isUnit.map Matrix.detMonoidHom
    rw [Matrix.coe_detMonoidHom, hD, scalar_apply] at hdet
    simp only [diagonal_zero, map_zero] at hdet
    have : Nonempty (Fin (m * 2)) := ⟨⟨0, by omega⟩⟩
    rw [det_zero] at hdet
    exact not_isUnit_zero hdet
  have hxk : x ^ (Nat.card K ^ 2 - 1) = 1 := by
    rw [← hcardE]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  have hDk : D ^ (Nat.card K ^ 2 - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hD, ← map_pow, ← map_pow, hxk, map_one, map_one, Units.val_one]
  rw [← map_pow, hDk, map_one]

theorem inner_pow_eq_one [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (projectiveSL n K)}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : GL (Fin n) K} (htA : ψ t = conjAut n K A)
    {y : X} (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hA2 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← htA, ← map_mul, htt, map_one]
  obtain ⟨-, l, hl⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 hA2
  have hns : ∀ c : Kˣ, A ≠ GeneralLinearGroup.scalar (Fin n) c := by
    intro c hc
    have : ψ t = 1 := by rw [htA, hc, conjAut_scalar]
    have ht1 : t = 1 := hψ (by rw [this, map_one])
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  by_cases hsq : IsSquare (l : K)
  ·
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact l.ne_zero (by rw [hr, mul_zero])
    set μ := Units.mk0 r hr0
    have hAμ : A * A = GeneralLinearGroup.scalar (Fin n) (μ * μ) := by
      rw [← hl]
      congr 1
      exact Units.ext hr
    obtain ⟨H, J, a, b, ha, hb, hH⟩ := exists_split_normal_form hK hAμ hns
    obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut n K H)
    set ψ' := (MulAut.conj (conjAut n K H)).toMonoidHom.comp ψ with hψ'def
    have hψ't : ψ' t = conjAut n K (signGL K J) := by
      change conjAut n K H * ψ t * (conjAut n K H)⁻¹ = _
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hH, map_mul, conjAut_scalar, one_mul]
    have hy' : ψ' y ∈ oddCoreIn ψ'.range (conjAut n K (signGL K J)) := by
      rw [← hψ't, ← map_oddCentralizerCore_of_injective hinj']
      exact ⟨y, hy, rfl⟩
    have h1 := split_pow_card_sub_one hK hn hinj hInn' ha hb hy'
    have h3 : y ^ (Nat.card K - 1) = 1 := hinj' (by rw [map_pow, h1, map_one])
    obtain ⟨c, hc⟩ := card_sub_one_dvd_sq_sub_one (Nat.card K)
    rw [hc, pow_mul, h3, one_pow]
  ·
    have hev := even_of_sq_eq_nonsquare hl.symm hsq
    obtain ⟨m, rfl⟩ : ∃ m, n = m * 2 := ⟨n / 2, by obtain ⟨k, hk⟩ := hev; omega⟩
    have hm : 2 ≤ m := by omega
    have hAm : (A : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * A = (l : K) • 1 := by
      have := congrArg Units.val hl
      rw [Units.val_mul] at this
      rw [← this]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    obtain ⟨H, hH⟩ := exists_quad_normal_form hsq hAm
    have hHGL : H * A * H⁻¹ = quadGL (l : K) m hsq := Units.ext hH
    obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut (m * 2) K H)
    set ψ' := (MulAut.conj (conjAut (m * 2) K H)).toMonoidHom.comp ψ with hψ'def
    have hψ't : ψ' t = conjAut (m * 2) K (quadGL (l : K) m hsq) := by
      change conjAut (m * 2) K H * ψ t * (conjAut (m * 2) K H)⁻¹ = _
      rw [htA, ← map_inv, ← map_mul, ← map_mul, hHGL]
    have hy' : ψ' y ∈ oddCoreIn ψ'.range (conjAut (m * 2) K (quadGL (l : K) m hsq)) := by
      rw [← hψ't, ← map_oddCentralizerCore_of_injective hinj']
      exact ⟨y, hy, rfl⟩
    have h1 := nonsplit_pow_card_sq_sub_one hsq hm hinj hInn' hy'
    exact hinj' (by rw [map_pow, h1, map_one])

theorem pow_eq_one_of_mem_oddCentralizerCore_PSL (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {n p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .PSL n p f) (hn : 3 ≤ n) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  obtain ⟨hp, hf⟩ : p.Prime ∧ 1 ≤ f := by
    rcases hL with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact ⟨h.1, h.2.1⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨K, _, _, hKc, ⟨θ⟩⟩ :=
    LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  set ψ := socleAction θ with hψdef
  have hψ : Function.Injective ψ := socleAction_injective hsimple hnab θ
  have hInn : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ ψ.range := by
    rintro _ ⟨x, rfl⟩
    exact conj_mem_range_socleAction θ x
  have hinj := conj_injective_of_mulEquiv hsimple hnab θ
  have hsq : ψ t ^ 2 = 1 := by rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  have hbot : oddCentralizerCore t = ⊥ → y ^ ((p ^ f) ^ 2 - 1) = 1 := by
    intro h0
    rw [h0, mem_bot] at hy
    rw [hy, one_pow]
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 (ψ t)
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα
      rw [← hKc]
      exact inner_pow_eq_one hK hn hinj hψ hInn ht hα hy
    · exact hbot (field_eq_bot hp hp2 hf hKc hn hinj hψ hInn ht hσ hα le_rfl)
  · rw [pow_one] at hα
    by_cases hσ : σ = 1
    · subst hσ
      have hα' : ψ t = conjAut n K A * dualAut n K := by rw [hα, map_one, mul_one]
      have hsq' : (conjAut n K A * fieldAut n K 1 * dualAut n K) ^ 2 = 1 := by
        rw [← hα]
        exact hsq
      rcases LocalAnalysis.ComponentInitial.OddHigherLinear.transpose_eq_or_eq_neg_of_sq hn A
          hsq' with hA | hA
      · exact hbot (orthogonal_eq_bot hK hn hinj hψ hInn hA hα' le_rfl)
      · refine hbot (eq_bot_of_oddCoreIn hψ ?_ le_rfl)
        rw [hα']
        exact symplectic_oddCoreIn_eq_bot hK hn hinj hInn hA
    · exact hbot (graphField_eq_bot hp hp2 hf hKc hn hinj hψ hInn ht hσ hα le_rfl)

end CFSG.ComponentClassification.Burgoyne.PSL
