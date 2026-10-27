module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3ThetaPSU
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.Blueprint
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem pow_card_sq_sub_one_of_mul_self [Finite K] {A : Type*} [Ring A] [Algebra K A] {l : K}
    (hl : ¬ IsSquare l) {N : A} (hN : N * N = l • 1) {p s : K}
    (hx : p • (1 : A) + s • N ≠ 0) : (p • (1 : A) + s • N) ^ (Nat.card K ^ 2 - 1) = 1 := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  have hNp : Polynomial.aeval N (quadPoly l) = 0 := by
    rw [quadPoly, map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, pow_two, hN,
      Algebra.algebraMap_eq_smul_one, sub_self]
  set φ : QuadExt l →ₐ[K] A :=
    Ideal.Quotient.liftₐ (Ideal.span {quadPoly l}) (Polynomial.aeval N) fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hNp, mul_zero] with hφ
  have hφr : φ (AdjoinRoot.root (quadPoly l)) = N := by
    show φ (AdjoinRoot.mk (quadPoly l) Polynomial.X) = N
    exact Polynomial.aeval_X N
  set z : QuadExt l := algebraMap K _ p + algebraMap K _ s * AdjoinRoot.root (quadPoly l)
    with hz
  have hφz : φ z = p • 1 + s • N := by
    rw [hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hφr,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hφz
    exact hx hφz.symm
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
  have hzk : z ^ (Nat.card K ^ 2 - 1) = 1 := by
    rw [← hcardE]
    exact FiniteField.pow_card_sub_one_eq_one z hz0
  rw [← hφz, ← map_pow, hzk, map_one]

variable {r : ℕ}

theorem skewSplit_pow_card_sub_one [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (h4 : 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {y : MulAut (StatedProj (StatedSp r K))}
    (hy : y ∈ oddCoreIn B (conjAut r K (stdSkewGsp r K))) : y ^ (Nat.card K - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨D, a, b, rfl, hD⟩ := skewSplit_oddCore hK hr (Or.inr h4) hinj hB hy
  have : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  have hdet := (D : GL (Fin r ⊕ Fin r) K).isUnit.map Matrix.detMonoidHom
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal] at hdet
  have hr0 : r ≠ 0 := by omega
  have ha : a ≠ 0 := by
    rintro rfl
    apply not_isUnit_zero (M₀ := K)
    convert hdet using 1
    rw [Fintype.prod_sum_type]
    simp [hr0]
  have hb : b ≠ 0 := by
    rintro rfl
    apply not_isUnit_zero (M₀ := K)
    convert hdet using 1
    rw [Fintype.prod_sum_type]
    simp [hr0]
  have hDk : D ^ (Nat.card K - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, diagonal_pow, Subgroup.coe_one,
      Units.val_one, ← diagonal_one]
    congr 1
    funext i
    rw [Pi.pow_apply, Nat.card_eq_fintype_card]
    rcases i with i | i
    · exact FiniteField.pow_card_sub_one_eq_one _ ha
    · exact FiniteField.pow_card_sub_one_eq_one _ hb
  rw [← map_pow, hDk, map_one]

theorem skewNs_pow_card_sq_sub_one [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hq5 : 5 ≤ ℓ ^ f)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) {y : MulAut (StatedProj (StatedSp r K))}
    (hy : y ∈ oddCoreIn B (conjAut r K (skewNsGsp r K hd0))) :
    y ^ (Nat.card K ^ 2 - 1) = 1 := by
  obtain ⟨D, p, s, rfl, hD⟩ := skewNs_oddCore hℓ hℓ2 hf hKc hr (Or.inr hq5) hinj hB hd hd0 hy
  have hl : ¬ IsSquare d := by
    rintro ⟨c, hc⟩
    exact hd c (by rw [hc, sq])
  have hx : p • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + s • skewNs r K d ≠ 0 := by
    intro h0
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    have hdet := (D : GL (Fin r ⊕ Fin r) K).isUnit.map Matrix.detMonoidHom
    rw [Matrix.coe_detMonoidHom, hD, h0, det_zero] at hdet
    exact not_isUnit_zero hdet
  have hDk : D ^ (Nat.card K ^ 2 - 1) = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hD, Subgroup.coe_one, Units.val_one]
    exact pow_card_sq_sub_one_of_mul_self hl (skewNs_mul_self d) hx
  rw [← map_pow, hDk, map_one]

theorem inner_pow_eq_one_Sp [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp r K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : gsp r K} (htA : ψ t = conjAut r K A) {y : X}
    (hy : y ∈ oddCentralizerCore t) : y ^ (Nat.card K ^ 2 - 1) = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq5 : ℓ ^ f ≠ 3 → 5 ≤ ℓ ^ f := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    have := hℓ.two_le
    have : 3 ≤ ℓ ^ f := le_trans (by omega) (Nat.le_self_pow (by omega) ℓ)
    omega
  have hbot' : oddCentralizerCore t = ⊥ → y ^ (Nat.card K ^ 2 - 1) = 1 := by
    intro h0
    rw [h0, mem_bot] at hy
    rw [hy, one_pow]
  have hdvd : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := card_sub_one_dvd_sq_sub_one _
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : conjAut r K A = 1 := (conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩
    have ht1 : t = 1 := hψ (by rw [htA, h1, map_one])
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htt : ψ t * ψ t = 1 := by
    rw [← map_mul, ← pow_two, ← ht, pow_orderOf_eq_one, map_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) (A * A)).1 (by rw [map_mul, ← htA, htt])
  set d : K := (c : K) with hd
  have hd0 : d ≠ 0 := c.ne_zero
  have hAA : M * M = d • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  set μ : K := (multiplier r K A : K) with hμ
  have hJμ : Mᵀ * formJ r K * M = μ • formJ r K := multiplier_spec A
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = μ * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJμ]
  have hratio := UnitaryHigher.multiplier_ratio SymplecticFlag.pairedSympForm_nondegenerate hd0
    (linA_mul_self hAA) hAμ
  have hμd : μ = d ∨ μ = -d := by
    rcases hratio with h | h
    · left
      field_simp at h
      exact h
    · right
      field_simp at h
      linear_combination h
  have hbot : oddCoreIn ψ.range (conjAut r K A) = ⊥ → y ^ (Nat.card K ^ 2 - 1) = 1 :=
    fun h => hbot' (eq_bot_of_oddCoreIn hψ (by rw [htA]; exact h) le_rfl)
  by_cases hsq : ∃ l : K, l ^ 2 = d
  · obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hd0 (by rw [← hl]; ring)
    have hAA' : M * M = (l ^ 2) • 1 := by rw [hl]; exact hAA
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = (l ^ 2) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      by_cases hP : Module.finrank K (VPl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form (A := negGsp A) (l := l) hK
          (by omega) hl0 (by rw [coe_negGsp, Matrix.neg_mul, Matrix.mul_neg, neg_neg]; exact hAA')
          (by rw [coe_negGsp, transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg,
            neg_neg]; exact hJ')
          (by rw [VMl_negGsp A hl0]; exact hP.1)
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H
          (neg_ne_zero.2 hl0) (A' := lrInvGsp r K ⟨0, by omega⟩)
          (by rw [neg_smul, ← hH, coe_negGsp, Matrix.mul_neg, Matrix.neg_mul, neg_neg])
        refine hbot' (eq_bot_of_oddCoreIn hinj' ?_ le_rfl)
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hP.2 hr hinj hInn' _
      by_cases hM2 : Module.finrank K (VMl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form hK (by omega) hl0 hAA' hJ' hM2.1
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H hl0 hH
        refine hbot' (eq_bot_of_oddCoreIn hinj' ?_ le_rfl)
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hM2.2 hr hinj hInn' _
      refine hbot (splitSelf_oddCoreIn_eq_bot hK hr hinj hInn hAns hl0 hAA' hJ' ?_ ?_)
      · by_contra h
        push Not at h
        exact hP h
      · by_contra h
        push Not at h
        exact hM2 h
    ·
      have hJ' : Mᵀ * formJ r K * M = (-(l ^ 2)) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA' hJ'
      obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H hl0
        (A' := stdSkewGsp r K) hH
      by_cases h3 : Nat.card K = 3
      · refine hbot' (eq_bot_of_oddCoreIn hinj' ?_ le_rfl)
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewSplit_oddCoreIn_eq_bot_two_three h3 hInn'
        · exact skewSplit_oddCoreIn_eq_bot_three h3 hr3 hinj hInn'
      · have h4 : 4 ≤ Nat.card K := by have := hq5 (by rwa [← hKc]); omega
        have h1 : y ^ (Nat.card K - 1) = 1 := by
          refine pow_eq_one_of_transfer hinj' (fun y' hy' => ?_) hy
          rw [hψ't] at hy'
          exact skewSplit_pow_card_sub_one hK hr h4 hinj hInn' hy'
        obtain ⟨e, he⟩ := hdvd
        rw [he, pow_mul, h1, one_pow]
  · push Not at hsq
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = d • formJ r K := by rw [← hμd]; exact hJμ
      exact hbot (nonsplitSelf_oddCoreIn_eq_bot hℓ hℓ2 hf hKc hr hinj hInn hAns hsq hAA hJ')
    ·
      have hJ' : Mᵀ * formJ r K * M = (-d) • formJ r K := by rw [← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) hAns hsq hAA hJ'
      obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H one_ne_zero
        (A' := skewNsGsp r K hd0) (by rw [one_smul, coe_skewNsGsp]; exact hH)
      by_cases h3 : Nat.card K = 3
      · refine hbot' (eq_bot_of_oddCoreIn hinj' ?_ le_rfl)
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewNs_oddCoreIn_eq_bot_two_three h3 hInn' hsq hd0
        · exact skewNs_oddCoreIn_eq_bot_three h3 hr3 hinj hInn' hsq hd0
      · refine pow_eq_one_of_transfer hinj' (fun y' hy' => ?_) hy
        rw [hψ't] at hy'
        exact skewNs_pow_card_sq_sub_one hℓ hℓ2 hf hKc hr (hq5 (by rwa [← hKc])) hinj hInn' hsq
          hd0 hy'

theorem pow_eq_one_of_mem_oddCentralizerCore_PSp (X : Type) [Group X] [Finite X]
    (hsimple : IsSimpleGroup (GeneralizedFitting.subgroup X))
    (hnab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a) {r p f : ℕ} (hp2 : p ≠ 2)
    (hL : LieModel (GeneralizedFitting.subgroup X) .PSp r p f) (t : X)
    (ht : orderOf t = 2) {y : X} (hy : y ∈ oddCentralizerCore t) :
    y ^ ((p ^ f) ^ 2 - 1) = 1 := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, hr, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have hψ := socleAction_injective hsimple hnab θ
    have hInn : (MulAut.conj : StatedProj (StatedSp r K) →*
        MulAut (StatedProj (StatedSp r K))).range ≤ (socleAction θ).range := by
      rintro _ ⟨x, rfl⟩
      exact conj_mem_range_socleAction θ x
    have hinj := conj_injective_of_mulEquiv hsimple hnab θ
    obtain ⟨A, τ, hα⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr
      (socleAction θ t)
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hα
      rw [← hKc]
      exact inner_pow_eq_one_Sp hp hp2 hf hKc hr hinj hψ hInn ht hα hy
    · have h0 := field_eq_bot hp hp2 hf hKc hr hinj hψ hInn ht hτ hα le_rfl
      rw [h0, mem_bot] at hy
      rw [hy, one_pow]
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.Sp
