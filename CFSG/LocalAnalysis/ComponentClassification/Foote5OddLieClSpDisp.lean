module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpNs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpInner

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

@[expose] def SpFourThreeSkewInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 3 →
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 K) →* MulAut (StatedProj (StatedSp 2 K))) →
    ∀ A : gsp 2 K, (A = stdSkewGsp 2 K ∨
      ∃ (d : K) (hd0 : d ≠ 0), (∀ l : K, l ^ 2 ≠ d) ∧ A = skewNsGsp 2 K hd0) →
    ∀ R : Subgroup (MulAut (StatedProj (StatedSp 2 K))), Odd (Nat.card R) →
      (∀ y ∈ R, y * conjAut 2 K A = conjAut 2 K A * y) →
      (∀ s, conjAut 2 K A s = s → Odd (orderOf s) → ∀ y ∈ R,
        MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) →
      ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

variable {r : ℕ} {K : Type} [Field K] [Finite K]
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

omit [Finite K] in
theorem commute_of_eq_one {G : Type*} [Group G] {H : Subgroup G} (h : ∀ y ∈ H, y = 1) :
    ∀ r₁ ∈ H, ∀ r₂ ∈ H, r₁ * r₂ = r₂ * r₁ := fun r₁ h₁ r₂ h₂ => by rw [h r₁ h₁, h r₂ h₂]

theorem commute_of_transfer (hr : 1 ≤ r) {A A' : gsp r K} (H : StatedSp r K) {c : K} (hc : c ≠ 0)
    (hH : ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        c • ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (h : ∀ R' : Subgroup (MulAut (StatedProj (StatedSp r K))), Odd (Nat.card R') →
      (∀ y ∈ R', y * conjAut r K A' = conjAut r K A' * y) →
      (∀ s, conjAut r K A' s = s → Odd (orderOf s) → ∀ y ∈ R',
        MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R') →
      ∀ r₁ ∈ R', ∀ r₂ ∈ R', r₁ * r₂ = r₂ * r₁)
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * conjAut r K A = conjAut r K A * y)
    (hRc : ∀ s, conjAut r K A s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  set Hg : gsp r K := ⟨H, statedSp_le_gsp H.2⟩ with hHg
  refine commute_of_congr (conjAut r K Hg)⁻¹ (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  have hcg : MulAut.congr (conjAut r K Hg)⁻¹ (conjAut r K A) = conjAut r K A' := by
    rw [congr_eq_conj, inv_inv, ← map_inv, ← map_mul, ← map_mul]
    refine conjAut_eq_of_eq_smul hr hc ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hH
  rw [hcg] at hR'i hR'c
  exact h R' hR'odd hR'i hR'c

theorem commute_inner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (h4 : SpFourThreeSkewInput) {A : gsp r K} (hi : orderOf (conjAut r K A) = 2)
    (hRodd : Odd (Nat.card R)) (hRi : ∀ y ∈ R, y * conjAut r K A = conjAut r K A * y)
    (hRc : ∀ s, conjAut r K A s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hq5 : ℓ ^ f ≠ 3 → 5 ≤ ℓ ^ f := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    omega
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : conjAut r K A = 1 := (conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩
    rw [h1, orderOf_one] at hi
    exact absurd hi (by norm_num)
  have htt : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hi, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) (A * A)).1 (by rw [map_mul, htt])
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
        refine commute_of_transfer (by omega) H (neg_ne_zero.2 hl0)
          (A' := lrInvGsp r K ⟨0, by omega⟩)
          (by rw [neg_smul, ← hH, coe_negGsp, Matrix.mul_neg, Matrix.neg_mul, neg_neg])
          (fun R' hR'odd hR'i hR'c => commute_of_eq_one fun y hy =>
            eq_one_lrInv_three hP.2 hr hinj _ hR'odd hR'i hR'c hy) hRodd hRi hRc
      by_cases hM2 : Module.finrank K (VMl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form hK (by omega) hl0 hAA' hJ' hM2.1
        exact commute_of_transfer (by omega) H hl0 hH
          (fun R' hR'odd hR'i hR'c => commute_of_eq_one fun y hy =>
            eq_one_lrInv_three hM2.2 hr hinj _ hR'odd hR'i hR'c hy) hRodd hRi hRc
      refine commute_of_eq_one fun y hy => eq_one_splitSelf hK hr hinj hAns hl0 hAA' hJ' ?_ ?_
        hRodd hRi hRc hy
      · by_contra h
        push Not at h
        exact hP h
      · by_contra h
        push Not at h
        exact hM2 h
    ·
      have hJ' : Mᵀ * formJ r K * M = (-(l ^ 2)) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA' hJ'
      refine commute_of_transfer (by omega) H hl0 (A' := stdSkewGsp r K) hH
        (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
      by_cases h23 : r = 2 ∧ Nat.card K = 3
      · obtain ⟨rfl, h3⟩ := h23
        exact h4 K h3 hinj _ (Or.inl rfl) R' hR'odd hR'i hR'c
      · refine commute_skewSplit hK hr ?_ hinj hR'odd hR'i hR'c
        by_cases hr3 : 3 ≤ r
        · exact Or.inl hr3
        · right
          have h3 : Nat.card K ≠ 3 := fun h => h23 ⟨by omega, h⟩
          have := hq5 (by rwa [← hKc])
          omega
  · push Not at hsq
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = d • formJ r K := by rw [← hμd]; exact hJμ
      exact commute_nonsplitSelf hℓ hℓ2 hf hKc hr hinj hAns hsq hAA hJ' hRodd hRi hRc
    ·
      have hJ' : Mᵀ * formJ r K * M = (-d) • formJ r K := by rw [← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) hAns hsq hAA hJ'
      refine commute_of_transfer (by omega) H one_ne_zero (A' := skewNsGsp r K hd0)
        (by rw [one_smul, coe_skewNsGsp]; exact hH) (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
      by_cases h23 : r = 2 ∧ Nat.card K = 3
      · obtain ⟨rfl, h3⟩ := h23
        exact h4 K h3 hinj _ (Or.inr ⟨d, hd0, hsq, rfl⟩) R' hR'odd hR'i hR'c
      · refine commute_skewNs hℓ hℓ2 hf hKc hr ?_ hinj hsq hd0 hR'odd hR'i hR'c
        by_cases hr3 : 3 ≤ r
        · exact Or.inl hr3
        · exact Or.inr (hq5 fun h => h23 ⟨by omega, by rw [hKc, h]⟩)

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
