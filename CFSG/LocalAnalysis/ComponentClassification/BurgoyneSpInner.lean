module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelfNormal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewE
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewFour

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

@[expose] def negGsp (A : gsp r K) : gsp r K :=
  ⟨-(A : GL (Fin r ⊕ Fin r) K), by
    obtain ⟨μ, hμ⟩ := A.2
    exact ⟨μ, by rw [Units.val_neg, transpose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, hμ]⟩⟩

theorem coe_negGsp (A : gsp r K) :
    ((negGsp A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      -((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  Units.val_neg _

theorem VMl_negGsp (A : gsp r K) {l : K} (hl0 : l ≠ 0) : VMl (negGsp A) l = VPl A l := by
  ext v
  rw [mem_eigenMinus hl0, mem_eigenPlus hl0, coe_negGsp, neg_mulVec, neg_smul, neg_inj]

theorem exists_conj_transfer [Finite K] (hr : 1 ≤ r) {X : Type} [Group X]
    {ψ : X →* MulAut (StatedProj (StatedSp r K))} (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} {A A' : gsp r K} (htA : ψ t = conjAut r K A) (H : StatedSp r K) {c : K} (hc : c ≠ 0)
    (hH : ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        c • ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    ∃ ψ' : X →* MulAut (StatedProj (StatedSp r K)), Function.Injective ψ' ∧
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
        ψ'.range ∧ ψ' t = conjAut r K A' := by
  set Hg : gsp r K := ⟨H, statedSp_le_gsp H.2⟩ with hHg
  obtain ⟨hinj', hInn'⟩ := conj_embedding hψ hInn (conjAut r K Hg⁻¹)
  refine ⟨_, hinj', hInn', ?_⟩
  change conjAut r K Hg⁻¹ * ψ t * (conjAut r K Hg⁻¹)⁻¹ = _
  rw [htA, ← map_inv, inv_inv, ← map_mul, ← map_mul]
  refine conjAut_eq_of_eq_smul hr hc ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
  exact hH

theorem propAConclusion_of_transfer {X : Type} [Group X] [Finite X]
    {ψ' : X →* MulAut (StatedProj (StatedSp r K))} (hinj' : Function.Injective ψ') {t : X}
    {Y : Subgroup X} (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t)
    (h : ∀ Y' : Subgroup (MulAut (StatedProj (StatedSp r K))), Y' ≠ ⊥ →
      Y' ≤ oddCoreIn ψ'.range (ψ' t) → PropAConclusionIn ψ'.range (ψ' t) Y') :
    PropAConclusion X t Y := by
  apply PropAConclusion.of_injective hinj'
  refine h _ (fun hmap => hY ((map_eq_bot_iff_of_injective _ hinj').1 hmap)) ?_
  rw [← map_oddCentralizerCore_of_injective hinj']
  exact map_mono hYO

theorem inner_propAConclusion_Sp [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {X : Type} [Group X] [Finite X] {ψ : X →* MulAut (StatedProj (StatedSp r K))}
    (hψ : Function.Injective ψ)
    (hInn : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range
      ≤ ψ.range)
    {t : X} (ht : orderOf t = 2) {A : gsp r K} (htA : ψ t = conjAut r K A) {Y : Subgroup X}
    (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) : PropAConclusion X t Y := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  have hq3 : 3 ≤ ℓ ^ f := by
    have := hℓ.two_le
    have : 3 ≤ ℓ := by omega
    exact this.trans (Nat.le_self_pow (by omega) ℓ)
  have hqodd : Odd (ℓ ^ f) := (hℓ.odd_of_ne_two hℓ2).pow
  have hq5 : ℓ ^ f ≠ 3 → 5 ≤ ℓ ^ f := fun h => by
    obtain ⟨k, hk⟩ := hqodd
    omega
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
  have hbot : oddCoreIn ψ.range (conjAut r K A) = ⊥ → PropAConclusion X t Y := fun h =>
    absurd (eq_bot_of_oddCoreIn hψ (by rw [htA]; exact h) hYO) hY
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
        refine absurd (eq_bot_of_oddCoreIn hinj' ?_ hYO) hY
        rw [hψ't]
        exact lrInv_oddCoreIn_eq_bot_three hP.2 hr hinj hInn' _
      by_cases hM2 : Module.finrank K (VMl A l) = 2 ∧ Nat.card K = 3
      · obtain ⟨H, hH⟩ := exists_split_self_lrInv_normal_form hK (by omega) hl0 hAA' hJ' hM2.1
        obtain ⟨ψ', hinj', hInn', hψ't⟩ := exists_conj_transfer (by omega) hψ hInn htA H hl0 hH
        refine absurd (eq_bot_of_oddCoreIn hinj' ?_ hYO) hY
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
      · refine absurd (eq_bot_of_oddCoreIn hinj' ?_ hYO) hY
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewSplit_oddCoreIn_eq_bot_two_three h3 hInn'
        · exact skewSplit_oddCoreIn_eq_bot_three h3 hr3 hinj hInn'
      · refine propAConclusion_of_transfer hinj' hY hYO fun Y' hY' hY'O => ?_
        rw [hψ't] at hY'O ⊢
        exact skewSplit_propAConclusionIn hK hr (by have := hq5 (by rwa [← hKc]); omega) hinj
          hInn' hY' hY'O
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
      · refine absurd (eq_bot_of_oddCoreIn hinj' ?_ hYO) hY
        rw [hψ't]
        rcases Nat.lt_or_ge r 3 with hr3 | hr3
        · obtain rfl : r = 2 := by omega
          exact skewNs_oddCoreIn_eq_bot_two_three h3 hInn' hsq hd0
        · exact skewNs_oddCoreIn_eq_bot_three h3 hr3 hinj hInn' hsq hd0
      · refine propAConclusion_of_transfer hinj' hY hYO fun Y' hY' hY'O => ?_
        rw [hψ't] at hY'O ⊢
        exact skewNs_propAConclusionIn hℓ hℓ2 hf hKc hr (hq5 (by rwa [← hKc])) hinj hInn' hsq hd0
          hY' hY'O

end CFSG.ComponentClassification.Burgoyne.Sp
