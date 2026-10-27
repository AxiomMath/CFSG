module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieS4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieS6c
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.CatLeafProof.EndOddCore CFSG.ComponentClassification.FooteLit

variable {r : ℕ} {K : Type} [Field K]

theorem false_of_config_psp [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) {z : StatedProj (StatedSp r K)}
    {L D : Subgroup (StatedProj (StatedSp r K))} (h : Config z L D) : False := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have hodd : Odd (Nat.card K) := by rw [hKc]; exact (hℓ.odd_of_ne_two hℓ2).pow
  rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
  · exact false_of_config_psp4 hodd h
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  set Z := (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) with hZ
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective Z z
  have hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : QuotientGroup.mk' Z A = 1 := (QuotientGroup.eq_one_iff _).2 (by
      rw [hZ, mem_subgroupOf]
      exact MonoidHom.mem_range.2 ⟨c, hc.symm⟩)
    have := h.twoComp.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hx2 : QuotientGroup.mk' Z (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← h.twoComp.1, pow_orderOf_eq_one]
  have hsc := (QuotientGroup.eq_one_iff _).1 hx2
  rw [hZ, mem_subgroupOf] at hsc
  obtain ⟨c, hc⟩ := hsc
  have hd0 : (c : K) ≠ 0 := c.ne_zero
  set Ag : gsp r K := ⟨A, statedSp_le_gsp A.2⟩ with hAg
  have hAA : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [Matrix.smul_one_eq_diagonal]
    exact this.symm
  have hJ : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      formJ r K := mem_statedSp_iff.1 A.2
  have hJ1 : ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ *
      formJ r K * ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (1 : K) • formJ r K := by rw [one_smul]; exact hJ
  have hAμ : ∀ v w, pairedSympForm K r (((linA Ag : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = 1 * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJ1]
  have hratio := UnitaryHigher.multiplier_ratio SymplecticFlag.pairedSympForm_nondegenerate hd0
    (linA_mul_self hAA) hAμ
  have hconj : ∀ H : StatedSp r K, ∃ L' D' : Subgroup (StatedProj (StatedSp r K)),
      Config (QuotientGroup.mk' Z (H⁻¹ * A * H)) L' D' := by
    intro H
    have hx : (MulAut.conj (QuotientGroup.mk' Z H)⁻¹) (QuotientGroup.mk' Z A) =
        QuotientGroup.mk' Z (H⁻¹ * A * H) := by
      rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
    have h' := h.map (MulAut.conj (QuotientGroup.mk' Z H)⁻¹)
    rw [hx] at h'
    exact ⟨_, _, h'⟩
  have hmat : ∀ H : StatedSp r K, ((((H⁻¹ * A * H : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (((H : GL (Fin r ⊕ Fin r) K)⁻¹ :
        GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := fun H => rfl
  rcases hratio with hq | hq
  ·
    rw [div_eq_iff hd0, one_mul] at hq
    rw [← hq, one_smul] at hAA
    exact false_of_config_split hK hr3 hAA hAns h
  ·
    rw [div_eq_iff hd0, neg_one_mul] at hq
    have hd1 : (c : K) = -1 := by linear_combination hq
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    · obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        exact one_ne_zero (neg_eq_zero.1 (by rw [← hl]; ring))
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK (A := Ag) hl0
        (by rw [hl, ← hd1]; exact hAA) (by rw [hl, neg_neg, one_smul]; exact hJ)
      obtain ⟨L', D', hC'⟩ := hconj H
      exact false_of_config_skewSplit hK hr3 hl0 (A := H⁻¹ * A * H) (by rw [hmat]; exact hH) hC'
    · push Not at hsq
      have hsq' : ∀ l : K, l ^ 2 ≠ (c : K) := by rw [hd1]; exact hsq
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) (A := Ag) hAns
        hsq' hAA (by rw [hd1, neg_neg, one_smul]; exact hJ)
      obtain ⟨L', D', hC'⟩ := hconj H
      exact false_of_config_skewNs hℓ hℓ2 hf hKc hr3 hsq (A := H⁻¹ * A * H)
        (by rw [hmat, hH, hd1]) hC'

theorem endOddLieInputFor_PSp : Sol78.F514.EndOddLieInputFor {.PSp} := by
  refine endOddLieInputFor_of_config {.PSp} ?_
  intro X _ _ _ τ n p f hτ hp hp2 _ hmod z L D h
  rw [Finset.mem_singleton] at hτ
  subst hτ
  rcases hmod with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨-, hf, hr, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    exact false_of_config_psp hp hp2 hf hKc hr (h.map θ)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.CatLeafProof.EndOddSp
