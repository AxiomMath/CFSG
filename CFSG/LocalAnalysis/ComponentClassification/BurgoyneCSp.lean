module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCSpSkew
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.C

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.Blueprint
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem psp_propC_false {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) {x : StatedProj (StatedSp r K)}
    {R₁ R₂ : Subgroup (StatedProj (StatedSp r K))} {p m : ℕ} [Fact p.Prime]
    (hC : PropCData x R₁ R₂ p m) : False := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  obtain ⟨A, rfl⟩ := projH_surjective x
  have hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : projH _ A = 1 := (QuotientGroup.eq_one_iff _).2 (by
      rw [mem_subgroupOf]
      exact MonoidHom.mem_range.2 ⟨c, hc.symm⟩)
    have := hC.orderOf_eq
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hx2 : projH _ (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← hC.orderOf_eq, pow_orderOf_eq_one]
  have hsc := (QuotientGroup.eq_one_iff _).1 hx2
  rw [mem_subgroupOf] at hsc
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
  have hconj : ∀ H : StatedSp r K, ∃ R₁' R₂' : Subgroup (StatedProj (StatedSp r K)),
      PropCData (projH _ (H⁻¹ * A * H)) R₁' R₂' p m := by
    intro H
    have hx : (MulAut.conj (projH _ H)⁻¹) (projH _ A) = projH _ (H⁻¹ * A * H) := by
      rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv]
    have h := hC.map (MulAut.conj (projH _ H)⁻¹)
    rw [hx] at h
    exact ⟨_, _, h⟩
  have hmat : ∀ H : StatedSp r K, ((((H⁻¹ * A * H : StatedSp r K) : GL (Fin r ⊕ Fin r) K)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (((H : GL (Fin r ⊕ Fin r) K)⁻¹ :
        GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := fun H => rfl
  rcases hratio with h | h
  ·
    rw [div_eq_iff hd0, one_mul] at h
    rw [← h, one_smul] at hAA
    exact psp_split_false hK hAA hAns hC
  ·
    rw [div_eq_iff hd0, neg_one_mul] at h
    have hd1 : (c : K) = -1 := by linear_combination h
    by_cases hsq : ∃ l : K, l ^ 2 = -1
    · obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        exact one_ne_zero (neg_eq_zero.1 (by rw [← hl]; ring))
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK (A := Ag) hl0
        (by rw [hl, ← hd1]; exact hAA) (by rw [hl, neg_neg, one_smul]; exact hJ)
      obtain ⟨R₁', R₂', hC'⟩ := hconj H
      exact psp_skewSplit_false hK hr hl0 (A := H⁻¹ * A * H) (by rw [hmat]; exact hH) hC'
    · push Not at hsq
      have hsq' : ∀ l : K, l ^ 2 ≠ (c : K) := by rw [hd1]; exact hsq
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) (A := Ag) hAns
        hsq' hAA (by rw [hd1, neg_neg, one_smul]; exact hJ)
      obtain ⟨R₁', R₂', hC'⟩ := hconj H
      exact psp_skewNs_false hℓ hℓ2 hf hKc hr hsq' (A := H⁻¹ * A * H) (by rw [hmat]; exact hH)
        hC'

theorem burgoynePropC_PSp {X : Type} [Group X] [Finite X] (hX : IsM4 X) {n' p' f' : ℕ}
    (hp2' : p' ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .PSp n' p' f') {t : X}
    {R₁ R₂ : Subgroup X} {p n : ℕ} [Fact p.Prime] (hC : PropCData t R₁ R₂ p n) : False := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hout : Group.IsSolvable (OuterAutomorphisms.Outer (GeneralizedFitting.subgroup X)) := by
      have hr : 2 ≤ n' := hc.1.2.2.1
      rcases (show n' = 2 ∨ 3 ≤ n' by omega) with rfl | h3
      · exact (CatalogueBSymplecticTwo.classical_model_two_schreier hc).2
      · exact (classical_model_schreier h3 hc).2
    obtain ⟨⟨hp, hf, hr, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    obtain ⟨x, R₁', R₂', hC', -⟩ := exists_propCData_of_socle hsimple hnab hout θ hC.orderOf_eq
      hC.le₁ hC.comp₁ hC.le₂ hC.comp₂ hC.p_ne_two hC.n_pos hC.iso₁ hC.iso₂ hC.mem
    exact psp_propC_false hp hp2' hf hKc hr hC'
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.C
