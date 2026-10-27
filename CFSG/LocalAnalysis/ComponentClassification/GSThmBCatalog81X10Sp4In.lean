module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10Sp4Tr
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerH

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4

namespace X10Sp4

variable {K : Type} [Field K]

theorem inner_cases [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (A : gsp 2 K) (d : Kˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (d : K) • 1)
    (hα1 : conjAut 2 K A ≠ 1) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ fixOf (conjAut 2 K A)) (hM : IsPComponent 2 (M.subgroupOf (fixOf (conjAut 2 K A)))) :
    Nonempty (↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∨
      (AllTraces M ∧ IsSimpleGroup M ∧
        Nat.card M * 2 = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)) ∨
      (IsSimpleGroup M ∧ Nat.card M * 2 = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1)) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  have hchar : ringChar K ≠ 2 := GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK
  have h4 : 4 ≤ Nat.card K := by omega
  set Am : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hAm
  set μ := multiplierUnit A with hμdef
  have hμ : Amᵀ * formJ 2 K * Am = (μ : K) • formJ 2 K := multiplierUnit_spec A
  have hdμ : (d : K) = μ ∨ (d : K) = -μ := by
    have e1 : (Am * Am)ᵀ * formJ 2 K * (Am * Am) = ((μ : K) * μ) • formJ 2 K := by
      rw [transpose_mul, show Amᵀ * Amᵀ * formJ 2 K * (Am * Am) =
        Amᵀ * (Amᵀ * formJ 2 K * Am) * Am by simp only [Matrix.mul_assoc], hμ,
        Matrix.mul_smul, Matrix.smul_mul, hμ, smul_smul]
    rw [hAA, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul] at e1
    exact mul_self_eq_mul_self_iff.mp (smul_formJ_injective 2 e1)
  by_cases hsq : ∃ l : K, l ^ 2 = (μ : K)
  ·
    obtain ⟨l, hl⟩ := hsq
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hl
      exact μ.ne_zero hl.symm
    have hA'sp : (l⁻¹ • Am)ᵀ * formJ 2 K * (l⁻¹ • Am) = formJ 2 K := by
      rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
        smul_smul, ← hl]
      rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
    set A' : StatedSp 2 K := toSp (l⁻¹ • Am) hA'sp with hA'def
    have hAz : (A : GL (Fin 2 ⊕ Fin 2) K) =
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
          (A' : GL (Fin 2 ⊕ Fin 2) K) := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
        Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
    have hαu : conjAut 2 K A = MulAut.conj (proj 2 K A') :=
      conjAut_eq_conj_of_scalar_mul A _ A' hAz
    set u := proj 2 K A' with hudef
    have hu1 : u ≠ 1 := fun h => hα1 (by rw [hαu, h, map_one])
    have hu2 : u * u = 1 := by
      have hs : A' * A' ∈ spScalars 2 K := by
        have hm : ((A' * A' : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
            ((l⁻¹ * l⁻¹ * (d : K)) • 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
          rw [Subgroup.coe_mul, Units.val_mul, hA'def, coe_toSp, Matrix.smul_mul,
            Matrix.mul_smul, hAA, smul_smul, smul_smul]
        have hsp := symplectic_of_mem (A' * A')
        rw [hm, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
          Matrix.mul_one, smul_smul] at hsp
        have hc : (l⁻¹ * l⁻¹ * (d : K)) * (l⁻¹ * l⁻¹ * (d : K)) = 1 :=
          smul_formJ_injective 2 (hsp.trans (one_smul K (formJ 2 K)).symm)
        rw [mem_spScalars_iff, hm]
        rcases mul_self_eq_one_iff.mp hc with hc1 | hc1
        · left
          rw [hc1, one_smul]
        · right
          rw [hc1, neg_one_smul]
      rw [hudef, ← map_mul, ← MonoidHom.mem_ker, ker_proj]
      exact hs
    have hu : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
    obtain ⟨φ, hφ⟩ := exists_model_conj hodd hu
    have hcomm : ∀ x, φ (MulAut.conj u x) = MulAut.conj (φ u) (φ x) := fun x => by
      simp only [MulAut.conj_apply, map_mul, map_inv]
    rw [hαu] at hMX hM
    obtain ⟨hM'X, hM'⟩ := isPComponent_map_fixOf hcomm hMX hM
    rw [fixOf_conj] at hM'X hM'
    have hMφ : (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id M
      ext x
      simp
    have hcardM : Nat.card ↥(M.map φ.toMonoidHom) = Nat.card M :=
      (Nat.card_congr (M.equivMapOfInjective _ φ.injective).toEquiv).symm
    rcases hφ with h | h <;> rw [h] at hM'X hM'
    · left
      obtain ⟨hE | hE, -⟩ := pComponent_centralizer_u1 hodd hM'X hM'
      · exact ⟨(M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
          ((MulEquiv.subgroupCongr hE).trans (E1Equiv h2).symm)⟩
      · exact ⟨(M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
          ((MulEquiv.subgroupCongr hE).trans (E2Equiv h2).symm)⟩
    · right; left
      obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hM'X hM'
      refine ⟨?_, ?_, ?_⟩
      · rw [← hMφ, hL]
        exact allTraces_map hchar allTraces_Lsub φ.symm
      · have : IsSimpleGroup ↥(M.map φ.toMonoidHom) := hL ▸ isSimpleGroup_Lsub h4
        exact (M.equivMapOfInjective φ.toMonoidHom φ.injective).isSimpleGroup
      · rw [← hcardM, hL, card_Lsub hodd, card_SL2]
        exact (Nat.mul_comm _ _).trans (two_mul_ordL2 hodd)
  · push Not at hsq
    rcases hdμ with hdm | hdm
    ·
      right; right
      have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
      have hμd : Amᵀ * formJ 2 K * Am = (d : K) • formJ 2 K := by rw [hdm]; exact hμ
      obtain ⟨hQ, hcard⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
      have hθα : ∀ g, conjAut 2 K A (proj 2 K g) = proj 2 K (conjSp 2 K A g) :=
        fun g => conjAut_proj A g
      have hZ : ∀ z ∈ spScalars 2 K, conjSp 2 K A z = z := fun z hz => conjSp_scalar A hz
      rw [eq_map_fixOf_of_isPComponent _ hθα hQ hMX hM]
      exact ⟨isSimpleGroup_map_fixOf h2 _ hZ hQ
        (card_center_fixOf_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd),
        by rw [card_map_fixOf_mul_two h2 _ hZ, hcard]⟩
    ·
      right; left
      have ha : (d : K) ≠ 0 := d.ne_zero
      have hA : Amᵀ * formJ 2 K * Am = (-(d : K)) • formJ 2 K := by rw [hμ, hdm, neg_neg]
      obtain ⟨g, hg⟩ := exists_frame_typeI h2 ha hA hAA
      have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
          (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, coe_aIgsp]
        exact hg
      set ψ := (MulAut.conj (proj 2 K g))⁻¹ with hψ
      have hcomm : ∀ x, ψ (conjAut 2 K A x) = alphaI ha (ψ x) := fun x =>
        conj_inv_conjAut A (aIgsp ha) g hGL x
      obtain ⟨hM'X, hM'⟩ := isPComponent_map_fixOf (β := ψ) hcomm hMX hM
      have hJ := pComponent_fix_alphaI ha h2 h4 hM'X hM'
      have hMψ : (M.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = M := by
        rw [Subgroup.map_map]
        convert Subgroup.map_id M
        ext x
        simp
      refine ⟨?_, ?_, ?_⟩
      · rw [← hMψ, hJ]
        exact allTraces_map hchar (allTraces_JI ha) ψ.symm
      · have : IsSimpleGroup ↥(M.map ψ.toMonoidHom) := hJ ▸ isSimpleGroup_JI ha h4
        exact (M.equivMapOfInjective ψ.toMonoidHom ψ.injective).isSimpleGroup
      · rw [← (Nat.card_congr (M.equivMapOfInjective ψ.toMonoidHom ψ.injective).toEquiv).symm,
          hJ, card_JI hodd ha, card_SL2]
        exact (Nat.mul_comm _ _).trans (two_mul_ordL2 hodd)

end X10Sp4

end CFSG.ComponentClassification.GSThmB
