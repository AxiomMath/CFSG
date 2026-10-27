module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSp

public section

namespace CFSG.ComponentClassification.GSThmB.X10Sp4.TwoL5

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem inner_unique [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (h5 : 5 ≤ p ^ f) (A : gsp 2 K) (d : Kˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (d : K) • 1)
    (hα1 : conjAut 2 K A ≠ 1) {M₁ M₂ : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX₁ : M₁ ≤ fixOf (conjAut 2 K A))
    (hM₁ : IsPComponent 2 (M₁.subgroupOf (fixOf (conjAut 2 K A))))
    (hMX₂ : M₂ ≤ fixOf (conjAut 2 K A))
    (hM₂ : IsPComponent 2 (M₂.subgroupOf (fixOf (conjAut 2 K A))))
    (hn₁ : ¬ Nonempty (↥M₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (hn₂ : ¬ Nonempty (↥M₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : M₁ = M₂ := by
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
    have key : ∀ {M : Subgroup (StatedProj (StatedSp 2 K))}, M ≤ fixOf (conjAut 2 K A) →
        IsPComponent 2 (M.subgroupOf (fixOf (conjAut 2 K A))) →
        ¬ Nonempty (↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) →
        M = (Lsub K).map φ.symm.toMonoidHom := by
      intro M hMX hM hno
      rw [hαu] at hMX hM
      obtain ⟨hM'X, hM'⟩ := isPComponent_map_fixOf hcomm hMX hM
      rw [fixOf_conj] at hM'X hM'
      have hMφ : (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
        rw [Subgroup.map_map]
        convert Subgroup.map_id M
        ext x
        simp
      rcases hφ with h | h <;> rw [h] at hM'X hM'
      · exfalso
        apply hno
        obtain ⟨hE | hE, -⟩ := pComponent_centralizer_u1 hodd hM'X hM'
        · exact ⟨(M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
            ((MulEquiv.subgroupCongr hE).trans (E1Equiv h2).symm)⟩
        · exact ⟨(M.equivMapOfInjective φ.toMonoidHom φ.injective).trans
            ((MulEquiv.subgroupCongr hE).trans (E2Equiv h2).symm)⟩
      · obtain ⟨hL, -⟩ := pComponent_centralizer_u2 hodd hM'X hM'
        rw [← hMφ, hL]
    exact (key hMX₁ hM₁ hn₁).trans (key hMX₂ hM₂ hn₂).symm
  · push Not at hsq
    rcases hdμ with hdm | hdm
    ·
      have hdsq : ∀ l : K, l ^ 2 ≠ (d : K) := by rw [hdm]; exact hsq
      have hμd : Amᵀ * formJ 2 K * Am = (d : K) • formJ 2 K := by rw [hdm]; exact hμ
      obtain ⟨hQ, -⟩ := fixOf_conjSp_nonsquare hp hp2 hf hK A d.ne_zero hdsq hAA hμd
      have hθα : ∀ g, conjAut 2 K A (proj 2 K g) = proj 2 K (conjSp 2 K A g) :=
        fun g => conjAut_proj A g
      exact (eq_map_fixOf_of_isPComponent _ hθα hQ hMX₁ hM₁).trans
        (eq_map_fixOf_of_isPComponent _ hθα hQ hMX₂ hM₂).symm
    ·
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
      have key : ∀ {M : Subgroup (StatedProj (StatedSp 2 K))}, M ≤ fixOf (conjAut 2 K A) →
          IsPComponent 2 (M.subgroupOf (fixOf (conjAut 2 K A))) →
          M = (JI ha).map ψ.symm.toMonoidHom := by
        intro M hMX hM
        obtain ⟨hM'X, hM'⟩ := isPComponent_map_fixOf (β := ψ) hcomm hMX hM
        have hJ := pComponent_fix_alphaI ha h2 h4 hM'X hM'
        have hMψ : (M.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = M := by
          rw [Subgroup.map_map]
          convert Subgroup.map_id M
          ext x
          simp
        rw [← hMψ, hJ]
      exact (key hMX₁ hM₁).trans (key hMX₂ hM₂).symm

theorem psp4_unique [Finite K] (hK : Nat.card K = 5)
    {α : MulAut (StatedProj (StatedSp 2 K))} (hα2 : α * α = 1) (hα1 : α ≠ 1)
    {M₁ M₂ : Subgroup (StatedProj (StatedSp 2 K))} (hMX₁ : M₁ ≤ fixOf α)
    (hM₁ : IsPComponent 2 (M₁.subgroupOf (fixOf α))) (hMX₂ : M₂ ≤ fixOf α)
    (hM₂ : IsPComponent 2 (M₂.subgroupOf (fixOf α)))
    (hn₁ : ¬ Nonempty (↥M₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K))
    (hn₂ : ¬ Nonempty (↥M₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K)) : M₁ = M₂ := by
  have hK1 : Nat.card K = 5 ^ 1 := by rw [hK]; norm_num
  have hchar : ringChar K ≠ 2 :=
    GH74.Generic.ringChar_ne_two_of_card_eq Nat.prime_five (by norm_num) hK1
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hchar le_rfl).2.2 α hα2 hα1
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hα
    subst hα
    exact inner_unique Nat.prime_five (by norm_num) le_rfl hK1 (by norm_num) A d
      (mul_self_of_rep A d hd) hα1 hMX₁ hM₁ hMX₂ hM₂ hn₁ hn₂
  · exfalso
    obtain ⟨hKk, -⟩ := hfield hσ
    rw [hK] at hKk
    obtain ⟨k, hk⟩ : ∃ k, k = Nat.card {c : K // σ c = c} := ⟨_, rfl⟩
    rw [← hk] at hKk
    have hk3 : k < 3 := by nlinarith
    interval_cases k <;> simp at hKk

end CFSG.ComponentClassification.GSThmB.X10Sp4.TwoL5

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SolMax.FiveCat

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem fiveTwoLayer_char5_PSp : FiveTwoLayerCharFiveClause .PSp := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  have hadm : StatedLieAdmissible .PSp n 5 f := hm.admissible
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hf1 : 1 ≤ f := hadm.2.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psp_of_lieModel' hadm hm
  have : IsSimpleGroup S := hs
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσ2 : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hcβ : ∀ (β : MulAut S) x, e (β x) = MulAut.congr e β (e x) := fun β x => by
    simp [MulAut.congr_apply]
  have hα2 : MulAut.congr e σ * MulAut.congr e σ = 1 := by rw [← map_mul, hσ2, map_one]
  have hα1 : MulAut.congr e σ ≠ 1 := fun h =>
    hσ1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  have htr : ∀ {P : Subgroup S}, ProperFixedComponent σ P →
      Open.fusionZStar ↥P = pPrimeCore 2 ↥P →
      Nonempty (↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin 5)) →
      P.map e.toMonoidHom ≤ CatFactsSp4.fixOf (MulAut.congr e σ) ∧
        IsPComponent 2 ((P.map e.toMonoidHom).subgroupOf (CatFactsSp4.fixOf (MulAut.congr e σ))) ∧
        Nonempty (↥(P.map e.toMonoidHom) ⧸ pPrimeCore 2 ↥(P.map e.toMonoidHom) ≃*
          alternatingGroup (Fin 5)) := by
    intro P hP hZ eP
    obtain ⟨-, hPF, hPp, -⟩ := hP
    obtain ⟨hM0, hM⟩ := CatFactsSp4.isPComponent_map_fixOf (hcβ σ) hPF hPp
    obtain ⟨eP⟩ := eP
    let eM : P ≃* P.map e.toMonoidHom := P.equivMapOfInjective e.toMonoidHom e.injective
    exact ⟨hM0, hM, ⟨(CatalogueBAlternating.primeCoreQuotientEquiv 2 eM).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans eP)⟩⟩
  obtain ⟨hM0₁, hM₁, hAM₁⟩ := htr h₁ hZ₁ e₁
  obtain ⟨hM0₂, hM₂, hAM₂⟩ := htr h₂ hZ₂ e₂
  have hnf : n = 2 ∧ f = 1 := by
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · obtain rfl : n = 2 := by omega
      exact ⟨rfl, PSpFive.psp4_f hf1 hK hα2 hα1 hM0₁ hM₁ hAM₁⟩
    · exfalso
      obtain ⟨eAM⟩ := hAM₁
      exact PSpFive.false_of_a5_high hK hadm hge hα2 hα1 hM₁
        ⟨(CatalogueBAlternating.primeCoreQuotientEquiv 2
          (Subgroup.subgroupOfEquivOfLe hM0₁)).trans eAM⟩
  obtain ⟨rfl, rfl⟩ := hnf
  have hK5 : Nat.card K = 5 := by rw [hK]; norm_num
  have hnotSL : ∀ {M : Subgroup (StatedProj (StatedSp 2 K))},
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 5)) →
      ¬ Nonempty (↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro M hAM hSL
    obtain ⟨eA⟩ := hAM
    obtain ⟨eS⟩ := hSL
    have hcardM : Nat.card M = 60 * Nat.card (pPrimeCore 2 ↥M) := by
      rw [card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥M), Nat.card_congr eA.toEquiv,
        card_alt_five]
    have h120 : Nat.card M = 120 := by
      rw [Nat.card_congr eS.toEquiv, card_SL_two, hK5]
      norm_num
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact Nat.coprime_two_left.1 (pPrimeCore_coprime_card (G := ↥M) (p := 2))
    obtain ⟨c, hc⟩ := hodd
    omega
  have hMeq : P₁.map e.toMonoidHom = P₂.map e.toMonoidHom :=
    GSThmB.X10Sp4.TwoL5.psp4_unique hK5 hα2 hα1 hM0₁ hM₁ hM0₂ hM₂ (hnotSL hAM₁) (hnotSL hAM₂)
  refine (hne ?_).elim
  have := congrArg (Subgroup.map e.symm.toMonoidHom) hMeq
  rwa [Subgroup.map_map, Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom =
    MonoidHom.id S from by ext; simp, Subgroup.map_id, Subgroup.map_id] at this

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
