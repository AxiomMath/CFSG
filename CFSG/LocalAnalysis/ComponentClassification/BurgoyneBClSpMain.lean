module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClSpNs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSp
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff lam
  coe_lam pairMat)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.Burgoyne.PSL (fixField mem_fixField)
open CFSG.ComponentClassification.CatLeafProof.EndOddSp (not_mem_scalars_of_ne_smul)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (QuatBlock quatBlock_map_of_sl2)
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem noL2At_sp_fieldAut (hK : ringChar K ≠ 2) (hr : 2 ≤ r) (σ : K ≃+* K) :
    NoL2At (fieldAut r K σ) := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  refine noL2At_of_fix (φ := (fieldSp r K σ).toMonoidHom) hZ (fun g => fieldAut_proj σ g) ?_
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin r := ⟨1, by omega⟩ with hi₁
  refine quatBlock_map_of_sl2 (isQuasisimple_spFixed hK hr σ)
    (ringChar_subfield_ne_two hK (fixField σ))
    ((lam (k := K) i₀).comp (SpecialLinearGroup.map (fixField σ).subtype)) (fun g => ?_) ?_
  · refine mem_spFixed ?_
    rw [MonoidHom.comp_apply, coe_lam]
    change (pairMat (Sum.inl i₀) (Sum.inr i₀) (((SpecialLinearGroup.map (fixField σ).subtype g :
      SL(2, K)) : Matrix (Fin 2) (Fin 2) K))).map σ.toRingHom = _
    rw [pairMat_map]
    congr 1
    ext a b
    rw [Matrix.map_apply, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact ((g : Matrix (Fin 2) (Fin 2) (fixField σ)) a b).2
  · have hφm : ((((lam (k := K) i₀).comp (SpecialLinearGroup.map (fixField σ).subtype)
        (-1 : SL(2, fixField σ)) : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        pairMat (Sum.inl i₀) (Sum.inr i₀) (-1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [MonoidHom.comp_apply, coe_lam]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    refine not_mem_scalars_of_ne_smul fun c hc => ?_
    rw [hφm] at hc
    have e0 := congrFun (congrFun hc (Sum.inl i₀)) (Sum.inl i₀)
    have e1 := congrFun (congrFun hc (Sum.inl i₁)) (Sum.inl i₁)
    have hne : i₁ ≠ i₀ := by simp [hi₀, hi₁, Fin.ext_iff]
    simp only [pairMat, Matrix.of_apply, ite_true, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at e0
    simp only [pairMat, Matrix.of_apply, Sum.inl.injEq, hne, ite_false, reduceCtorEq,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e1
    apply h2
    have e0' : (-1 : K) = c := by
      rw [← e0]
      rfl
    linear_combination e1 - e0'

theorem noL2At_sp_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) {A : gsp r K} {σ : K ≃+* K} (hσ : σ ≠ 1)
    (hv : orderOf (conjAut r K A * fieldAut r K σ) = 2) :
    NoL2At (conjAut r K A * fieldAut r K σ) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  obtain ⟨-, -, -, -, -, -, -, -, -, hdesc⟩ :=
    RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent hℓ hf hr hKc
  have hmem : conjAut r K A * fieldAut r K σ ∈ spSemilinearAutGroup r K :=
    mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have hnot : conjAut r K A * fieldAut r K σ ∉ spLinearAutGroup r K :=
    conjAut_mul_fieldAut_not_mem (by omega) hσ
  obtain ⟨-, σ', -, -, h, -, hht⟩ := hdesc 2 Nat.prime_two _ hmem hnot hv
  refine NoL2At.of_conj h⁻¹ ?_
  have e : h⁻¹ * (conjAut r K A * fieldAut r K σ) * h⁻¹⁻¹ = fieldAut r K σ' := by
    rw [hht]
    group
  rw [e]
  exact noL2At_sp_fieldAut hK hr σ'

omit [Finite K] in
theorem noL2At_sp_of_conj (hr : 1 ≤ r) {A A' : gsp r K} (H : gsp r K) {c : K} (hc : c ≠ 0)
    (hH : ((((H : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((H : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) =
        c • ((A' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    [Finite K] (h : NoL2At (conjAut r K A')) : NoL2At (conjAut r K A) := by
  refine NoL2At.of_conj (conjAut r K H⁻¹) ?_
  have e : conjAut r K H⁻¹ * conjAut r K A * (conjAut r K H⁻¹)⁻¹ = conjAut r K A' := by
    rw [← map_inv, inv_inv, ← map_mul, ← map_mul]
    refine conjAut_eq_of_eq_smul hr hc ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul]
    exact hH
  rw [e]
  exact h

theorem noL2At_sp_conjAut {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) {A : gsp r K} (hv : orderOf (conjAut r K A) = 2) :
    NoL2At (conjAut r K A) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have : NeZero r := ⟨by omega⟩
  have : Nontrivial (Fin r ⊕ Fin r → K) := by
    have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
    infer_instance
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
    intro c hc
    have h1 : conjAut r K A = 1 := (conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩
    rw [h1, orderOf_one] at hv
    exact absurd hv (by norm_num)
  have htt : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hv, pow_orderOf_eq_one]
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
      exact noL2At_sp_split hK hl0 hAA' hJ' hAns
    ·
      have hJ' : Mᵀ * formJ r K * M = (-(l ^ 2)) • formJ r K := by rw [hl, ← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_split_normal_form hK hl0 hAA' hJ'
      exact noL2At_sp_of_conj (by omega) ⟨H, statedSp_le_gsp H.2⟩ hl0 (A' := stdSkewGsp r K)
        hH (noL2At_stdSkew hK hr)
  · push Not at hsq
    rcases hμd with hμd | hμd
    ·
      have hJ' : Mᵀ * formJ r K * M = d • formJ r K := by rw [← hμd]; exact hJμ
      exact noL2At_nonsplitSelf hℓ hℓ2 hf hKc hr hAns hsq hAA hJ'
    ·
      have hJ' : Mᵀ * formJ r K * M = (-d) • formJ r K := by rw [← hμd]; exact hJμ
      obtain ⟨H, hH⟩ := exists_skew_nonsplit_normal_form hℓ hℓ2 hf hKc (by omega) hAns hsq hAA hJ'
      exact noL2At_sp_of_conj (by omega) ⟨H, statedSp_le_gsp H.2⟩ one_ne_zero
        (A' := skewNsGsp r K hd0) (by rw [one_smul, coe_skewNsGsp]; exact hH)
        (noL2At_skewNs hℓ hℓ2 hf hKc hr hsq hd0)

theorem noL2At_psp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) {v : MulAut (StatedProj (StatedSp r K))}
    (hv : orderOf v = 2) : NoL2At v := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  obtain ⟨A, τ, hα⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK (by omega) v
  rw [hα] at hv ⊢
  by_cases hτ : τ = 1
  · subst hτ
    rw [map_one, mul_one] at hv ⊢
    exact noL2At_sp_conjAut hℓ hℓ2 hf hKc hr hv
  · exact noL2At_sp_field hℓ hℓ2 hf hKc (by omega) hτ hv

theorem noL2At_of_lieModel_PSp {S : Type} [Group S] [Finite S] {r p f : ℕ} (hp2 : p ≠ 2)
    (hr : 3 ≤ r) (hL : CFSG.Blueprint.LieModel S .PSp r p f) {v : MulAut S}
    (hv : orderOf v = 2) : NoL2At v := by
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hKc, ⟨θ⟩⟩ := hc
    refine NoL2At.of_congr θ (noL2At_psp hp hp2 hf hKc hr ?_)
    rw [MulEquiv.orderOf_eq]
    exact hv
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.Cl
