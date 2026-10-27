module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClSpQuat
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClForms
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClSp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBFinal
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBTypeInputs

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.Sp
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (QuatBlock quatBlock_of_isSolvable)
open scoped commutatorElement MatrixGroups

variable {K : Type} [Field K]

section Blocks

theorem J₂_transpose_mul_self : (J₂ K)ᵀ * J₂ K = 1 := by
  rw [J₂_transpose, Matrix.neg_mul, J₂_mul_J₂, neg_neg]

theorem J₂_transpose_mul_J₂_mul : (J₂ K)ᵀ * J₂ K * J₂ K = J₂ K := by
  rw [J₂_transpose_mul_self, Matrix.one_mul]

abbrev symM (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, b; b, -a]

theorem symM_mul_self (a b : K) : symM a b * symM a b = (a ^ 2 + b ^ 2) • (1 : Matrix _ _ K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem symM_transpose (a b : K) : (symM a b)ᵀ = symM a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem symM_mul_J₂ (a b : K) : symM a b * J₂ K = -(J₂ K * symM a b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_symM (a b : K) : (symM a b).det = -(a ^ 2 + b ^ 2) := by
  rw [det_fin_two_of]
  ring

end Blocks

variable {r : ℕ}

theorem noL2At_nonsplitSelf [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) {A : gsp r K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • formJ r K) :
    NoL2At (conjAut r K A) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hq := isQuasisimple_spCent_nonsplit hℓ hℓ2 hf hKc (by omega) hAns hd hAA hJ
  set J := formJ r K with hJdef
  set Am := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  have hJt : Jᵀ = -J := by
    rw [hJdef, formJ, fromBlocks_transpose, fromBlocks_neg]
    simp
  have hJA : Amᵀ * J = J * Am := by
    calc Amᵀ * J = d⁻¹ • (Amᵀ * J * (Am * Am)) := by
          rw [hAA, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hd0, one_smul]
      _ = d⁻¹ • ((Amᵀ * J * Am) * Am) := by rw [Matrix.mul_assoc (Amᵀ * J)]
      _ = J * Am := by
          rw [hJ, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  set ω : (Fin r ⊕ Fin r → K) → (Fin r ⊕ Fin r → K) → K := fun u v => u ⬝ᵥ (J *ᵥ v) with hω
  have halt : ∀ v, ω v v = 0 := dotProduct_mulVec_self_of_alt' h2 hJt
  have hanti : ∀ u v, ω u v = -ω v u := dotProduct_mulVec_antisymm hJt
  have hself : ∀ u v, ω (Am *ᵥ u) v = ω u (Am *ᵥ v) := by
    intro u v
    change (Am *ᵥ u) ⬝ᵥ (J *ᵥ v) = u ⬝ᵥ (J *ᵥ (Am *ᵥ v))
    rw [dotProduct_mulVec_left, hJA, mulVec_mulVec]
  have hsqv : ∀ v, Am *ᵥ (Am *ᵥ v) = d • v := fun v => by
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hlin : ∀ (u v w : Fin r ⊕ Fin r → K) (c : K), ω u (v + c • w) = ω u v + c * ω u w := by
    intro u v w c
    change u ⬝ᵥ (J *ᵥ (v + c • w)) = u ⬝ᵥ (J *ᵥ v) + c * u ⬝ᵥ (J *ᵥ w)
    rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hsmul : ∀ (u v : Fin r ⊕ Fin r → K) (c : K), ω u (c • v) = c * ω u v := by
    intro u v c
    change u ⬝ᵥ (J *ᵥ (c • v)) = c * u ⬝ᵥ (J *ᵥ v)
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  set e : Fin r ⊕ Fin r → K := Pi.single (Sum.inl ⟨0, by omega⟩) 1 with he
  set f₀ : Fin r ⊕ Fin r → K := Pi.single (Sum.inr ⟨0, by omega⟩) 1 with hf₀
  have hef₀ : ω e f₀ = 1 := by
    change e ⬝ᵥ (J *ᵥ f₀) = 1
    rw [he, hf₀, single_dotProduct, mulVec_single_one, one_mul, hJdef, formJ]
    simp
  set β := ω e (Am *ᵥ f₀) with hβ
  have hβd : d - β ^ 2 ≠ 0 := fun h => hd β (by linear_combination -h)
  set c := d * (d - β ^ 2)⁻¹ with hc
  set f : Fin r ⊕ Fin r → K := c • (f₀ + (-(β / d)) • (Am *ᵥ f₀)) with hfdef
  have hef : ω e f = 1 := by
    rw [hfdef, hsmul, hlin, hef₀, ← hβ]
    rw [hc]
    field_simp
    ring
  have heAf : ω e (Am *ᵥ f) = 0 := by
    rw [hfdef, mulVec_smul, mulVec_add, mulVec_smul, hsqv, hsmul, hlin, hsmul, hef₀, ← hβ]
    field_simp
    ring
  set u : Fin 2 → Fin r ⊕ Fin r → K := ![e, f] with hu
  set E := frame4 Am u with hE
  set G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks (J₂ K) 0 0 (d • J₂ K) with hG
  have hselfalt : ∀ v, ω v (Am *ᵥ v) = 0 := by
    intro v
    have h1 : ω v (Am *ᵥ v) = -ω v (Am *ᵥ v) := by
      calc ω v (Am *ᵥ v) = ω (Am *ᵥ v) v := (hself v v).symm
        _ = -ω v (Am *ᵥ v) := hanti _ _
    have h3 : (2 : K) * ω v (Am *ᵥ v) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hfe : ω f e = -1 := by rw [hanti, hef]
  have hfAe : ω f (Am *ᵥ e) = 0 := by rw [← hself, hanti, heAf, neg_zero]
  have hAef : ω (Am *ᵥ e) f = 0 := by rw [hself, heAf]
  have hAfe : ω (Am *ᵥ f) e = 0 := by rw [hanti, heAf, neg_zero]
  have hAee : ω (Am *ᵥ e) e = 0 := by rw [hself, hselfalt]
  have hAff : ω (Am *ᵥ f) f = 0 := by rw [hself, hselfalt]
  have hAeAf : ω (Am *ᵥ e) (Am *ᵥ f) = d := by rw [hself, hsqv, hsmul, hef, mul_one]
  have hAfAe : ω (Am *ᵥ f) (Am *ᵥ e) = -d := by rw [hanti, hAeAf]
  have hGram : Eᵀ * J * E = G := by
    ext (a | a) (b | b) <;> fin_cases a <;> fin_cases b <;>
      simp only [gram_apply', hE, frame4, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, hG,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul, hu, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, mul_one, mul_neg]
    exacts [halt e, hef, hfe, halt f, hselfalt e, heAf, hfAe, hselfalt f, hAee, hAef, hAfe, hAff,
      halt _, hAeAf, hAfAe, halt _]
  set Ginv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    fromBlocks (-J₂ K) 0 0 (-(d⁻¹) • J₂ K) with hGinv
  have hGG : Ginv * G = 1 := by
    rw [hGinv, hG, fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · rw [Matrix.neg_mul, J₂_mul_J₂, neg_neg, Matrix.zero_mul, add_zero]
    · rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    · rw [Matrix.zero_mul, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, J₂_mul_J₂,
        neg_mul, inv_mul_cancel₀ hd0, neg_smul, one_smul, neg_neg]
  have hGG' : G * Ginv = 1 := by
    rw [hGinv, hG, fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · rw [Matrix.mul_neg, J₂_mul_J₂, neg_neg, Matrix.zero_mul, add_zero]
    · rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    · rw [Matrix.zero_mul, Matrix.mul_zero, add_zero]
    · rw [Matrix.zero_mul, zero_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, J₂_mul_J₂,
        mul_neg, mul_inv_cancel₀ hd0, neg_smul, one_smul, neg_neg]
  set F : Matrix (Fin 2 ⊕ Fin 2) (Fin r ⊕ Fin r) K := Ginv * Eᵀ * J with hF
  have hFE : F * E = 1 := by
    rw [hF, show Ginv * Eᵀ * J * E = Ginv * (Eᵀ * J * E) by simp only [Matrix.mul_assoc], hGram,
      hGG]
  have h1 : Eᵀ * J = G * F := by
    rw [hF, show G * (Ginv * Eᵀ * J) = (G * Ginv) * (Eᵀ * J) by simp only [Matrix.mul_assoc],
      hGG', Matrix.one_mul]
  have hGt : Gᵀ = -G := by
    rw [hG, fromBlocks_transpose, fromBlocks_neg]
    simp only [J₂_transpose, transpose_smul, transpose_zero, neg_zero, smul_neg]
  have h2' : J * E = Fᵀ * G := by
    have e1 := congrArg Matrix.transpose h1
    rw [transpose_mul, transpose_mul, hJt, hGt, Matrix.neg_mul, Matrix.mul_neg] at e1
    exact neg_inj.1 e1
  have hAE : Am * E = E * frameA d := mul_frame4 hAA u
  have hA₄G : (frameA d)ᵀ * G = G * frameA d := by
    rw [frameA, hG, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, transpose_one, transpose_smul, Matrix.zero_mul, Matrix.mul_zero,
      Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.smul_mul, Matrix.mul_smul,
      smul_zero]
  have hFA : F * Am = frameA d * F := by
    calc F * Am = Ginv * Eᵀ * (J * Am) := by rw [hF]; simp only [Matrix.mul_assoc]
      _ = Ginv * (Am * E)ᵀ * J := by
          rw [← hJA, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = Ginv * (frameA d)ᵀ * (Eᵀ * J) := by
          rw [hAE, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Ginv * G) * frameA d * F := by
          rw [h1, ← Matrix.mul_assoc, Matrix.mul_assoc Ginv, hA₄G]; simp only [Matrix.mul_assoc]
      _ = frameA d * F := by rw [hGG, Matrix.one_mul]
  obtain ⟨a, b, hab⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hK (-1)
  set x₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks (J₂ K) 0 0 (J₂ K) with hx₄
  set y₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    fromBlocks (symM a b) 0 0 (symM a b) with hy₄
  have hYY : symM a b * symM a b = -1 := by rw [symM_mul_self, hab, neg_one_smul]
  have hYJ : (symM a b)ᵀ * J₂ K * symM a b = J₂ K :=
    transpose_J₂_mul ⟨symM a b, by rw [det_symM, hab, neg_neg]⟩
  have hdiag : ∀ g h : Matrix (Fin 2) (Fin 2) K,
      fromBlocks g 0 0 g * fromBlocks h 0 0 h = fromBlocks (g * h) 0 0 (g * h) := by
    intro g h
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hneg1 : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (-1) 0 0 (-1) := by
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
  have hx : x₄ * x₄ = -1 := by rw [hx₄, hdiag, J₂_mul_J₂, hneg1]
  have hy : y₄ * y₄ = -1 := by rw [hy₄, hdiag, hYY, hneg1]
  have hyx : y₄ * x₄ = -(x₄ * y₄) := by
    rw [hx₄, hy₄, hdiag, hdiag, symM_mul_J₂, fromBlocks_neg, neg_zero]
  have hGiso : ∀ g : Matrix (Fin 2) (Fin 2) K, gᵀ * J₂ K * g = J₂ K →
      (fromBlocks g 0 0 g)ᵀ * G * fromBlocks g 0 0 g = G := by
    intro g hg
    rw [hG, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_smul, Matrix.smul_mul, hg, smul_zero]
  have hxG : x₄ᵀ * G * x₄ = G := hGiso _ J₂_transpose_mul_J₂_mul
  have hyG : y₄ᵀ * G * y₄ = G := hGiso _ hYJ
  have hAcomm : ∀ g : Matrix (Fin 2) (Fin 2) K,
      frameA d * fromBlocks g 0 0 g = fromBlocks g 0 0 g * frameA d := by
    intro g
    rw [frameA, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  obtain ⟨x, y, z, hxm, hym, hz2, hxz, hyz, hxy, hzZ⟩ :=
    exists_sp_quat_pair h2 hr hFE h1 h2' hAE hFA hx hy hyx hxG hyG (hAcomm _) (hAcomm _)
  refine noL2At_of_fix (scalars_subgroupOf_le_center (H := StatedSp r K)) (conjAut_sp_lift A) ?_
  rw [fixOf_conjSp]
  exact quatBlock_map_of_pair hq (commutator_le_self' _ hxm) (commutator_le_self' _ hym) hz2 hxz
    hyz hxy hzZ

theorem noL2At_skewNs [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hr : 3 ≤ r) {d : K} (hd : ∀ l : K, l ^ 2 ≠ d) (hd0 : d ≠ 0) :
    NoL2At (conjAut r K (skewNsGsp r K hd0)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hZ := scalars_subgroupOf_le_center (H := StatedSp r K)
  set Ag := skewNsGsp r K hd0 with hAg
  set Am := ((Ag : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hAm
  have hAgm : Am = skewNs r K d := coe_skewNsGsp hd0
  set J := formJ r K with hJdef
  have hAns : ∀ c : Kˣ, (Ag : GL (Fin r ⊕ Fin r) K) ≠
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    skewNsGsp_ne_scalar (by omega) hd0
  have hAA : Am * Am = d • 1 := by rw [hAgm, skewNs_mul_self]
  have hJ : Amᵀ * J * Am = (-d) • J := by rw [hAgm, skewNs_similitude]
  have hAμ : ∀ v w, pairedSympForm K r (((linA Ag : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA Ag : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = (-d) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJ]
  rcases C.unitary_layer_abstract hℓ hℓ2 hf hKc (by omega) finrank_standard pairedSympForm_isAlt
      SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) hd (linA_mul_self hAA) hAμ with
    hs | ⟨L, hLn, hLq, hLc⟩
  ·
    have hs' : Group.IsSolvable (spCent r K Ag) := Group.isSolvable_of_isSolvable_injective
      (f := (spCentEquiv Ag).toMonoidHom) (spCentEquiv Ag).injective
    refine noL2At_of_fix hZ (conjAut_sp_lift Ag) (quatBlock_of_isSolvable ?_)
    rw [fixOf_conjSp]
    have hfr : ((QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) K).subgroupOf
        (StatedSp r K))).comp (spCent r K Ag).subtype).range =
        (spCent r K Ag).map (QuotientGroup.mk' _) := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hfr]
    exact Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
  set L' := (L.comap (spCentEquiv Ag).toMonoidHom).map (spCent r K Ag).subtype with hL'
  have hL'C : L' ≤ spCent r K Ag := map_subtype_le _
  have hL'q : IsQuasisimple L' := isQuasisimple_map_subtype_comap (spCentEquiv Ag) hLq
  have hcomm : ⁅spCent r K Ag, spCent r K Ag⁆ ≤ L' := by
    rw [commutator_le]
    intro g hg h hh
    refine ⟨⁅(⟨g, hg⟩ : spCent r K Ag), (⟨h, hh⟩ : spCent r K Ag)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, map_commutatorElement]
    exact hLc (commutator_mem_commutator (mem_top _) (mem_top _))
  have hJA : Amᵀ * J = -(J * Am) := by
    calc Amᵀ * J = d⁻¹ • (Amᵀ * J * (Am * Am)) := by
          rw [hAA, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hd0, one_smul]
      _ = d⁻¹ • ((Amᵀ * J * Am) * Am) := by rw [Matrix.mul_assoc (Amᵀ * J)]
      _ = -(J * Am) := by
          rw [hJ, Matrix.smul_mul, smul_smul, mul_neg, inv_mul_cancel₀ hd0, neg_smul, one_smul]
  have hJt : Jᵀ = -J := by
    rw [hJdef, formJ, fromBlocks_transpose, fromBlocks_neg]
    simp
  set u : Fin 2 → Fin r ⊕ Fin r → K := fun k => Pi.single (Sum.inl (Fin.castLE (by omega) k)) 1
    with hu
  set E := frame4 Am u with hE
  set G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := formJ 2 K with hG
  have hcol : ∀ k : Fin 2, Am *ᵥ Pi.single (Sum.inl (Fin.castLE (by omega) k)) 1 =
      Pi.single (Sum.inr (Fin.castLE (by omega) k)) 1 := by
    intro k
    rw [mulVec_single_one, hAgm]
    ext (i | i)
    · simp [skewNs, Matrix.col]
    · simp [skewNs, Matrix.col, Pi.single_apply, Matrix.one_apply]
  have hGram : Eᵀ * J * E = G := by
    ext (a | a) (b | b) <;>
      simp only [gram_apply', hE, frame4, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, hu,
        hcol] <;>
      simp [single_dotProduct, hJdef, hG, formJ, Matrix.col, Matrix.one_apply, Fin.ext_iff]
  set Ginv : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := -G with hGinv
  have hGG2 : G * G = -1 := by
    rw [hG, formJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
    simp
  have hGG : Ginv * G = 1 := by rw [hGinv, Matrix.neg_mul, hGG2, neg_neg]
  have hGG' : G * Ginv = 1 := by rw [hGinv, Matrix.mul_neg, hGG2, neg_neg]
  set F : Matrix (Fin 2 ⊕ Fin 2) (Fin r ⊕ Fin r) K := Ginv * Eᵀ * J with hF
  have hFE : F * E = 1 := by
    rw [hF, show Ginv * Eᵀ * J * E = Ginv * (Eᵀ * J * E) by simp only [Matrix.mul_assoc], hGram,
      hGG]
  have h1 : Eᵀ * J = G * F := by
    rw [hF, show G * (Ginv * Eᵀ * J) = (G * Ginv) * (Eᵀ * J) by simp only [Matrix.mul_assoc],
      hGG', Matrix.one_mul]
  have hGt : Gᵀ = -G := by
    rw [hG, formJ, fromBlocks_transpose, fromBlocks_neg]
    simp
  have h2' : J * E = Fᵀ * G := by
    have e1 := congrArg Matrix.transpose h1
    rw [transpose_mul, transpose_mul, hJt, hGt, Matrix.neg_mul, Matrix.mul_neg] at e1
    exact neg_inj.1 e1
  have hAE : Am * E = E * frameA d := mul_frame4 hAA u
  have hA₄G : (frameA d)ᵀ * G = -(G * frameA d) := by
    rw [frameA, hG, formJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
      fromBlocks_neg]
    simp
  have hFA : F * Am = frameA d * F := by
    calc F * Am = Ginv * Eᵀ * (J * Am) := by rw [hF]; simp only [Matrix.mul_assoc]
      _ = -(Ginv * (Am * E)ᵀ * J) := by
          rw [show J * Am = -(Amᵀ * J) by rw [hJA, neg_neg], transpose_mul, Matrix.mul_neg]
          simp only [Matrix.mul_assoc]
      _ = -(Ginv * (frameA d)ᵀ * (Eᵀ * J)) := by
          rw [hAE, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Ginv * G) * frameA d * F := by
          rw [h1, ← Matrix.mul_assoc, Matrix.mul_assoc Ginv, hA₄G]
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = frameA d * F := by rw [hGG, Matrix.one_mul]
  obtain ⟨s, t, hst⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hK (-d⁻¹)
  set x₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks (J₂ K) 0 0 (J₂ K) with hx₄
  set y₄ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    fromBlocks 0 (d • symM s t) (symM s t) 0 with hy₄
  have hSS : d • (symM s t * symM s t) = -1 := by
    rw [symM_mul_self, hst, smul_smul, mul_neg, mul_inv_cancel₀ hd0, neg_one_smul]
  have hneg1 : (-1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (-1) 0 0 (-1) := by
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
  have hx : x₄ * x₄ = -1 := by
    rw [hx₄, fromBlocks_multiply, J₂_mul_J₂, hneg1]
    simp
  have hy : y₄ * y₄ = -1 := by
    rw [hy₄, fromBlocks_multiply, hneg1]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.smul_mul]
    rw [hSS, Matrix.mul_smul, hSS]
  have hyx : y₄ * x₄ = -(x₄ * y₄) := by
    rw [hx₄, hy₄, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.smul_mul,
      Matrix.mul_smul, symM_mul_J₂, smul_neg, neg_zero, smul_zero]
  have hxG : x₄ᵀ * G * x₄ = G := by
    rw [hx₄, hG, formJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, J₂_transpose_mul_self, neg_zero]
  have hyG : y₄ᵀ * G * y₄ = G := by
    rw [hy₄, hG, formJ, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [transpose_zero, transpose_smul, symM_transpose, Matrix.zero_mul, Matrix.mul_zero,
      zero_add, add_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.smul_mul, Matrix.mul_smul, neg_zero, smul_neg, smul_zero, hSS, neg_neg]
  have hxA : frameA d * x₄ = x₄ * frameA d := by
    rw [frameA, hx₄, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  have hyA : frameA d * y₄ = y₄ * frameA d := by
    rw [frameA, hy₄, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_zero]
  obtain ⟨x, y, z, hxm, hym, hz2, hxz, hyz, hxy, hzZ⟩ :=
    exists_sp_quat_pair h2 hr hFE h1 h2' hAE hFA hx hy hyx hxG hyG hxA hyA
  exact noL2At_of_fix_layer hZ (conjAut_sp_lift Ag) hL'C (by rw [fixOf_conjSp]; exact hcomm)
    (quatBlock_map_of_pair hL'q (hcomm hxm) (hcomm hym) hz2 hxz hyz hxy hzZ)

end CFSG.ComponentClassification.Burgoyne.Cl
