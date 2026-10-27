module

public import CFSG.GH74.Generic.Front.SpAut
public import CFSG.GH74.Generic.Front.SpNFToH
public import CFSG.GH74.Generic.Front.OuterModels
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix Subgroup
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.Classical.SteinbergBY
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation (conjAut_mul_fieldAut_eq_one_iff)

section Embed

variable {K L : Type} [Field K] [Field L]

theorem formJ_map_hom (f : K →+* L) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map f =
      fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_map]
  congr 1
  · exact Matrix.map_zero _ (map_zero f)
  · exact Matrix.map_one _ (map_zero f) (map_one f)
  · rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]
  · exact Matrix.map_zero _ (map_zero f)

theorem map_mem_statedSp (f : K →+* L) {g : GL (Fin 2 ⊕ Fin 2) K} (hg : g ∈ StatedSp 2 K) :
    Matrix.GeneralLinearGroup.map f g ∈ StatedSp 2 L :=
  CFSG.Open.StatedAPI.map_mem_statedSp f hg

@[expose] noncomputable def embedSp (f : K →+* L) : StatedSp 2 K →* StatedSp 2 L where
  toFun g := ⟨Matrix.GeneralLinearGroup.map f g, map_mem_statedSp f g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem coe_embedSp (f : K →+* L) (g : StatedSp 2 K) :
    (((embedSp f g : StatedSp 2 L) : GL (Fin 2 ⊕ Fin 2) L) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) L) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map f := rfl

@[expose] def negOneSp (K : Type) [Field K] : StatedSp 2 K :=
  ⟨-1, Subgroup.subset_closure (by simp)⟩

theorem coe_negOneSp (K : Type) [Field K] :
    (((negOneSp K : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  simp [negOneSp]

theorem embedSp_negOneSp (f : K →+* L) : embedSp f (negOneSp K) = negOneSp L := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_embedSp, coe_negOneSp, coe_negOneSp]
  rw [Matrix.map_neg _ (map_neg f), Matrix.map_one _ (map_zero f) (map_one f)]

end Embed

section Comm

variable {F : Type} [Field F]

theorem fieldSp_mul_conjSp (σ : F ≃+* F) (A : gsp 2 F) :
    fieldSp 2 F σ * conjSp 2 F A = conjSp 2 F (gspFieldMap σ A) * fieldSp 2 F σ := by
  refine MulEquiv.ext fun g => ?_
  apply Subtype.ext
  change glFieldEquiv (Fin 2 ⊕ Fin 2) σ ((A : GL (Fin 2 ⊕ Fin 2) F) * g *
      (A : GL (Fin 2 ⊕ Fin 2) F)⁻¹) =
    glFieldEquiv (Fin 2 ⊕ Fin 2) σ A * glFieldEquiv (Fin 2 ⊕ Fin 2) σ g *
      (glFieldEquiv (Fin 2 ⊕ Fin 2) σ A)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem conjSp_scalarGsp (b : Fˣ) : conjSp 2 F (scalarGsp b) = 1 := by
  refine MulEquiv.ext fun g => ?_
  apply Subtype.ext
  change (scalarGsp b : gsp 2 F).1 * (g : GL (Fin 2 ⊕ Fin 2) F) * ((scalarGsp b : gsp 2 F).1)⁻¹ = g
  rw [coe_scalarGsp, scalar_mul_comm_gl, mul_inv_cancel_right]

end Comm

section Main

variable {F : Type} [Field F]

theorem exists_conj_to_field [Finite F] (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (A : gsp 2 F) (c : F)
    (hAσ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ = c • 1) :
    ∃ (M : gsp 2 F) (t : Fˣ), A * gspFieldMap σ M = M * scalarGsp t := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hcard⟩ := exists_prime_pow_card F
  obtain ⟨-, hinj, hDF, -, -, -, -, -, -, hlast⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf (le_refl 2) hcard
  have hfaith := conjAut_mul_fieldAut_eq_one_iff (K := F) (r := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hAσ
    have hu : IsUnit (((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ) :=
      (Units.isUnit _).mul (Units.isUnit (glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F)))
    rw [hAσ] at hu
    exact not_isUnit_zero hu
  have hAA : A * gspFieldMap σ A = scalarGsp (Units.mk0 c hc0) := by
    apply Subtype.ext
    apply Units.ext
    change ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ =
        ((GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 c hc0) : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    rw [hAσ, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rfl
  have haE : conjAut 2 F A * fieldAut 2 F σ ∈ spSemilinearAutGroup 2 F :=
    mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
      (fieldAut_mem_spSemilinearAutGroup σ)
  have haD : conjAut 2 F A * fieldAut 2 F σ ∉ spLinearAutGroup 2 F := by
    intro haD
    have hfD : fieldAut 2 F σ ∈ spLinearAutGroup 2 F := by
      have h1 : fieldAut 2 F σ = (conjAut 2 F A)⁻¹ * (conjAut 2 F A * fieldAut 2 F σ) := by group
      rw [h1]
      exact mul_mem (inv_mem (conjAut_mem_spLinearAutGroup A)) haD
    have hmem : fieldAut 2 F σ ∈ spLinearAutGroup 2 F ⊓ (fieldAut 2 F).range := ⟨hfD, σ, rfl⟩
    rw [hDF] at hmem
    exact hσ1 (hinj ((Subgroup.mem_bot.1 hmem).trans (map_one (fieldAut 2 F)).symm))
  have hasq : (conjAut 2 F A * fieldAut 2 F σ) ^ 2 = 1 := by
    rw [conjAut_mul_fieldAut_pow]
    have htn1 : gspTwistedNorm σ A 1 = A := by
      rw [gspTwistedNorm_succ, gspTwistedNorm_zero, pow_zero, gspFieldMap_one, one_mul]
    have htn : gspTwistedNorm σ A 2 = scalarGsp (Units.mk0 c hc0) := by
      show gspTwistedNorm σ A (1 + 1) = _
      rw [gspTwistedNorm_succ', htn1]
      exact hAA
    rw [htn, conjAut_scalarGsp (r := 2) (by norm_num),
      show σ ^ 2 = 1 by rw [pow_two]; exact hσ2, map_one, one_mul]
  have hao : orderOf (conjAut 2 F A * fieldAut 2 F σ) = 2 := by
    refine orderOf_eq_prime hasq ?_
    intro h1
    apply haD
    rw [h1]
    exact one_mem _
  obtain ⟨-, σ', -, -, h, hhD, hah⟩ := hlast 2 Nat.prime_two _ haE haD hao
  obtain ⟨M, rfl⟩ := mem_spLinearAutGroup_iff.mp hhD
  have h1 : conjAut 2 F M⁻¹ * (conjAut 2 F A * fieldAut 2 F σ) =
      fieldAut 2 F σ' * conjAut 2 F M⁻¹ := by
    rw [hah, map_inv]
    group
  have h2 : conjAut 2 F (M⁻¹ * A) * fieldAut 2 F σ =
      conjAut 2 F (gspFieldMap σ' M⁻¹) * fieldAut 2 F σ' := by
    rw [map_mul, mul_assoc, h1, fieldAut_mul_conjAut]
  have h3 : conjAut 2 F ((gspFieldMap σ' M⁻¹)⁻¹ * (M⁻¹ * A)) * fieldAut 2 F (σ * σ'⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul (fieldAut 2 F), map_inv (fieldAut 2 F)]
    calc (conjAut 2 F (gspFieldMap σ' M⁻¹))⁻¹ * conjAut 2 F (M⁻¹ * A) *
          (fieldAut 2 F σ * (fieldAut 2 F σ')⁻¹)
        = (conjAut 2 F (gspFieldMap σ' M⁻¹))⁻¹ *
            (conjAut 2 F (M⁻¹ * A) * fieldAut 2 F σ) * (fieldAut 2 F σ')⁻¹ := by group
      _ = (conjAut 2 F (gspFieldMap σ' M⁻¹))⁻¹ *
            (conjAut 2 F (gspFieldMap σ' M⁻¹) * fieldAut 2 F σ') * (fieldAut 2 F σ')⁻¹ := by
          rw [h2]
      _ = 1 := by group
  obtain ⟨hσσ', t, ht⟩ := (hfaith _ _).1 h3
  have hσ'σ : σ' = σ := (mul_inv_eq_one.1 hσσ').symm
  subst hσ'σ
  have hinv : gspFieldMap σ' M⁻¹ = (gspFieldMap σ' M)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← gspFieldMap_mul, mul_inv_cancel, gspFieldMap_one_right])
  have hs : (gspFieldMap σ' M⁻¹)⁻¹ * (M⁻¹ * A) = scalarGsp t := Subtype.ext ht
  rw [hinv, inv_inv] at hs
  refine ⟨M, t, ?_⟩
  have hA' : A = M * (gspFieldMap σ' M)⁻¹ * scalarGsp t := by
    calc A = M * (gspFieldMap σ' M)⁻¹ * (gspFieldMap σ' M * (M⁻¹ * A)) := by group
      _ = M * (gspFieldMap σ' M)⁻¹ * scalarGsp t := by rw [hs]
  calc A * gspFieldMap σ' M = M * (gspFieldMap σ' M)⁻¹ * scalarGsp t * gspFieldMap σ' M := by
        rw [← hA']
    _ = M * (gspFieldMap σ' M)⁻¹ * (gspFieldMap σ' M * scalarGsp t) := by
        rw [mul_assoc (M * (gspFieldMap σ' M)⁻¹) (scalarGsp t) (gspFieldMap σ' M),
          scalarGsp_mul_comm]
    _ = M * scalarGsp t := by group

theorem exists_good_fixed_of_field_involution [Finite F] (hF : Odd (Nat.card F)) (σ : F ≃+* F)
    (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1) (A : gsp 2 F) (c : F)
    (hAσ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ = c • 1) :
    ∃ H : Subgroup ↥(StatedSp 2 F),
      (∀ h ∈ H, (conjSp 2 F A * fieldSp 2 F σ) h = h) ∧
      (∀ z ∈ Subgroup.center ↥(StatedSp 2 F), z ∈ H) ∧
      GoodSub (ThreeModel ↥(StatedSp 2 F)) H := by
  classical
  obtain ⟨M, t, hh⟩ := exists_conj_to_field σ hσ1 hσ2 A c hAσ
  have hinv : gspFieldMap σ M⁻¹ = (gspFieldMap σ M)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← gspFieldMap_mul, mul_inv_cancel, gspFieldMap_one_right])
  have hA' : A = M * gspFieldMap σ M⁻¹ * scalarGsp t := by
    rw [hinv]
    calc A = (A * gspFieldMap σ M) * (gspFieldMap σ M)⁻¹ := by group
      _ = M * scalarGsp t * (gspFieldMap σ M)⁻¹ := by rw [hh]
      _ = M * (gspFieldMap σ M)⁻¹ * scalarGsp t := by
          rw [mul_assoc M (scalarGsp t), scalarGsp_mul_comm, ← mul_assoc]
  have hconj : conjSp 2 F A * fieldSp 2 F σ =
      conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F M)⁻¹ := by
    have hcA : conjSp 2 F A = conjSp 2 F M * conjSp 2 F (gspFieldMap σ M⁻¹) := by
      rw [hA', map_mul, map_mul, conjSp_scalarGsp, mul_one]
    calc conjSp 2 F A * fieldSp 2 F σ
        = conjSp 2 F M * conjSp 2 F (gspFieldMap σ M⁻¹) * fieldSp 2 F σ := by rw [hcA]
      _ = conjSp 2 F M * (fieldSp 2 F σ * conjSp 2 F M⁻¹) := by
          rw [fieldSp_mul_conjSp, mul_assoc]
      _ = conjSp 2 F M * fieldSp 2 F σ * (conjSp 2 F M)⁻¹ := by rw [map_inv, mul_assoc]
  have hrank := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield_finrank F σ
    (by rw [pow_two]; exact hσ2) hσ1
  have hcardF : Nat.card F = Nat.card ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank
      (K := ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ)) (V := F),
      hrank]
  have hF₀ : Odd (Nat.card ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ)) := by
    have h2 : Odd (Nat.card ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ) *
        Nat.card ↥(CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ)) := by
      rw [← pow_two, ← hcardF]
      exact hF
    exact (Nat.odd_mul.1 h2).1
  let F₀ := CFSG.ComponentClassification.CatalogueBLinearTwoDescent.fixedSubfield F σ
  have hperf : Group.IsPerfect (StatedSp 2 ↥F₀) := isPerfect_statedSp2_of_odd hF₀
  let ι : StatedSp 2 ↥F₀ →* StatedSp 2 F :=
    ((conjSp 2 F M).toMonoidHom).comp (embedSp F₀.subtype)
  have hfix : ∀ k : StatedSp 2 ↥F₀, fieldSp 2 F σ (embedSp F₀.subtype k) = embedSp F₀.subtype k := by
    intro k
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp, coe_embedSp]
    ext i j
    simp only [Matrix.map_apply]
    exact (CFSG.ComponentClassification.CatalogueBLinearTwoDescent.mem_fixedSubfield F σ _).1
      (((k : GL (Fin 2 ⊕ Fin 2) ↥F₀) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ↥F₀) i j).2
  refine ⟨ι.range, ?_, ?_, Or.inl (Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι))⟩
  · rintro _ ⟨k, rfl⟩
    change (conjSp 2 F A * fieldSp 2 F σ) (conjSp 2 F M (embedSp F₀.subtype k)) =
      conjSp 2 F M (embedSp F₀.subtype k)
    have hy : ((conjSp 2 F M)⁻¹ : MulAut ↥(StatedSp 2 F)) ((conjSp 2 F M) (embedSp F₀.subtype k)) =
        embedSp F₀.subtype k := by simp
    rw [hconj, MulAut.mul_apply, MulAut.mul_apply, hy, hfix]
  · intro z hz
    rcases center_statedSp2_eq z hz with h1 | h1
    · have : z = 1 := Subtype.ext (Units.ext (by rw [h1]; rfl))
      rw [this]
      exact one_mem _
    · have hz' : z = negOneSp F := Subtype.ext (Units.ext (by rw [h1, coe_negOneSp]))
      refine ⟨negOneSp ↥F₀, ?_⟩
      change conjSp 2 F M (embedSp F₀.subtype (negOneSp ↥F₀)) = z
      rw [embedSp_negOneSp, hz']
      apply Subtype.ext
      apply Units.ext
      change ((M : GL (Fin 2 ⊕ Fin 2) F) * ((negOneSp F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
        (M : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F).val = _
      rw [Units.val_mul, Units.val_mul]
      have hcoe : ((negOneSp F : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F).val = -1 := coe_negOneSp F
      rw [hcoe, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul]
      have : ((M : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
          (((M : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by simp
      rw [this]

end Main

end CFSG.GH74.Generic
