module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizers
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersTorus
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolutionTorus

public section

namespace CFSG.Wreathed.OriginalAllPrime.ModelSignalizers

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open CFSG.Wreathed.CentralSL2 CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

theorem semidirect_conj_inl {N G : Type*} [Group N] [Group G] {φ : G →* MulAut N}
    (h : N ⋊[φ] G) (x : N) :
    h * SemidirectProduct.inl x * h⁻¹ =
      SemidirectProduct.inl (h.left * φ h.right x * h.left⁻¹) := by
  apply SemidirectProduct.ext <;> simp [mul_assoc]

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem modelY_eq : modelY b m hm heven Sigma hSigma =
    SemidirectProduct.inl (involutionY F b m hm heven) := rfl

theorem modelX_eq : modelX b m hm heven Sigma hSigma =
    SemidirectProduct.inl (specialInclusion F b m hm heven (-1)) := by
  rw [modelX, cyclicGenerator_pow_m, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]

theorem modelLayer_eq_matrixLayer :
    modelLayer b m hm heven Sigma hSigma = matrixLayer F b m hm heven Sigma hSigma :=
  MonoidHom.map_range _ _

theorem mem_modelLayer_iff {h : SemilinearExtension F b m hm heven Sigma hSigma} :
    h ∈ modelLayer b m hm heven Sigma hSigma ↔
      ∃ Z, SemidirectProduct.inl (specialInclusion F b m hm heven Z) = h := by
  rw [modelLayer_eq_matrixLayer]
  rfl

theorem inl_specialInclusion_mem_modelLayer (Z : SpecialLinearGroup (Fin 2) F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
      SemilinearExtension F b m hm heven Sigma hSigma) ∈ modelLayer b m hm heven Sigma hSigma :=
  mem_modelLayer_iff.mpr ⟨Z, rfl⟩

theorem inl_specialInclusion_injective :
    Function.Injective (fun Z : SpecialLinearGroup (Fin 2) F =>
      (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
        SemilinearExtension F b m hm heven Sigma hSigma)) :=
  SemidirectProduct.inl_injective.comp (specialInclusion_injective F b m hm heven)

theorem mem_modelC_iff (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h ∈ modelC b m hm heven Sigma hSigma ↔
      h.left ∈ Subgroup.centralizer {involutionY F b m hm heven} :=
  mem_centralizer_inl_iff (fun σ => fieldAction_involutionY σ) h

theorem inr_mem_modelC (σ : Sigma) :
    (SemidirectProduct.inr σ : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      modelC b m hm heven Sigma hSigma := by
  rw [mem_modelC_iff, SemidirectProduct.left_inr]
  exact Subgroup.one_mem _

theorem inl_mem_modelC_iff (v : CentralExtension F b m hm heven) :
    (SemidirectProduct.inl v : SemilinearExtension F b m hm heven Sigma hSigma) ∈
      modelC b m hm heven Sigma hSigma ↔ v ∈ Subgroup.centralizer {involutionY F b m hm heven} := by
  rw [mem_modelC_iff, SemidirectProduct.left_inl]

theorem inl_specialInclusion_mem_modelC_iff (Z : SpecialLinearGroup (Fin 2) F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
      SemilinearExtension F b m hm heven Sigma hSigma) ∈ modelC b m hm heven Sigma hSigma ↔
        Z ∈ Subgroup.centralizer {weyl F} := by
  rw [inl_mem_modelC_iff, CFSG.Wreathed.ReducedInvolution.specialInclusion_mem_centralizer_iff]

theorem modelX_comm (h : SemilinearExtension F b m hm heven Sigma hSigma) :
    h * modelX b m hm heven Sigma hSigma = modelX b m hm heven Sigma hSigma * h :=
  inl_cyclicGenerator_pow_m_comm h

theorem modelX_mem_modelC :
    modelX b m hm heven Sigma hSigma ∈ modelC b m hm heven Sigma hSigma :=
  Subgroup.mem_centralizer_singleton_iff.mpr (modelX_comm _).symm

theorem conj_specialInclusion_eq {v : CentralExtension F b m hm heven} {G : GL (Fin 2) F}
    (hv : projectiveMap F b m hm heven v = ProjGenLinGroup.mk G)
    (Y : SpecialLinearGroup (Fin 2) F) :
    v * specialInclusion F b m hm heven Y * v⁻¹ =
      specialInclusion F b m hm heven (matrixConjugation F G Y) :=
  conj_specialInclusion hv (matrixConjugation_toGL F G Y)

theorem conj_inl_specialInclusion {h : SemilinearExtension F b m hm heven Sigma hSigma}
    {G : GL (Fin 2) F} (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G)
    (Y : SpecialLinearGroup (Fin 2) F) :
    h * SemidirectProduct.inl (specialInclusion F b m hm heven Y) * h⁻¹ =
      SemidirectProduct.inl (specialInclusion F b m hm heven
        (matrixConjugation F G (fieldSL F h.right Y))) := by
  rw [semidirect_conj_inl, fieldAction_specialInclusion, conj_specialInclusion_eq hG]

theorem exists_projectiveMap_eq (v : CentralExtension F b m hm heven) :
    ∃ G : GL (Fin 2) F, projectiveMap F b m hm heven v = ProjGenLinGroup.mk G :=
  (ProjGenLinGroup.mk_surjective _).imp fun _ hG => hG.symm

theorem conj_involutionY {v : CentralExtension F b m hm heven} {G : GL (Fin 2) F}
    (hv : projectiveMap F b m hm heven v = ProjGenLinGroup.mk G) :
    v * involutionY F b m hm heven * v⁻¹ =
      (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (matrixConjugation F G (weyl F)) := by
  have ha := (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven v) (m / 4)).eq
  rw [involutionY, ← conj_specialInclusion_eq hv]
  calc v * ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (weyl F)) * v⁻¹
      = v * (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * v⁻¹ *
          (v * specialInclusion F b m hm heven (weyl F) * v⁻¹) := by group
    _ = (cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) * v * v⁻¹ *
          (v * specialInclusion F b m hm heven (weyl F) * v⁻¹) := by rw [ha]
    _ = _ := by group

theorem conj_modelY {h : SemilinearExtension F b m hm heven Sigma hSigma} {G : GL (Fin 2) F}
    (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G) :
    h * modelY b m hm heven Sigma hSigma * h⁻¹ =
      SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (matrixConjugation F G (weyl F))) := by
  rw [modelY_eq, semidirect_conj_inl, fieldAction_involutionY, conj_involutionY hG]

theorem mem_centralizer_involutionY_iff {v : CentralExtension F b m hm heven}
    {G : GL (Fin 2) F} (hv : projectiveMap F b m hm heven v = ProjGenLinGroup.mk G) :
    v ∈ Subgroup.centralizer {involutionY F b m hm heven} ↔
      G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G := by
  have key := conj_involutionY hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    have h1 : v * involutionY F b m hm heven * v⁻¹ = involutionY F b m hm heven := by
      rw [hc, mul_inv_cancel_right]
    rw [key, involutionY, mul_right_inj] at h1
    have h2 := specialInclusion_injective F b m hm heven h1
    have h3 := congrArg (fun X : SpecialLinearGroup (Fin 2) F => SpecialLinearGroup.toGL X) h2
    simp only [matrixConjugation_toGL] at h3
    calc G * SpecialLinearGroup.toGL (weyl F)
        = G * SpecialLinearGroup.toGL (weyl F) * G⁻¹ * G := by group
      _ = SpecialLinearGroup.toGL (weyl F) * G := by rw [h3]
  · intro hG
    have h2 : matrixConjugation F G (weyl F) = weyl F := by
      apply SpecialLinearGroup.toGL_injective
      rw [matrixConjugation_toGL, hG, mul_inv_cancel_right]
    have h1 : v * involutionY F b m hm heven * v⁻¹ = involutionY F b m hm heven := by
      rw [key, h2, involutionY]
    calc v * involutionY F b m hm heven
        = v * involutionY F b m hm heven * v⁻¹ * v := by group
      _ = involutionY F b m hm heven * v := by rw [h1]

theorem mem_modelC_iff_commute {h : SemilinearExtension F b m hm heven Sigma hSigma}
    {G : GL (Fin 2) F} (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G) :
    h ∈ modelC b m hm heven Sigma hSigma ↔
      G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G := by
  rw [mem_modelC_iff, mem_centralizer_involutionY_iff hG]

theorem exists_mem_centralizer_projectiveMap_eq [Finite F] (hb : ¬ IsSquare b)
    {G : GL (Fin 2) F}
    (hG : G * SpecialLinearGroup.toGL (weyl F) = SpecialLinearGroup.toGL (weyl F) * G) :
    ∃ v ∈ Subgroup.centralizer {involutionY F b m hm heven},
      projectiveMap F b m hm heven v = ProjGenLinGroup.mk G := by
  obtain ⟨v, hv⟩ := projectiveMap_surjective F b m hm heven hb (ProjGenLinGroup.mk G)
  exact ⟨v, (mem_centralizer_involutionY_iff hv).mpr hG, hv⟩

theorem modelX_mul_modelY :
    modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma =
      SemidirectProduct.inl ((cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
        specialInclusion F b m hm heven (weyl F)⁻¹) := by
  rw [modelX_eq, modelY_eq, involutionY, ← map_mul]
  congr 1
  have hw : (weyl F)⁻¹ = -1 * weyl F := by
    apply inv_eq_of_mul_eq_one_right
    rw [neg_one_mul, mul_neg, weyl_sq,
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one, neg_neg]
  rw [hw, map_mul, ← mul_assoc, ← mul_assoc]
  congr 1
  exact (Commute.pow_left (cyclicGenerator_sq_comm F b m hm heven _) (m / 4)).eq.symm

theorem conj_modelY_eq_modelX_mul_iff {h : SemilinearExtension F b m hm heven Sigma hSigma}
    {G : GL (Fin 2) F} (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G) :
    h * modelY b m hm heven Sigma hSigma * h⁻¹ =
        modelX b m hm heven Sigma hSigma * modelY b m hm heven Sigma hSigma ↔
      matrixConjugation F G (weyl F) = (weyl F)⁻¹ := by
  rw [conj_modelY hG, modelX_mul_modelY]
  constructor
  · intro h1
    have h2 := mul_left_cancel (SemidirectProduct.inl_injective h1)
    exact specialInclusion_injective F b m hm heven h2
  · intro h1
    rw [h1]

theorem card_modelC [Finite F] :
    Nat.card (modelC b m hm heven Sigma hSigma) =
      Nat.card (Subgroup.centralizer {involutionY F b m hm heven}) * Nat.card Sigma :=
  card_centralizer_inl (fun σ => fieldAction_involutionY σ)

theorem card_semilinearExtension :
    Nat.card (SemilinearExtension F b m hm heven Sigma hSigma) =
      m * Nat.card (SpecialLinearGroup (Fin 2) F) * Nat.card Sigma := by
  rw [SemidirectProduct.card, card_centralExtension]

theorem semilinear_smul_eq {h : SemilinearExtension F b m hm heven Sigma hSigma}
    {G : GL (Fin 2) F} (hG : projectiveMap F b m hm heven h.left = ProjGenLinGroup.mk G)
    (x : Omega F) :
    h • x = coordinateGLAction F G (fieldExtension F h.right x) := by
  rw [semilinearExtension_smul_def]
  change semilinearAction F b m hm heven Sigma hSigma ⟨h.left, h.right⟩ x = _
  rw [semilinearAction_mk, Equiv.Perm.mul_apply, ← coordinatePGLAction_projectiveMap, hG]
  rfl

theorem inl_specialInclusion_smul (Z : SpecialLinearGroup (Fin 2) F) (x : Omega F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven Z) :
      SemilinearExtension F b m hm heven Sigma hSigma) • x =
        coordinateGLAction F (SpecialLinearGroup.toGL Z) x := by
  rw [semilinearExtension_smul_def]
  exact congrFun (congrArg DFunLike.coe
    (semilinearAction_matrixInclusion F b m hm heven Sigma hSigma Z)) x

theorem odd_orderOf_of_mem_sigma [Finite F] (hd : Odd (Nat.card Sigma)) (σ : Sigma) :
    Odd (orderOf (σ : F ≃+* F)) := by
  rw [Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat hd (orderOf_dvd_natCard σ)

theorem sigma_apply_sqrt [Finite F] (hd : Odd (Nat.card Sigma)) (h2 : (2 : F) ≠ 0) (σ : Sigma)
    {i : F} (hi : i * i = -1) : (σ : F ≃+* F) i = i :=
  fieldAut_apply_eq_of_mul_self_eq_neg_one h2 (odd_orderOf_of_mem_sigma hd σ) hi

theorem fieldSL_rootSL [Finite F] (hd : Odd (Nat.card Sigma)) (h2 : (2 : F) ≠ 0) (σ : Sigma)
    {i : F} (hi : i * i = -1) (l : F) :
    fieldSL F σ (rootSL i hi l) = rootSL i hi ((σ : F ≃+* F) l) := by
  have hσi := sigma_apply_sqrt hd h2 σ hi
  apply SL_ext_entries <;> simp [fieldSL_apply, rootSL_coe, hσi]

variable (b m hm heven Sigma hSigma) in
@[expose] def rootGroup (i : F) (hi : i * i = -1) :
    Subgroup (SemilinearExtension F b m hm heven Sigma hSigma) :=
  ((SemidirectProduct.inl.comp (specialInclusion F b m hm heven)).comp (rootHom i hi)).range

theorem mem_rootGroup_iff {i : F} {hi : i * i = -1}
    {x : SemilinearExtension F b m hm heven Sigma hSigma} :
    x ∈ rootGroup b m hm heven Sigma hSigma i hi ↔
      ∃ l, SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l)) = x := by
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.toAdd, rfl⟩
  · rintro ⟨l, rfl⟩
    exact ⟨Multiplicative.ofAdd l, rfl⟩

theorem inl_rootSL_mem_rootGroup {i : F} (hi : i * i = -1) (l : F) :
    (SemidirectProduct.inl (specialInclusion F b m hm heven (rootSL i hi l)) :
      SemilinearExtension F b m hm heven Sigma hSigma) ∈ rootGroup b m hm heven Sigma hSigma i hi :=
  mem_rootGroup_iff.mpr ⟨l, rfl⟩

theorem rootGroup_le_modelLayer {i : F} (hi : i * i = -1) :
    rootGroup b m hm heven Sigma hSigma i hi ≤ modelLayer b m hm heven Sigma hSigma := by
  intro x hx
  obtain ⟨l, rfl⟩ := mem_rootGroup_iff.mp hx
  exact inl_specialInclusion_mem_modelLayer _

theorem card_rootGroup {i : F} (hi : i * i = -1) :
    Nat.card (rootGroup b m hm heven Sigma hSigma i hi) = Nat.card F := by
  have hinj : Function.Injective ((SemidirectProduct.inl.comp
      (specialInclusion F b m hm heven)).comp (rootHom i hi) :
        Multiplicative F →* SemilinearExtension F b m hm heven Sigma hSigma) :=
    (inl_specialInclusion_injective (b := b) (hm := hm) (heven := heven) (Sigma := Sigma)
      (hSigma := hSigma)).comp (rootHom_injective i hi)
  rw [rootGroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

end CFSG.Wreathed.OriginalAllPrime.ModelSignalizers
