module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenOrth2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthCent

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.X10Orth

open Module Matrix CFSG Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (signMat diagGL coe_diagGL isoOrthGL transportGL
  trans_commutator)
open CFSG.LocalAnalysis.ComponentInitial (determinantLeftFactor determinantRightFactor
  orthogonal_low_dimensional_fixed_derived_component_coverage)
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (specialRho specialRho_apply
  specialRho_eq_one_iff)
open scoped MatrixGroups

variable {K : Type} [Field K] {d : ℕ}

theorem isoOrthGL_val {E : Type} [Field E] {n : ℕ} (hE : ringChar E ≠ 2) (Rw : GL (Fin n) E)
    (hRw : (Rw : Matrix (Fin n) (Fin n) E)ᵀ = Rw)
    (g : TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm Rw)) :
    (((isoOrthGL hE Rw hRw g : CatalogueBGraphForm.isometryGroup n E Rw) : GL (Fin n) E) :
      Matrix (Fin n) (Fin n) E) = LinearMap.toMatrix'
        ((g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : (Fin n → E) →ₗ[E] (Fin n → E)) :=
  rfl

theorem isoOrthGL_neg {E : Type} [Field E] {n : ℕ} (hE : ringChar E ≠ 2) (Rw : GL (Fin n) E)
    (hRw : (Rw : Matrix (Fin n) (Fin n) E)ᵀ = Rw)
    {g : TauCeti.QuadraticMap.orthogonalGroup (CatalogueBLinearHigherB.matrixQuadraticForm Rw)}
    (hg : ∀ v, (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) v = -v) :
    ((isoOrthGL hE Rw hRw g : CatalogueBGraphForm.isometryGroup n E Rw) : GL (Fin n) E) = -1 := by
  apply Units.ext
  rw [isoOrthGL_val, Units.val_neg, Units.val_one]
  have : ((g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : (Fin n → E) →ₗ[E] (Fin n → E)) =
      -LinearMap.id := by
    ext v i
    simp [hg]
  rw [this, map_neg, LinearMap.toMatrix'_id]

theorem specialRho_inl_injective {E : Type*} [Field E] :
    Function.Injective ((specialRho (K := E)).comp (MonoidHom.inl _ _)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, -, h1, h2⟩ := (specialRho_eq_one_iff _).1 hA
  change Matrix.SpecialLinearGroup.toGL A = _ at h1
  change Matrix.SpecialLinearGroup.toGL (1 : SL(2, E)) = _ at h2
  rw [map_one] at h2
  rw [← h2] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)

theorem specialRho_inr_injective {E : Type*} [Field E] :
    Function.Injective ((specialRho (K := E)).comp (MonoidHom.inr _ _)) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, -, h1, h2⟩ := (specialRho_eq_one_iff _).1 hA
  change Matrix.SpecialLinearGroup.toGL (1 : SL(2, E)) = _ at h1
  change Matrix.SpecialLinearGroup.toGL A = _ at h2
  rw [map_one] at h1
  rw [← h1] at h2
  exact Matrix.SpecialLinearGroup.toGL_injective (h2.trans (map_one _).symm)

theorem specialRho_neg_apply {E : Type*} [Field E] (X : Matrix (Fin 2) (Fin 2) E) :
    ((specialRho (K := E)).comp (MonoidHom.inl _ _) (-1)).val X = -X ∧
      ((specialRho (K := E)).comp (MonoidHom.inr _ _) (-1)).val X = -X := by
  constructor
  · rw [MonoidHom.comp_apply, MonoidHom.inl_apply, specialRho_apply]
    simp
  · rw [MonoidHom.comp_apply, MonoidHom.inr_apply, specialRho_apply]
    simp

variable [Finite K]

theorem false_of_orth2_split (hK : ringChar K ≠ 2) {c : K} (hc : ¬ IsSquare c)
    [Fact (Irreducible (sqPoly c))] {w : Fin 4 → EAlg c} (hw : ∀ i, w i ≠ 0)
    {R : GL (Fin (2 * 4)) K} (hRs : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K)ᵀ = R)
    (hR : (R : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      blkDiag 4 (wMat 1 c) * resMat (phiE c).toRingHom 4 (diagonal w))
    (hker : OKer (oQ R)) {gs : similarityPairs (oQ R)} (hσ : gs.val.right = 1)
    (hgA : (gs.val.left : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = blkDiag 4 (jMat c))
    {M : Subgroup (GL (Fin (2 * 4)) K)} {Q : ℕ} (h : X10Data R gs M Q)
    (hS : ∃ S : Submodule (EAlg c) (Fin 4 → EAlg c), Module.finrank (EAlg c) S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm (diagGL hw) x = 0) : False := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨hEf, hE⟩ := finite_ringChar_EAlg hK hc0
  have h2E : (2 : EAlg c) ≠ 0 := Ring.two_ne_zero hE
  have hoddE := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two (EAlg c) hE
  have hoddK := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have hcardE : Nat.card (EAlg c) = Nat.card K ^ 2 := card_EAlg hc0
  have hK3 : 3 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hoddK
    have := Nat.card_pos (α := K)
    have h1 : Nat.card K ≠ 1 := fun h1 => by
      have := Finite.one_lt_card (α := K)
      omega
    omega
  have hE2 : Nat.card (EAlg c) ≠ 2 := by rw [hcardE]; nlinarith
  have hE3 : Nat.card (EAlg c) ≠ 3 := by rw [hcardE]; nlinarith
  set Rw : GL (Fin 4) (EAlg c) := diagGL hw with hRwdef
  have hRw : (Rw : Matrix (Fin 4) (Fin 4) (EAlg c))ᵀ = Rw := diagGL_transpose hw
  set QE := CatalogueBLinearHigherB.matrixQuadraticForm Rw with hQE
  have hQnd := CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hE Rw hRw
  have hdim : Module.finrank (EAlg c) (Fin 4 → EAlg c) = 4 := Module.finrank_fin_fun _
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage QE hQnd
    (Or.inl ⟨hoddE, Or.inr (Or.inl hdim)⟩)
  obtain ⟨ψ, e', -, he', hsup, -, -, -, -, hcomm⟩ := hcov.2.2.2.1 hdim hS hE2 hE3
  clear hcov
  set I := CatalogueBGraphForm.isometryGroup 4 (EAlg c) Rw with hI
  set φ := (phiE c).toRingHom with hφ
  set ι₁ : SL(2, EAlg c) →* GL (Fin (2 * 4)) K := (resGL φ 4).comp (I.subtype.comp
    ((isoOrthGL hE Rw hRw).toMonoidHom.comp (e'.symm.toMonoidHom.comp
      ((specialRho (K := EAlg c)).comp (MonoidHom.inl _ _))))) with hι₁
  set ι₂ : SL(2, EAlg c) →* GL (Fin (2 * 4)) K := (resGL φ 4).comp (I.subtype.comp
    ((isoOrthGL hE Rw hRw).toMonoidHom.comp (e'.symm.toMonoidHom.comp
      ((specialRho (K := EAlg c)).comp (MonoidHom.inr _ _))))) with hι₂
  have hinj : ∀ (ρ : SL(2, EAlg c) →* CatalogueBOrthogonalFourSplit.DeterminantIsometries (EAlg c)),
      Function.Injective ρ → Function.Injective ((resGL φ 4).comp (I.subtype.comp
        ((isoOrthGL hE Rw hRw).toMonoidHom.comp (e'.symm.toMonoidHom.comp ρ)))) := fun ρ hρ =>
    (resGL_injective (phiE_injective c) 4).comp (Subtype.val_injective.comp
      ((isoOrthGL hE Rw hRw).injective.comp (e'.symm.injective.comp hρ)))
  have hι₁i : Function.Injective ι₁ := hinj _ specialRho_inl_injective
  have hι₂i : Function.Injective ι₂ := hinj _ specialRho_inr_injective
  have hneg : ∀ (ρ : SL(2, EAlg c) →* CatalogueBOrthogonalFourSplit.DeterminantIsometries (EAlg c)),
      (∀ X, (ρ (-1)).val X = -X) → (resGL φ 4).comp (I.subtype.comp
        ((isoOrthGL hE Rw hRw).toMonoidHom.comp (e'.symm.toMonoidHom.comp ρ))) (-1) = -1 := by
    intro ρ hρ
    set g₀ := e'.symm (ρ (-1)) with hg₀
    have hg₀v : ∀ v, (g₀ : (Fin 4 → EAlg c) ≃ₗ[EAlg c] (Fin 4 → EAlg c)) v = -v := by
      intro v
      have e1 := he' g₀ (ψ v)
      rw [hg₀, MulEquiv.apply_symm_apply, hρ, ← hg₀, LinearEquiv.symm_apply_apply] at e1
      have e2 := congrArg ψ.symm e1
      rw [LinearEquiv.symm_apply_apply, map_neg, LinearEquiv.symm_apply_apply] at e2
      exact e2.symm
    have hval := isoOrthGL_neg hE Rw hRw hg₀v
    change resGL φ 4 ((isoOrthGL hE Rw hRw g₀ : I) : GL (Fin 4) (EAlg c)) = -1
    rw [hval]
    apply Units.ext
    rw [coe_resGL, Units.val_neg, Units.val_one, map_neg, map_one, Units.val_neg, Units.val_one]
  have hι₁n : ι₁ (-1) = -1 := hneg _ (specialRho_neg_apply ·|>.1)
  have hι₂n : ι₂ (-1) = -1 := hneg _ (specialRho_neg_apply ·|>.2)
  have hZ := commutator_iso_inf_centralizer_eq (φ := φ) (σ := RingHom.id (EAlg c))
    (r := AdjoinRoot.root (sqPoly c)) (phiE_injective c) (wOne_inv_mul hc0)
    (fun x => transpose_phiE_mul_wOne hc0 x) (phiE_root c) (fun M hM => phiE_mem_range hc0 hM)
    (diagonal w) hR hgA
  rw [uGrp_id_eq_iso hw] at hZ
  have hr₁ : ι₁.range = (transportGL (isoOrthGL hE Rw hRw)
      ((determinantLeftFactor (EAlg c)).map e'.symm.toMonoidHom)).map (resGL φ 4) := by
    simp only [hι₁, MonoidHom.range_comp, transportGL, determinantLeftFactor]
    rfl
  have hr₂ : ι₂.range = (transportGL (isoOrthGL hE Rw hRw)
      ((determinantRightFactor (EAlg c)).map e'.symm.toMonoidHom)).map (resGL φ 4) := by
    simp only [hι₂, MonoidHom.range_comp, transportGL, determinantRightFactor]
    rfl
  have hN : (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * 4)) K)) =
      ι₁.range ⊔ ι₂.range := by
    rw [hZ, ← trans_commutator (isoOrthGL hE Rw hRw), hsup, hr₁, hr₂, transportGL, transportGL,
      transportGL, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
  have hcomm' : ∀ A B : SL(2, EAlg c), ι₁ A * ι₂ B = ι₂ B * ι₁ A := by
    intro A B
    have hu : e'.symm ((specialRho (K := EAlg c)).comp (MonoidHom.inl _ _) A) ∈
        (determinantLeftFactor (EAlg c)).map e'.symm.toMonoidHom := ⟨_, ⟨A, rfl⟩, rfl⟩
    have hv : e'.symm ((specialRho (K := EAlg c)).comp (MonoidHom.inr _ _) B) ∈
        (determinantRightFactor (EAlg c)).map e'.symm.toMonoidHom := ⟨_, ⟨B, rfl⟩, rfl⟩
    have e := hcomm _ hu _ hv
    set u := e'.symm ((specialRho (K := EAlg c)).comp (MonoidHom.inl _ _) A) with hu'
    set v := e'.symm ((specialRho (K := EAlg c)).comp (MonoidHom.inr _ _) B) with hv'
    change resGL φ 4 ((isoOrthGL hE Rw hRw u : I) : GL (Fin 4) (EAlg c)) *
        resGL φ 4 ((isoOrthGL hE Rw hRw v : I) : GL (Fin 4) (EAlg c)) =
      resGL φ 4 ((isoOrthGL hE Rw hRw v : I) : GL (Fin 4) (EAlg c)) *
        resGL φ 4 ((isoOrthGL hE Rw hRw u : I) : GL (Fin 4) (EAlg c))
    clear_value u v
    rw [← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, e]
  obtain ⟨hMN, hNH, hPs⟩ := h.le_isoCent hK hRs hσ
  rw [hN] at hMN hNH hPs
  set H := matrixDerived (oQ R) with hH
  have hL₁H : ι₁.range ≤ H := le_sup_left.trans hNH
  have hL₂H : ι₂.range ≤ H := le_sup_right.trans hNH
  set P₁ := (ι₁.range.subgroupOf H).map (projH H) with hP₁
  set P₂ := (ι₂.range.subgroupOf H).map (projH H) with hP₂
  have hPN : ((ι₁.range ⊔ ι₂.range).subgroupOf H).map (projH H) = P₁ ⊔ P₂ := by
    rw [subgroupOf_sup hL₁H hL₂H, Subgroup.map_sup]
  rw [hPN] at hPs
  have hcommP : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨A, hA⟩ := mem_subgroupOf.1 hx
    obtain ⟨B, hB⟩ := mem_subgroupOf.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (x : GL (Fin (2 * 4)) K) * y = y * x
    rw [← hA, ← hB]
    exact hcomm' A B
  have hn₁ : (P₁.subgroupOf (P₁ ⊔ P₂)).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le le_normalizer (DX.Dr.le_normalizer_of_commute hcommP)
  have hn₂ : (P₂.subgroupOf (P₁ ⊔ P₂)).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
    exact sup_le (DX.Dr.le_normalizer_of_commute fun a ha b hb => (hcommP b hb a ha).symm)
      le_normalizer
  set Qb := (M.subgroupOf H).map (projH H) with hQb
  have hQP : Qb ≤ P₁ ⊔ P₂ := by
    rw [← hPN]
    exact map_mono fun x hx => mem_subgroupOf.2 (hMN (mem_subgroupOf.1 hx))
  have hQc' := C.isPComponent_subgroupOf_of_le hQP hPs h.comp
  have hιC : ∀ (ι : SL(2, EAlg c) →* GL (Fin (2 * 4)) K), ι.range ≤ ι₁.range ⊔ ι₂.range →
      ∀ B, ι B ∈ isoCent R gs.val.left := fun ι hι B =>
    commutator_le_self _ (hN.symm ▸ hι ⟨B, rfl⟩ :
      ι B ∈ (⁅isoCent R gs.val.left, isoCent R gs.val.left⁆ : Subgroup (GL (Fin (2 * 4)) K)))
  rcases C.le_or_le_of_le_sup hQP hQc' le_sup_left le_sup_right hn₁.isSubnormal
      hn₂.isSubnormal hQP with h1 | h1
  ·
    have hML := le_of_map_projH_le h.le h.perf h1
    refine h.false_of_e4_sl2 h2E hker hσ hι₂i hι₂n (hιC ι₂ le_sup_right)
      (fun B => hL₂H ⟨B, rfl⟩) fun B m hm => ?_
    obtain ⟨A, rfl⟩ := hML hm
    exact (hcomm' A B).symm
  ·
    have hML := le_of_map_projH_le h.le h.perf h1
    refine h.false_of_e4_sl2 h2E hker hσ hι₁i hι₁n (hιC ι₁ le_sup_left)
      (fun B => hL₁H ⟨B, rfl⟩) fun B m hm => ?_
    obtain ⟨A, rfl⟩ := hML hm
    exact hcomm' B A

end CFSG.ComponentClassification.GSThmB.X10Orth
