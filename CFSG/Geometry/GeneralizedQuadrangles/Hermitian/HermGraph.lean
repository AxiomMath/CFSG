module

public import CFSG.ClassicalGroups.Unitary.Form
public import CFSG.RankThree.GF2n.Stroth80.FieldAut

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open Module

@[expose] def HermGraph (K : Type*) [Field K] (σ : K ≃+* K) : SimpleGraph
    {U : Submodule K (Fin 5 → K) // (finrank K U = 1 ∨ finrank K U = 2) ∧
      ∀ u ∈ U, ∀ v ∈ U, CFSG.ClassicalGroups.Unitary.herm σ u v = 0} :=
  SimpleGraph.fromRel fun U W => U.1 < W.1

private abbrev HermVertex (K : Type*) [Field K] (σ : K ≃+* K) :=
  {U : Submodule K (Fin 5 → K) // (finrank K U = 1 ∨ finrank K U = 2) ∧
    ∀ u ∈ U, ∀ v ∈ U, CFSG.ClassicalGroups.Unitary.herm σ u v = 0}

private noncomputable def coordLin {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂) :
    (Fin 5 → K₁) →ₛₗ[(φ : K₁ →+* K₂)] (Fin 5 → K₂) where
  toFun x i := φ (x i)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

private lemma coordLin_apply {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂)
    (x : Fin 5 → K₁) (i : Fin 5) : coordLin φ x i = φ (x i) := rfl

private lemma coordLin_symm_coordLin {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (φ : K₁ ≃+* K₂) (x : Fin 5 → K₁) : coordLin φ.symm (coordLin φ x) = x := by
  ext i
  simp [coordLin]

private lemma coordLin_injective {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂) :
    Function.Injective (coordLin φ) := by
  intro x y h
  funext i
  exact φ.injective (congrFun h i)

private noncomputable abbrev image {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂)
    (U : Submodule K₁ (Fin 5 → K₁)) : Submodule K₂ (Fin 5 → K₂) :=
  Submodule.map (coordLin φ) U

private lemma herm_coord {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂)
    {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂} (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x))
    (x y : Fin 5 → K₁) :
    CFSG.ClassicalGroups.Unitary.herm σ₂ (coordLin φ x) (coordLin φ y) =
      φ (CFSG.ClassicalGroups.Unitary.herm σ₁ x y) := by
  simp only [CFSG.ClassicalGroups.Unitary.herm, coordLin_apply, map_sum, map_mul, hφσ]

private lemma finrank_image {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁] [Fintype K₂]
    (φ : K₁ ≃+* K₂) (hcard : Fintype.card K₁ = Fintype.card K₂)
    (U : Submodule K₁ (Fin 5 → K₁)) :
    Module.finrank K₂ (image φ U) = Module.finrank K₁ U := by
  classical
  haveI : Fintype U := Fintype.ofFinite U
  haveI : Fintype (image φ U) := Fintype.ofFinite (image φ U)
  have hU : Fintype.card U = Fintype.card K₁ ^ Module.finrank K₁ U :=
    Module.card_eq_pow_finrank
  have hV : Fintype.card (image φ U) =
      Fintype.card K₂ ^ Module.finrank K₂ (image φ U) :=
    Module.card_eq_pow_finrank
  have hUV : Fintype.card (image φ U) = Fintype.card U := by
    refine (Fintype.card_congr ?_).symm
    refine
      { toFun := fun u => ⟨coordLin φ u.1, Submodule.mem_map_of_mem u.2⟩
        invFun := fun v =>
          ⟨(Submodule.mem_map.mp v.2).choose, (Submodule.mem_map.mp v.2).choose_spec.1⟩
        left_inv := fun u => by
          apply Subtype.ext
          exact coordLin_injective φ
            (Submodule.mem_map.mp (Submodule.mem_map_of_mem u.2)).choose_spec.2
        right_inv := fun v => by
          apply Subtype.ext
          exact (Submodule.mem_map.mp v.2).choose_spec.2 }
  have hpow : Fintype.card K₂ ^ Module.finrank K₂ (image φ U) =
      Fintype.card K₁ ^ Module.finrank K₁ U := by
    rw [← hV, hUV, hU]
  have hpow' : Fintype.card K₁ ^ Module.finrank K₂ (image φ U) =
      Fintype.card K₁ ^ Module.finrank K₁ U := by
    simpa [hcard] using hpow
  exact Nat.pow_right_injective (Nat.succ_le_of_lt Fintype.one_lt_card) hpow'

private lemma isTotallyIsotropic_image {K₁ K₂ : Type*} [Field K₁] [Field K₂]
    (φ : K₁ ≃+* K₂) {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂}
    (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x)) {U : Submodule K₁ (Fin 5 → K₁)}
    (hU : ∀ u ∈ U, ∀ v ∈ U, CFSG.ClassicalGroups.Unitary.herm σ₁ u v = 0) :
    ∀ u ∈ image φ U, ∀ v ∈ image φ U, CFSG.ClassicalGroups.Unitary.herm σ₂ u v = 0 := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  rw [herm_coord φ hφσ u v, hU u hu v hv, map_zero]

private lemma image_symm_image {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂)
    (U : Submodule K₁ (Fin 5 → K₁)) : image φ.symm (image φ U) = U := by
  ext x
  simp only [image, Submodule.mem_map]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [coordLin_symm_coordLin φ z]
    exact hz
  · intro hx
    exact ⟨coordLin φ x, ⟨x, hx, rfl⟩, coordLin_symm_coordLin φ x⟩

private lemma image_lt_iff {K₁ K₂ : Type*} [Field K₁] [Field K₂] (φ : K₁ ≃+* K₂)
    (U W : Submodule K₁ (Fin 5 → K₁)) : image φ U < image φ W ↔ U < W :=
  Submodule.map_lt_map_iff_of_injective (coordLin_injective φ)

private noncomputable def imageVertex {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁]
    [Fintype K₂] {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂} (φ : K₁ ≃+* K₂)
    (hcard : Fintype.card K₁ = Fintype.card K₂) (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x))
    (U : HermVertex K₁ σ₁) : HermVertex K₂ σ₂ :=
  ⟨image φ U.1, by
      have hfin := finrank_image φ hcard U.1
      rcases U.2.1 with h | h
      · exact Or.inl (hfin.trans h)
      · exact Or.inr (hfin.trans h),
    isTotallyIsotropic_image φ hφσ U.2.2⟩

private lemma symm_hφσ {K₁ K₂ : Type*} [Field K₁] [Field K₂] {σ₁ : K₁ ≃+* K₁}
    {σ₂ : K₂ ≃+* K₂} (φ : K₁ ≃+* K₂) (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x)) :
    ∀ y, σ₁ (φ.symm y) = φ.symm (σ₂ y) := by
  intro y
  have := congrArg φ.symm (hφσ (φ.symm y))
  simpa using this.symm

private lemma imageVertex_inj {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁]
    [Fintype K₂] {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂} (φ : K₁ ≃+* K₂)
    (hcard : Fintype.card K₁ = Fintype.card K₂) (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x))
    (U W : HermVertex K₁ σ₁) :
    imageVertex φ hcard hφσ U = imageVertex φ hcard hφσ W ↔ U = W := by
  constructor
  · intro h
    have h' := congrArg
      (imageVertex φ.symm hcard.symm (symm_hφσ φ hφσ)) h
    apply Subtype.ext
    have hval := congrArg Subtype.val h'
    simpa [imageVertex, image_symm_image] using hval
  · rintro rfl
    rfl

private lemma imageVertex_left_inv {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁]
    [Fintype K₂] {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂} (φ : K₁ ≃+* K₂)
    (hcard : Fintype.card K₁ = Fintype.card K₂) (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x))
    (U : HermVertex K₁ σ₁) :
    imageVertex φ.symm hcard.symm (symm_hφσ φ hφσ) (imageVertex φ hcard hφσ U) = U := by
  apply Subtype.ext
  exact image_symm_image φ U.1

private lemma imageVertex_right_inv {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁]
    [Fintype K₂] {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂} (φ : K₁ ≃+* K₂)
    (hcard : Fintype.card K₁ = Fintype.card K₂) (hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x))
    (U : HermVertex K₂ σ₂) :
    imageVertex φ hcard hφσ (imageVertex φ.symm hcard.symm (symm_hφσ φ hφσ) U) = U := by
  apply Subtype.ext
  exact image_symm_image φ.symm U.1

theorem hermGraph_iso {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Fintype K₁] [Fintype K₂]
    (h : Fintype.card K₁ = Fintype.card K₂) {σ₁ : K₁ ≃+* K₁} {σ₂ : K₂ ≃+* K₂}
    (h₁ : σ₁ ≠ 1) (h₁' : σ₁ * σ₁ = 1) (h₂ : σ₂ ≠ 1) (h₂' : σ₂ * σ₂ = 1) :
    Nonempty (HermGraph K₁ σ₁ ≃g HermGraph K₂ σ₂) := by
  classical
  haveI : Finite K₂ := Finite.of_fintype K₂
  let φ : K₁ ≃+* K₂ := FiniteField.ringEquivOfCardEq h
  let τ : K₂ ≃+* K₂ := φ.symm.trans (σ₁.trans φ)
  have hσ₁ : ∀ x, σ₁ (σ₁ x) = x := by
    intro x
    have := congrArg (fun e : K₁ ≃+* K₁ => e x) h₁'
    simpa using this
  have hτ1 : τ ≠ 1 := by
    intro hτ
    apply h₁
    ext x
    have h := congrArg (fun e : K₂ ≃+* K₂ => e (φ x)) hτ
    exact φ.injective (by simpa [τ, RingEquiv.trans_apply] using h)
  have hτ2 : τ * τ = 1 := by
    ext y
    simp [τ, RingEquiv.trans_apply, hσ₁]
  have hτ2_apply : ∀ x, τ (τ x) = x := by
    intro x
    have := congrArg (fun e : K₂ ≃+* K₂ => e x) hτ2
    simpa using this
  have hσ₂2_apply : ∀ x, σ₂ (σ₂ x) = x := by
    intro x
    have := congrArg (fun e : K₂ ≃+* K₂ => e x) h₂'
    simpa using this
  obtain ⟨p, hpchar⟩ := CharP.exists K₂
  haveI : CharP K₂ p := hpchar
  obtain ⟨n, hpn, hncard⟩ := FiniteField.card K₂ p
  haveI : Fact p.Prime := ⟨hpn⟩
  let G := GaloisField p (n : ℕ)
  haveI : Field G := inferInstance
  haveI : Fintype G := Fintype.ofFinite G
  have hGcard : Fintype.card G = Fintype.card K₂ := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      GaloisField.card (p := p) (n := (n : ℕ)) n.ne_zero, Nat.card_eq_fintype_card]
    exact hncard.symm
  let ψ : K₂ ≃+* G := FiniteField.ringEquivOfCardEq hGcard.symm
  let τ' : G ≃+* G := ψ.symm.trans (τ.trans ψ)
  let σ' : G ≃+* G := ψ.symm.trans (σ₂.trans ψ)
  have hτ'2 : τ' * τ' = 1 := by
    ext y
    simp [τ', RingEquiv.trans_apply, hτ2_apply]
  have hσ'2 : σ' * σ' = 1 := by
    ext y
    simp [σ', RingEquiv.trans_apply, hσ₂2_apply]
  have hτ'1 : τ' ≠ 1 := by
    intro h
    apply hτ1
    calc
      τ = ψ.trans (τ'.trans ψ.symm) := by ext x; simp [τ', RingEquiv.trans_apply]
      _ = ψ.trans ((1 : G ≃+* G).trans ψ.symm) := by rw [h]
      _ = 1 := by ext x; simp
  have hσ'1 : σ' ≠ 1 := by
    intro h
    apply h₂
    calc
      σ₂ = ψ.trans (σ'.trans ψ.symm) := by ext x; simp [σ', RingEquiv.trans_apply]
      _ = ψ.trans ((1 : G ≃+* G).trans ψ.symm) := by rw [h]
      _ = 1 := by ext x; simp
  have hconj : τ' = σ' :=
    CFSG.RankThree.GF2n.Stroth80.ringEquiv_eq_of_sq_eq_one τ' σ' hτ'2 hσ'2 hτ'1 hσ'1
  have hτeq : τ = σ₂ := by
    calc
      τ = ψ.trans (τ'.trans ψ.symm) := by ext x; simp [τ', RingEquiv.trans_apply]
      _ = ψ.trans (σ'.trans ψ.symm) := by rw [hconj]
      _ = σ₂ := by ext x; simp [σ', RingEquiv.trans_apply]
  have hφσ : ∀ x, σ₂ (φ x) = φ (σ₁ x) := by
    intro x
    have h := congrArg (fun e : K₂ ≃+* K₂ => e (φ x)) hτeq
    simpa [τ, RingEquiv.trans_apply] using h.symm
  refine ⟨{ toFun := imageVertex φ h hφσ
            invFun := imageVertex φ.symm h.symm (symm_hφσ φ hφσ)
            left_inv := imageVertex_left_inv φ h hφσ
            right_inv := imageVertex_right_inv φ h hφσ
            map_rel_iff' := ?_ }⟩
  intro U W
  have hne := imageVertex_inj φ h hφσ U W
  have hlt₁ := image_lt_iff φ U.1 W.1
  have hlt₂ := image_lt_iff φ W.1 U.1
  simp only [HermGraph, SimpleGraph.fromRel_adj]
  change (imageVertex φ h hφσ U ≠ imageVertex φ h hφσ W ∧
      (image φ U.1 < image φ W.1 ∨ image φ W.1 < image φ U.1)) ↔
    (U ≠ W ∧ (U.1 < W.1 ∨ W.1 < U.1))
  rw [hlt₁, hlt₂]
  have hne' : (imageVertex φ h hφσ U ≠ imageVertex φ h hφσ W) ↔ U ≠ W :=
    not_congr hne
  rw [hne']

end CFSG.Geometry.GeneralizedQuadrangles

end
