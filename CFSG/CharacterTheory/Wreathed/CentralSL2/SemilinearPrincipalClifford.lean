module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalTwist

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Transport

variable {K : Type} [Group K] [Fintype K]

theorem inducedFunction_congr_subgroup {J₁ J₂ : Subgroup K} (h : J₁ = J₂) (f : J₂ → ℂ) :
    inducedFunction J₁ (fun x => f ⟨x.1, h ▸ x.2⟩) = inducedFunction J₂ f := by
  subst h
  rfl

end Transport

section Clifford

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

@[expose] noncomputable def principalInduced (P : PrincipalSeriesParameter F b m)
    (ρ : parameterStabilizer hSigma P →* ℂˣ) :
    SemilinearExtension F b m hm heven Sigma hSigma → ℂ :=
  principalTwist hSigma P (parameterStabilizer hSigma P) le_rfl ρ

theorem principalSeries_classFunction (P : PrincipalSeriesParameter F b m) :
    BlocksIsClassFunction (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) :=
  fun g h => inducedFunction_conjugate _ _ g h

theorem inertia_principalSeries (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    characterInertiaSubgroup (baseLayer F b m hm heven Sigma hSigma)
        (layerFunction (principalSeries F b m hm heven (torusCharacter F b m hm heven P))) =
      semilinearInertia (parameterStabilizer hSigma P) := by
  rw [characterInertiaSubgroup_layer hSigma (principalSeries_classFunction P),
    twistStabilizer_principalSeries hSigma hb hd hP]
  rfl

theorem semilinearInertia_normal (S : Subgroup Sigma) :
    (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S).Normal := by
  have hcyc : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  have hS : S.Normal := ⟨fun n hn g => by
    rw [IsCyclic.commGroup.mul_comm g n, mul_inv_cancel_right]
    exact hn⟩
  exact Subgroup.Normal.comap hS _

omit [Fintype F] in
theorem index_semilinearInertia (S : Subgroup Sigma) :
    (semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S).index = S.index :=
  Subgroup.index_comap_of_surjective S
    (f := (SemidirectProduct.rightHom : SemilinearExtension F b m hm heven Sigma hSigma →* Sigma))
    (fun σ => ⟨SemidirectProduct.inr σ, rfl⟩)

theorem image_inr_reps (S : Subgroup Sigma) (C : Finset Sigma)
    (hC : ∀ q : Sigma ⧸ S, ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ S) = q) :
    ∀ q : SemilinearExtension F b m hm heven Sigma hSigma ⧸
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S,
      ∃! h : SemilinearExtension F b m hm heven Sigma hSigma,
        h ∈ C.image (SemidirectProduct.inr : Sigma →* SemilinearExtension F b m hm heven Sigma
          hSigma) ∧
        (h : SemilinearExtension F b m hm heven Sigma hSigma ⧸ semilinearInertia S) = q := by
  have hmk : ∀ x y : SemilinearExtension F b m hm heven Sigma hSigma,
      (x : SemilinearExtension F b m hm heven Sigma hSigma ⧸
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) = y ↔
        (x.right : Sigma ⧸ S) = y.right := by
    intro x y
    rw [QuotientGroup.eq, QuotientGroup.eq, mem_semilinearInertia_iff]
    rfl
  intro q
  induction q using QuotientGroup.induction_on with
  | H h₀ =>
    obtain ⟨σ, ⟨hσC, hσ⟩, huniq⟩ := hC (h₀.right : Sigma ⧸ S)
    refine ⟨SemidirectProduct.inr σ, ⟨Finset.mem_image.mpr ⟨σ, hσC, rfl⟩, ?_⟩, ?_⟩
    · rw [hmk]
      exact hσ
    · rintro h ⟨hhC, hh⟩
      obtain ⟨σ', hσ'C, rfl⟩ := Finset.mem_image.mp hhC
      rw [hmk] at hh
      rw [huniq σ' ⟨hσ'C, hh⟩]

end Clifford

section Main

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

omit [Fintype F] in
theorem layerFunction_sum {ι : Type} (s : Finset ι) (f : ι → CentralExtension F b m hm heven → ℂ) :
    layerFunction (Sigma := Sigma) (hSigma := hSigma) (∑ i ∈ s, f i) =
      ∑ i ∈ s, layerFunction (f i) := by
  funext n
  simp only [layerFunction, Finset.sum_apply]

theorem principal_clifford (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) :
    (∀ ρ, principalInduced (hm := hm) (heven := heven) hSigma P ρ ∈
        BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma) ∧
      principalInduced (hm := hm) (heven := heven) hSigma P ρ 1 =
        ((parameterStabilizer hSigma P).index : ℂ) * ((Nat.card F : ℂ) + 1)) ∧
    Function.Injective (principalInduced (hm := hm) (heven := heven) hSigma P) ∧
    (∀ ξ ∈ BlocksIrr (SemilinearExtension F b m hm heven Sigma hSigma),
      0 < BlocksInnerProduct (fun g => ξ (SemidirectProduct.inl g))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven P)) ↔
      ∃ ρ, ξ = principalInduced hSigma P ρ) ∧
    (∀ C : Finset Sigma, (∀ q : Sigma ⧸ parameterStabilizer hSigma P,
        ∃! σ, σ ∈ C ∧ (σ : Sigma ⧸ parameterStabilizer hSigma P) = q) →
      (∀ ρ, (fun g => principalInduced (hm := hm) (heven := heven) hSigma P ρ
          (SemidirectProduct.inl g)) =
        ∑ σ ∈ C, principalSeries F b m hm heven
          (torusCharacter F b m hm heven (fieldParameter hSigma σ P))) ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        principalSeries F b m hm heven (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) ≠
          principalSeries F b m hm heven
            (torusCharacter F b m hm heven (fieldParameter hSigma σ' P))) ∧
      (∀ ρ, ∀ σ ∈ C, BlocksInnerProduct (fun g => principalInduced (hm := hm) (heven := heven)
          hSigma P ρ (SemidirectProduct.inl g))
        (principalSeries F b m hm heven
          (torusCharacter F b m hm heven (fieldParameter hSigma σ P))) = 1)) ∧
    (∀ ρ (g : CentralExtension F b m hm heven) (τ : Sigma), τ ∉ parameterStabilizer hSigma P →
      principalInduced (hm := hm) (heven := heven) hSigma P ρ ⟨g, τ⟩ = 0) := by
  set N := baseLayer F b m hm heven Sigma hSigma with hN
  set Ψ := principalSeries F b m hm heven (torusCharacter F b m hm heven P) with hΨ
  set θ := layerFunction (Sigma := Sigma) (hSigma := hSigma) Ψ with hθdef
  set S := parameterStabilizer hSigma P with hSdef
  have hθ : θ ∈ BlocksIrr N :=
    layerFunction_mem_blocksIrr (principalSeries_mem_blocksIrr F b m hm heven hb P hP)
  have hJ : characterInertiaSubgroup N θ = semilinearInertia S :=
    inertia_principalSeries hSigma hb hd hP
  have : IsMulCommutative (InertiaQuotient N θ) := quotient_baseLayer_isMulCommutative _
  have hlin : (fun x : (semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf
      (semilinearInertia S) => (borelTwist hSigma P S le_rfl 1
        ⟨(x.1 : SemilinearExtension F b m hm heven Sigma hSigma), x.2⟩ : ℂ)) ∈
        BlocksIrr ((semilinearBorel (hm := hm) (heven := heven) hSigma S).subgroupOf
          (semilinearInertia S)) :=
    monoidHom_mem_blocksIrr ((Units.coeHom ℂ).comp (borelTwistB hSigma P S le_rfl 1))
  obtain ⟨W, i₁, i₂, i₃, τ₂, hτ₂⟩ := CFSG.Wreathed.exists_representation_inducedFunction _ hlin
  let τ₁ : Representation ℂ (characterInertiaSubgroup N θ) W :=
    τ₂.comp (MulEquiv.subgroupCongr hJ).toMonoidHom
  have hτ₁ : ∀ x : characterInertiaSubgroup N θ, τ₁.character x =
      inertiaTwist hSigma P S le_rfl 1 ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma),
        hJ ▸ x.2⟩ := fun x => congrFun hτ₂ _
  have hρN : ∀ (x : characterInertiaSubgroup N θ)
      (hx : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈ N),
      τ₁.character x = θ ⟨x, hx⟩ := by
    intro x hx
    rw [hτ₁]
    have hx' := eq_inl_left_of_mem_baseLayer hx
    have h1 := inertiaTwist_inl (hm := hm) (heven := heven) hSigma P S le_rfl 1
      (x : SemilinearExtension F b m hm heven Sigma hSigma).left (by rw [hx']; exact hJ ▸ x.2)
    have h2 : (⟨(x : SemilinearExtension F b m hm heven Sigma hSigma), hJ ▸ x.2⟩ :
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S) =
        ⟨SemidirectProduct.inl (x : SemilinearExtension F b m hm heven Sigma hSigma).left,
          by rw [hx']; exact hJ ▸ x.2⟩ := Subtype.ext hx'.symm
    rw [h2, h1]
    rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    abelian_inertia_extension_induction_character_family N hθ τ₁ hρN
  let φ : characterInertiaSubgroup N θ →* S :=
    (SemidirectProduct.rightHom.comp (characterInertiaSubgroup N θ).subtype).codRestrict S
      fun x => (hJ ▸ x.2 : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈
        semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S)
  have hker : N.subgroupOf (characterInertiaSubgroup N θ) = φ.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_baseLayer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext hx
    · intro hx
      exact congrArg Subtype.val hx
  have hsurj : Function.Surjective φ := by
    intro σ
    refine ⟨⟨SemidirectProduct.inr (σ : Sigma), ?_⟩, rfl⟩
    rw [hJ, mem_semilinearInertia_iff]
    exact σ.2
  let e : InertiaQuotient N θ ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
  have he : ∀ x : characterInertiaSubgroup N θ,
      e (x : InertiaQuotient N θ) = ⟨(x : SemilinearExtension F b m hm heven Sigma hSigma).right,
        (hJ ▸ x.2 : (x : SemilinearExtension F b m hm heven Sigma hSigma) ∈
          semilinearInertia (hm := hm) (heven := heven) (hSigma := hSigma) S)⟩ := fun x => rfl
  have hΘ : ∀ ρ : S →* ℂˣ, principalInduced (hm := hm) (heven := heven) hSigma P ρ =
      inertiaInducedCharacter N τ₁ (ρ.comp e.toMonoidHom) := by
    intro ρ
    rw [inertiaInducedCharacter, principalInduced, principalTwist_eq_induced,
      ← inducedFunction_congr_subgroup hJ]
    congr 1
    funext x
    rw [inertiaTwist_eq_mul, quotientTwist, hτ₁, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, he]
    rfl
  have hres : ∀ ξ : SemilinearExtension F b m hm heven Sigma hSigma → ℂ,
      BlocksInnerProduct (fun n : N => ξ n) θ =
        BlocksInnerProduct (fun g => ξ (SemidirectProduct.inl g)) Ψ := by
    intro ξ
    rw [restrict_baseLayer_eq, hθdef, blocksInnerProduct_layerFunction]
  have hθ1 : θ 1 = (Nat.card F : ℂ) + 1 := principalSeries_one F b m hm heven _
  have hindex : (characterInertiaSubgroup N θ).index = S.index := by
    rw [hJ, index_semilinearInertia]
  refine ⟨fun ρ => ?_, fun ρ ρ' h => ?_, fun ξ hξ => ?_, fun C hC => ?_, fun ρ g τ hτ => ?_⟩
  · rw [hΘ]
    obtain ⟨hirr, hdeg⟩ := h1 (ρ.comp e.toMonoidHom)
    refine ⟨hirr, ?_⟩
    rw [hdeg, hindex, hθ1]
  · rw [hΘ, hΘ] at h
    have h' := h2 h
    refine MonoidHom.ext fun s => ?_
    have := DFunLike.congr_fun h' (e.symm s)
    simpa using this
  · rw [← hres, h3 ξ hξ]
    constructor
    · rintro ⟨σ', rfl⟩
      refine ⟨σ'.comp e.symm.toMonoidHom, ?_⟩
      rw [hΘ]
      congr 1
      refine MonoidHom.ext fun q => ?_
      simp
    · rintro ⟨ρ, rfl⟩
      exact ⟨ρ.comp e.toMonoidHom, hΘ ρ⟩
  · have hCH : ∀ q : SemilinearExtension F b m hm heven Sigma hSigma ⧸
        characterInertiaSubgroup N θ, ∃! h, h ∈ C.image (SemidirectProduct.inr :
          Sigma →* SemilinearExtension F b m hm heven Sigma hSigma) ∧
          (h : SemilinearExtension F b m hm heven Sigma hSigma ⧸
            characterInertiaSubgroup N θ) = q := by
      rw [hJ]
      exact image_inr_reps hSigma S C hC
    obtain ⟨hsum, hdist, -, hmult⟩ := h4 _ hCH
    have hconj : ∀ σ : Sigma, conjugateNormalCharacter N θ (SemidirectProduct.inr σ) =
        layerFunction (principalSeries F b m hm heven
          (torusCharacter F b m hm heven (fieldParameter hSigma σ P))) := by
      intro σ
      rw [hθdef, conjugateNormalCharacter_layer hSigma (principalSeries_classFunction P),
        SemidirectProduct.right_inr, principalSeries_fieldTwist]
    have hinj : Set.InjOn (SemidirectProduct.inr : Sigma →*
        SemilinearExtension F b m hm heven Sigma hSigma) C :=
      fun _ _ _ _ h => SemidirectProduct.inr_injective h
    refine ⟨fun ρ => ?_, fun σ hσ σ' hσ' hne => ?_, fun ρ σ hσ => ?_⟩
    · apply layerFunction_injective (Sigma := Sigma) (hSigma := hSigma)
      rw [layerFunction_sum, ← restrict_baseLayer_eq, hΘ, hsum, Finset.sum_image hinj]
      exact Finset.sum_congr rfl fun σ _ => hconj σ
    · intro heq
      apply hdist (SemidirectProduct.inr σ) (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)
        (SemidirectProduct.inr σ') (Finset.mem_image.mpr ⟨σ', hσ', rfl⟩)
        (fun h => hne (SemidirectProduct.inr_injective h))
      rw [hconj, hconj, heq]
    · have h6 := hmult (ρ.comp e.toMonoidHom) (SemidirectProduct.inr σ)
        (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)
      rw [hconj, ← hΘ, restrict_baseLayer_eq, blocksInnerProduct_layerFunction] at h6
      exact h6
  · rw [hΘ]
    apply h5 (by rw [hJ]; exact semilinearInertia_normal hSigma S)
    rw [hJ, mem_semilinearInertia_iff]
    exact hτ

end Main

end CFSG.Wreathed.CentralSL2
