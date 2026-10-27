module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalClifford

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Stabilizers

variable {F : Type} [Field F] [Finite F] {b : Fˣ} {m : ℕ}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem sigma_mul_comm (σ τ : Sigma) : σ * τ = τ * σ := by
  have hcyc : IsCyclic Sigma := fieldSubgroup_isCyclic F Sigma
  exact IsCyclic.commGroup.mul_comm σ τ

omit [Finite F] in
theorem fieldParameter_injective (σ : Sigma) :
    Function.Injective (fieldParameter (m := m) hSigma σ) := by
  intro P Q h
  have h1 := congrArg (fieldParameter hSigma σ⁻¹) h
  rwa [← fieldParameter_mul, ← fieldParameter_mul, inv_mul_cancel, fieldParameter_one,
    fieldParameter_one] at h1

theorem parameterStabilizer_fieldParameter (σ : Sigma) (P : PrincipalSeriesParameter F b m) :
    parameterStabilizer hSigma (fieldParameter hSigma σ P) = parameterStabilizer hSigma P := by
  ext τ
  rw [mem_parameterStabilizer_iff, mem_parameterStabilizer_iff, ← fieldParameter_mul,
    sigma_mul_comm τ σ, fieldParameter_mul]
  exact (fieldParameter_injective hSigma σ).eq_iff

omit [Finite F] in
theorem parameterStabilizer_weylParameter (heven : Even m) (P : PrincipalSeriesParameter F b m) :
    parameterStabilizer hSigma (weylParameter F b m heven P) = parameterStabilizer hSigma P := by
  ext τ
  rw [mem_parameterStabilizer_iff, mem_parameterStabilizer_iff, fieldParameter_weylParameter]
  exact (weylParameter_involutive F b m heven).injective.eq_iff

end Stabilizers

section Covariance

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem principalTwist_congr (P : PrincipalSeriesParameter F b m) {S₁ S₂ : Subgroup Sigma}
    (h : S₁ = S₂) (hS₁ : S₁ ≤ parameterStabilizer hSigma P)
    (hS₂ : S₂ ≤ parameterStabilizer hSigma P) (ρ₁ : S₁ →* ℂˣ) (ρ₂ : S₂ →* ℂˣ)
    (hρ : ∀ τ : Sigma, ∀ (h₁ : τ ∈ S₁) (h₂ : τ ∈ S₂), ρ₁ ⟨τ, h₁⟩ = ρ₂ ⟨τ, h₂⟩) :
    principalTwist (hm := hm) (heven := heven) hSigma P S₁ hS₁ ρ₁ =
      principalTwist hSigma P S₂ hS₂ ρ₂ := by
  subst h
  have : ρ₁ = ρ₂ := MonoidHom.ext fun τ => hρ τ τ.2 τ.2
  subst this
  rfl

theorem inr_conj (σ : Sigma) (y : SemilinearExtension F b m hm heven Sigma hSigma) :
    SemidirectProduct.inr σ * y * (SemidirectProduct.inr σ)⁻¹ =
      ⟨fieldAction F b m hm heven Sigma hSigma σ y.left, y.right⟩ := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, SemidirectProduct.mul_right, inv_one, map_one, one_mul,
      mul_one]
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inr]
    rw [sigma_mul_comm σ y.right, mul_inv_cancel_right]

theorem principalTwist_fieldParameter (σ : Sigma) (P : PrincipalSeriesParameter F b m)
    (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (hS' : S ≤ parameterStabilizer hSigma (fieldParameter hSigma σ P)) (ρ : S →* ℂˣ) :
    principalTwist (hm := hm) (heven := heven) hSigma (fieldParameter hSigma σ P) S hS' ρ =
      principalTwist hSigma P S hS ρ := by
  funext g
  have hcl := inducedFunction_conjugate (semilinearBorel (hm := hm) (heven := heven) hSigma S)
    (fun y => (borelTwist hSigma (fieldParameter hSigma σ P) S hS' ρ y : ℂ)) g
    (SemidirectProduct.inr σ)
  have hmem : ∀ y : SemilinearExtension F b m hm heven Sigma hSigma,
      MulAut.conj (SemidirectProduct.inr σ) y ∈ semilinearBorel hSigma S ↔
        y ∈ semilinearBorel hSigma S := by
    intro y
    rw [MulAut.conj_apply, inr_conj, mem_semilinearBorel_iff, mem_semilinearBorel_iff]
    exact and_congr_left' (fieldAction_mem_borel_iff hSigma σ y.left)
  change principalTwist hSigma (fieldParameter hSigma σ P) S hS' ρ g = _
  rw [principalTwist, ← hcl, ← MulAut.conj_apply, inducedFunction_mulEquiv _ _ hmem]
  congr 1
  funext y
  rw [borelTwist_apply, borelTwist_apply]
  have h1 : borelLeft hSigma S ⟨MulAut.conj (SemidirectProduct.inr σ)
      (y : SemilinearExtension F b m hm heven Sigma hSigma), (hmem _).mpr y.2⟩ =
        ⟨fieldAction F b m hm heven Sigma hSigma σ
          (y : SemilinearExtension F b m hm heven Sigma hSigma).left,
          (fieldAction_mem_borel_iff hSigma σ _).mpr y.2.1⟩ := by
    apply Subtype.ext
    change (MulAut.conj (SemidirectProduct.inr σ)
      (y : SemilinearExtension F b m hm heven Sigma hSigma)).left = _
    rw [MulAut.conj_apply, inr_conj]
  have h2 : borelProjection F b m hm heven ⟨fieldAction F b m hm heven Sigma hSigma σ
      (y : SemilinearExtension F b m hm heven Sigma hSigma).left,
        (fieldAction_mem_borel_iff hSigma σ _).mpr y.2.1⟩ =
      torusField hSigma σ (borelProjection F b m hm heven (borelLeft hSigma S y)) :=
    Subtype.ext (borelProjection_fieldAction hSigma σ (borelLeft hSigma S y))
  have h3 := torusCharacter_fieldAction (hm := hm) (heven := heven) hSigma σ⁻¹
    (fieldParameter hSigma σ P)
  rw [inv_inv, ← fieldParameter_mul, inv_mul_cancel, fieldParameter_one] at h3
  have h4 : (⟨(⟨MulAut.conj (SemidirectProduct.inr σ)
      (y : SemilinearExtension F b m hm heven Sigma hSigma), (hmem _).mpr y.2⟩ :
        semilinearBorel (hm := hm) (heven := heven) hSigma S).1.right, ((hmem _).mpr y.2).2⟩ :
          S) = ⟨(y : SemilinearExtension F b m hm heven Sigma hSigma).right, y.2.2⟩ := by
    apply Subtype.ext
    change (MulAut.conj (SemidirectProduct.inr σ)
      (y : SemilinearExtension F b m hm heven Sigma hSigma)).right = _
    rw [MulAut.conj_apply, inr_conj]
  rw [h1, h2, ← MonoidHom.comp_apply, h3, h4]

theorem principalTwist_weylParameter (hb : ¬ IsSquare b) {P : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1) (S : Subgroup Sigma) (hS : S ≤ parameterStabilizer hSigma P)
    (hS' : S ≤ parameterStabilizer hSigma (weylParameter F b m heven P)) (ρ : S →* ℂˣ) :
    principalTwist (hm := hm) (heven := heven) hSigma (weylParameter F b m heven P) S hS' ρ =
      principalTwist hSigma P S hS ρ := by
  rw [principalTwist_eq_induced, principalTwist_eq_induced,
    inertiaTwist_weyl hSigma hb hP S hS hS' ρ]

end Covariance

section Equality

variable {F : Type} [Field F] [Fintype F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem principalInduced_orbit (hb : ¬ IsSquare b) {P P' : PrincipalSeriesParameter F b m}
    (hP : P.1.1 ≠ 1)
    (hPP' : ∃ σ : Sigma, P' = fieldParameter hSigma σ P ∨
      P' = fieldParameter hSigma σ (weylParameter F b m heven P))
    (ρ : parameterStabilizer hSigma P →* ℂˣ) (ρ' : parameterStabilizer hSigma P' →* ℂˣ)
    (hρ : ∀ τ : Sigma, ∀ (h₁ : τ ∈ parameterStabilizer hSigma P)
      (h₂ : τ ∈ parameterStabilizer hSigma P'), ρ ⟨τ, h₁⟩ = ρ' ⟨τ, h₂⟩) :
    principalInduced (hm := hm) (heven := heven) hSigma P ρ = principalInduced hSigma P' ρ' := by
  obtain ⟨σ, hσ | hσ⟩ := hPP'
  · have hstab : parameterStabilizer hSigma P' = parameterStabilizer hSigma P := by
      rw [hσ, parameterStabilizer_fieldParameter]
    have hle : parameterStabilizer hSigma P ≤ parameterStabilizer hSigma P' := hstab.ge
    rw [principalInduced, principalInduced,
      principalTwist_congr hSigma P' hstab le_rfl hle ρ' ρ fun τ h₁ h₂ => (hρ τ h₂ h₁).symm]
    subst hσ
    exact (principalTwist_fieldParameter hSigma σ P _ le_rfl _ ρ).symm
  · have hstabw := parameterStabilizer_weylParameter hSigma heven P
    have hstab : parameterStabilizer hSigma P' = parameterStabilizer hSigma P := by
      rw [hσ, parameterStabilizer_fieldParameter, hstabw]
    have hle : parameterStabilizer hSigma P ≤ parameterStabilizer hSigma P' := hstab.ge
    rw [principalInduced, principalInduced,
      principalTwist_congr hSigma P' hstab le_rfl hle ρ' ρ fun τ h₁ h₂ => (hρ τ h₂ h₁).symm]
    subst hσ
    rw [principalTwist_fieldParameter hSigma σ (weylParameter F b m heven P) _ hstabw.ge,
      principalTwist_weylParameter hSigma hb hP _ le_rfl hstabw.ge]

theorem card_coset_reps {G : Type} [Group G] [Fintype G] (S : Subgroup G) (C : Finset G)
    (hC : ∀ q : G ⧸ S, ∃! σ, σ ∈ C ∧ (σ : G ⧸ S) = q) : C.card = S.index := by
  rw [Subgroup.index, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun x : C => ((x : G) : G ⧸ S)) ⟨?_, ?_⟩)
  · intro x y h
    obtain ⟨σ, -, huniq⟩ := hC ((x : G) : G ⧸ S)
    exact Subtype.ext ((huniq x ⟨x.2, rfl⟩).trans (huniq y ⟨y.2, h.symm⟩).symm)
  · intro q
    obtain ⟨σ, ⟨hσC, hσ⟩, -⟩ := hC q
    exact ⟨⟨σ, hσC⟩, hσ⟩

theorem principalInduced_eq_iff (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P P' : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1) (hP' : P'.1.1 ≠ 1)
    (ρ : parameterStabilizer hSigma P →* ℂˣ) (ρ' : parameterStabilizer hSigma P' →* ℂˣ) :
    principalInduced (hm := hm) (heven := heven) hSigma P ρ = principalInduced hSigma P' ρ' ↔
      (∃ σ : Sigma, P' = fieldParameter hSigma σ P ∨
        P' = fieldParameter hSigma σ (weylParameter F b m heven P)) ∧
      ∀ τ : Sigma, ∀ (h₁ : τ ∈ parameterStabilizer hSigma P)
        (h₂ : τ ∈ parameterStabilizer hSigma P'), ρ ⟨τ, h₁⟩ = ρ' ⟨τ, h₂⟩ := by
  constructor
  · intro h
    obtain ⟨hirr, hinj, hiff, hrest, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma
      hb hd hP
    obtain ⟨hirr', -, hiff', -, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma
      hb hd hP'
    have hpos : 0 < BlocksInnerProduct (fun g => principalInduced (hm := hm) (heven := heven)
        hSigma P ρ (SemidirectProduct.inl g))
          (principalSeries F b m hm heven (torusCharacter F b m hm heven P')) := by
      rw [h]
      exact (hiff' _ (hirr' ρ').1).mpr ⟨ρ', rfl⟩
    obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (parameterStabilizer hSigma P)
    obtain ⟨hsum, -, -⟩ := hrest C hC
    rw [hsum ρ, CFSG.Wreathed.blocksInnerProduct_finset_sum_left] at hpos
    obtain ⟨σ, -, hσ⟩ : ∃ σ ∈ C, BlocksInnerProduct (principalSeries F b m hm heven
        (torusCharacter F b m hm heven (fieldParameter hSigma σ P)))
          (principalSeries F b m hm heven (torusCharacter F b m hm heven P')) ≠ 0 := by
      by_contra hall
      rw [Finset.sum_eq_zero fun σ hσ => by
        by_contra h
        exact hall ⟨σ, hσ, h⟩] at hpos
      exact lt_irrefl 0 hpos
    have hσP : (fieldParameter hSigma σ P).1.1 ≠ 1 := by
      intro h1
      apply hP
      have h2 : P = fieldParameter hSigma σ⁻¹ (fieldParameter hSigma σ P) := by
        rw [← fieldParameter_mul, inv_mul_cancel, fieldParameter_one]
      rw [h2, fieldParameter_fst, h1]
      rfl
    have hirrσ := principalSeries_mem_blocksIrr F b m hm heven hb _ hσP
    have hirrP' := principalSeries_mem_blocksIrr F b m hm heven hb _ hP'
    have h3 := blocksInnerProduct_irreducible ⟨_, hirrσ⟩ ⟨_, hirrP'⟩
    change BlocksInnerProduct (principalSeries F b m hm heven
      (torusCharacter F b m hm heven (fieldParameter hSigma σ P)))
        (principalSeries F b m hm heven (torusCharacter F b m hm heven P')) = _ at h3
    have heq : principalSeries F b m hm heven
        (torusCharacter F b m hm heven (fieldParameter hSigma σ P)) =
        principalSeries F b m hm heven (torusCharacter F b m hm heven P') := by
      by_contra hne
      rw [ite_eq_right (fun h => hne (congrArg Subtype.val h))] at h3
      exact hσ h3
    have horbit : ∃ σ : Sigma, P' = fieldParameter hSigma σ P ∨
        P' = fieldParameter hSigma σ (weylParameter F b m heven P) := by
      refine ⟨σ, ?_⟩
      rcases (principalSeries_eq_iff F b m hm heven hb hσP hP').mp heq with h4 | h4
      · exact Or.inl h4
      · right
        rw [h4, fieldParameter_weylParameter]
    refine ⟨horbit, ?_⟩
    have hstab : parameterStabilizer hSigma P' = parameterStabilizer hSigma P := by
      obtain ⟨σ', h5 | h5⟩ := horbit
      · rw [h5, parameterStabilizer_fieldParameter]
      · rw [h5, parameterStabilizer_fieldParameter, parameterStabilizer_weylParameter]
    let ρ'' : parameterStabilizer hSigma P →* ℂˣ := ρ'.comp (Subgroup.inclusion hstab.ge)
    have h6 : principalInduced (hm := hm) (heven := heven) hSigma P ρ'' =
        principalInduced hSigma P' ρ' :=
      principalInduced_orbit hSigma hb hP horbit ρ'' ρ' fun τ h₁ h₂ => rfl
    have h7 : ρ = ρ'' := hinj (h.trans h6.symm)
    intro τ h₁ h₂
    rw [h7]
    rfl
  · rintro ⟨horbit, hρ⟩
    exact principalInduced_orbit hSigma hb hP horbit ρ ρ' hρ

theorem principalInduced_x (hb : ¬ IsSquare b) (hd : Odd (Nat.card Sigma))
    {P : PrincipalSeriesParameter F b m} (hP : P.1.1 ≠ 1)
    (ρ : parameterStabilizer hSigma P →* ℂˣ) :
    principalInduced (hm := hm) (heven := heven) hSigma P ρ
        (SemidirectProduct.inl (cyclicGenerator F b m hm heven ^ m)) =
      ((parameterStabilizer hSigma P).index : ℂ) * ((Nat.card F : ℂ) + 1) * (P.1.1 (-1) : ℂ) := by
  obtain ⟨-, -, -, hrest, -⟩ := principal_clifford (hm := hm) (heven := heven) hSigma hb hd hP
  obtain ⟨C, hC⟩ := CFSG.Wreathed.exists_leftCoset_reps (parameterStabilizer hSigma P)
  obtain ⟨hsum, -, -⟩ := hrest C hC
  have h1 := congrFun (hsum ρ) (cyclicGenerator F b m hm heven ^ m)
  rw [h1, Finset.sum_apply]
  have h2 : ∀ σ : Sigma, principalSeries F b m hm heven
      (torusCharacter F b m hm heven (fieldParameter hSigma σ P))
        (cyclicGenerator F b m hm heven ^ m) = ((Nat.card F : ℂ) + 1) * (P.1.1 (-1) : ℂ) := by
    intro σ
    rw [principalSeries_x]
    change ((Nat.card F : ℂ) + 1) * (P.1.1 (unitsField ((σ⁻¹ : Sigma) : F ≃+* F) (-1)) : ℂ) = _
    have h3 : unitsField ((σ⁻¹ : Sigma) : F ≃+* F) (-1) = -1 := by
      apply Units.ext
      rw [unitsField_apply]
      simp
    rw [h3]
  rw [Finset.sum_congr rfl fun σ _ => h2 σ, Finset.sum_const, nsmul_eq_mul,
    card_coset_reps _ C hC]
  ring

end Equality

end CFSG.Wreathed.CentralSL2
