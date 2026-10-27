module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftLocal
public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData
public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Wreathed.CentralSL2.Basic
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.CharacterTheory.Wreathed.TwoPartArithmetic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockAtoms
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Wreathed.BrauerWong
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearCuspidalCharacters
public import CFSG.CharacterTheory.Wreathed.CharacterDegreeCongruence
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.OneBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.InductionGram
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.OddFieldLift
  CFSG.Semidihedral.SemilinearOddExtensions CFSG.Wreathed.TorusSplitting CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G] {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {p f : ℕ} {F : Type} [Field F] [Finite F]
  {Sigma : Subgroup (F ≃+* F)} {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}

theorem fieldProjection_pgl_mul (g : PGL2 F) (σ : Sigma) (x : Gamma F Sigma)
    (hx : ((x : coordinateE F) : Equiv.Perm (Omega F)) =
      coordinatePGLAction F g * fieldExtension F σ) :
    CFSG.Wreathed.SylowCentralizerOddField.fieldProjection F Sigma x = σ := by
  have hD : coordinatePGLAction F g ∈ coordinateD F := by
    rw [← coordinatePGLAction_range_eq_D]
    exact ⟨g, rfl⟩
  let d : coordinateE F := ⟨coordinatePGLAction F g, coordinateD_le_E F hD⟩
  have hdL : d ∈ linearLayer F := Subgroup.mem_subgroupOf.mpr hD
  let d' : Gamma F Sigma := ⟨d, le_sup_left (a := linearLayer F) hdL⟩
  have hx' : x = d' * ((gammaFieldEquiv F Sigma).symm σ : Gamma F Sigma) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hx]
    change _ = (d : Equiv.Perm (Omega F)) *
      ((((gammaFieldEquiv F Sigma).symm σ : Gamma F Sigma) : coordinateE F) :
        Equiv.Perm (Omega F))
    rw [gammaFieldEquiv_symm_coe]
  rw [hx']
  exact CFSG.Wreathed.SylowCentralizerOddField.fieldProjection_mul F Sigma d'
    (Subgroup.mem_subgroupOf.mpr hdL) σ

theorem fieldCharacter_eq (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (k : involutionCentralizer n S e) :
    fieldCharacter n hn S e F Sigma ρ hdata.rho_range k =
      (Ψ.symm (centralizerOddCoreMap n S e k)).right := by
  set v := Ψ.symm (centralizerOddCoreMap n S e k) with hv
  have hk : centralizerOddCoreMap n S e k = Ψ v := by rw [hv, MulEquiv.apply_symm_apply]
  obtain ⟨w, σ⟩ := v
  obtain ⟨X, j, rfl⟩ := CentralSL2.quotientClass_surjective F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) w
  apply fieldProjection_pgl_mul (ProjGenLinGroup.mk
    (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) σ
  change ((ρ (centralizerFullQuotientMap n hn S e (centralizerOddCoreMap n S e k)) :
    coordinateE F) : Equiv.Perm (Omega F)) = _
  rw [hk, hdata.action_eq]

theorem commutator_comap_le {H Γ : Type*} [Group H] [Group Γ] (φ : H →* Γ) (L : Subgroup Γ)
    (M : Subgroup H) (hker : φ.ker ≤ Subgroup.center H) (hsurj : ∀ l ∈ L, ∃ m ∈ M, φ m = l) :
    ⁅L.comap φ, L.comap φ⁆ ≤ M := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨m₁, hm₁, h₁⟩ := hsurj (φ a) ha
  obtain ⟨m₂, hm₂, h₂⟩ := hsurj (φ b) hb
  have hz₁ : m₁⁻¹ * a ∈ Subgroup.center H :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, inv_mul_cancel])
  have hz₂ : m₂⁻¹ * b ∈ Subgroup.center H :=
    hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, h₂, inv_mul_cancel])
  rw [Subgroup.mem_center_iff] at hz₁ hz₂
  set z₁ := m₁⁻¹ * a with hz₁def
  set z₂ := m₂⁻¹ * b with hz₂def
  have ha' : a = m₁ * z₁ := by rw [hz₁def, mul_inv_cancel_left]
  have hb' : b = m₂ * z₂ := by rw [hz₂def, mul_inv_cancel_left]
  have e₁ : z₁ * m₂ * z₁⁻¹ = m₂ := by rw [← hz₁ m₂, mul_inv_cancel_right]
  have e₂ : z₁ * z₂ * z₁⁻¹ = z₂ := by rw [← hz₁ z₂, mul_inv_cancel_right]
  have e₃ : z₂ * m₁⁻¹ * z₂⁻¹ = m₁⁻¹ := by rw [← hz₂ m₁⁻¹, mul_inv_cancel_right]
  have key : a * b * a⁻¹ * b⁻¹ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by
    rw [ha', hb']
    calc m₁ * z₁ * (m₂ * z₂) * (m₁ * z₁)⁻¹ * (m₂ * z₂)⁻¹
        = m₁ * (z₁ * m₂ * z₁⁻¹) * (z₁ * z₂ * z₁⁻¹) * m₁⁻¹ * z₂⁻¹ * m₂⁻¹ := by group
      _ = m₁ * m₂ * (z₂ * m₁⁻¹ * z₂⁻¹) * m₂⁻¹ := by rw [e₁, e₂]; group
      _ = m₁ * m₂ * m₁⁻¹ * m₂⁻¹ := by rw [e₃]
  change a * b * a⁻¹ * b⁻¹ ∈ M
  rw [key]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

theorem range_eq_commutator_of_isPerfect {P H : Type*} [Group P] [Group H] [Group.IsPerfect P]
    (φ : P →* H) : φ.range = ⁅φ.range, φ.range⁆ := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

theorem rho_specialInclusion_mem
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (X : SpecialLinearGroup (Fin 2) F) :
    ρ (centralizerFullQuotientMap n hn S e (Ψ (SemidirectProduct.inl
      (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X)))) ∈
      specialLayer F := by
  have h := hdata.action_eq X 0 1
  rw [Subgroup.mem_subgroupOf]
  change ((ρ (centralizerFullQuotientMap n hn S e (Ψ ⟨quotientClass F b (2 ^ n)
    (wreathModulus_pos n) (wreathModulus_even hn) X 0, 1⟩)) : coordinateE F) :
      Equiv.Perm (Omega F)) ∈ coordinateG F
  rw [h]
  have hf1 : fieldExtension F ((1 : Sigma) : F ≃+* F) = 1 := by
    ext x
    cases x <;> rfl
  rw [hf1, mul_one, ZMod.val_zero, pow_zero, mul_one,
    ← ProjectiveSpecialLinearGroup.toPGL_mk, coordinatePGLAction_toPGL,
    ← coordinatePSLAction_range_eq_G]
  exact ⟨_, rfl⟩

theorem five_le_card (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    5 ≤ Nat.card F := by
  rw [hdata.card]
  obtain ⟨-, -, -, -, h3⟩ := hmodel.1
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hpodd).pow
  have h3' : p ^ f ≠ 3 := fun h => h3 (by rw [h])
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hge : 3 ≤ p ^ f := calc
    3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  obtain ⟨k, hk⟩ := hodd
  omega

theorem map_specialInclusion_eq_layer
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    (Ψ.toMonoidHom.comp (SemidirectProduct.inl.comp
      (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)))).range =
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  set φ := Ψ.toMonoidHom.comp (SemidirectProduct.inl.comp
    (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))) with hφ
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  have hq5 := five_le_card hdata hp hpodd hf hmodel
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) := by
    apply CFSG.LinearGroups.special_linear_dimension_two_perfect
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have hle1 : φ.range ≤
      (centralizerSimpleLayer n hn S e).comap (centralizerFullQuotientMap n hn S e) := by
    rintro _ ⟨X, rfl⟩
    have h := rho_specialInclusion_mem hdata X
    rw [← hdata.rho_layer] at h
    obtain ⟨l, hl, hl'⟩ := h
    have hl'' := hdata.rho_injective hl'
    rw [Subgroup.mem_comap]
    change centralizerFullQuotientMap n hn S e (Ψ (SemidirectProduct.inl
      (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X))) ∈ _
    rw [← hl'']
    exact hl
  have hle2 : φ.range ≤ CFSG.layer (centralizerOddCoreQuotient n S e) := by
    rw [range_eq_commutator_of_isPerfect φ, hU.layer]
    refine (Subgroup.commutator_mono hle1 hle1).trans (commutator_comap_le _ _ _ ?_ ?_)
    · rw [← hU.ambient_center]
    · intro l hl
      obtain ⟨m, hm⟩ := hU.restriction_surjective ⟨l, hl⟩
      exact ⟨m, m.2, congrArg Subtype.val hm⟩
  have hinj : Function.Injective φ :=
    Ψ.injective.comp (SemidirectProduct.inl_injective.comp
      (CentralSL2Abelianization.specialInclusion_injective F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn)))
  obtain ⟨F', _, _, hcard', -, -, -, -, eta', -, -, -, -⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  refine Subgroup.eq_of_le_of_card_ge hle2 ?_
  rw [Nat.card_congr eta'.toEquiv, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    CentralSL2.card_SL_two F',
    CentralSL2.card_SL_two F, hcard', hdata.card]

theorem psi_minusIdentity
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    Ψ (SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F))) =
      centralizerOddCoreMap n S e (centralInvolution n S e) := by
  set φ := Ψ.toMonoidHom.comp (SemidirectProduct.inl.comp
    (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))) with hφ
  have hlayer := map_specialInclusion_eq_layer hnonab hfour hp hpodd hf hmodel hdata
  have hinj : Function.Injective φ :=
    Ψ.injective.comp (SemidirectProduct.inl_injective.comp
      (CentralSL2Abelianization.specialInclusion_injective F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn)))
  set z := φ (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity F) with hz
  change z = _
  have hzM : z ∈ CFSG.layer (centralizerOddCoreQuotient n S e) := hlayer ▸ ⟨_, rfl⟩
  have hzc : (⟨z, hzM⟩ : CFSG.layer (centralizerOddCoreQuotient n S e)) ∈
      Subgroup.center (CFSG.layer (centralizerOddCoreQuotient n S e)) := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    rw [← hlayer] at hg
    obtain ⟨X, rfl⟩ := hg
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hz, ← map_mul, ← map_mul,
      Subgroup.mem_center_iff.mp (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_mem_center F)]
  have hcenter := (ActualCentralizerSemilinear.actual_layer_component_data hnonab n hn S e
    hfour).2.2.2.2
  rw [hcenter, Subgroup.mem_subgroupOf] at hzc
  have hord : orderOf (centralizerOddCoreMap n S e (centralInvolution n S e)) = 2 := by
    change orderOf ((centralizerOddCoreMap n S e).comp (nModel n hn S e) (Original.x (2 ^ n))) = 2
    rw [orderOf_injective _ (centralizerOddCoreMap_nModel_injective n hn S e),
      ← orderOf_injective _ (wreathModelHom_injective S e)]
    exact CompatibleFamilies.orderOf_x S e hn
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hzc
  simp only [Finset.mem_image, Finset.mem_range] at hzc
  obtain ⟨k, hk, hzk⟩ := hzc
  interval_cases k
  · exfalso
    rw [pow_zero] at hzk
    have h2 : (2 : F) ≠ 0 := CentralSL2.two_ne_zero_of_not_isSquare hdata.nonsquare
    apply CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_ne_one F
      (OddFieldTorus.ringChar_ne_two h2)
    apply hinj
    change z = φ 1
    rw [map_one]
    exact hzk.symm
  · rw [pow_one] at hzk
    exact hzk.symm

theorem two_pow_eq_two_part
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    2 ^ n = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)) := by
  obtain ⟨F', _, _, hcard', -, -, theta', rho', eta', hin', hrho', -, hdata'⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  have hpart := hdata'.structural.q_two_part
  rw [hcard'] at hpart
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hpodd).pow
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ p ^ f := calc
    3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  by_cases hq4 : p ^ f % 4 = 1
  · rw [ite_eq_left hq4]
    have hfac := two_part_square_sub_one_split (p ^ f) n hq3 hq4 hpart
    have hcast : ((p ^ f : ℕ) : ℤ) - 1 = ((p ^ f - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, padicValInt.of_nat, ← Nat.factorization_def _ Nat.prime_two, hfac]
  · rw [ite_eq_right hq4]
    have hq4' : p ^ f % 4 = 3 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hfac := two_part_square_sub_one_nonsplit (p ^ f) n hq3 hq4' hpart
    have hcast : ((p ^ f : ℕ) : ℤ) - -1 = ((p ^ f + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast, padicValInt.of_nat, ← Nat.factorization_def _ Nat.prime_two, hfac]

end CFSG.Wreathed.NormalComponentLift
