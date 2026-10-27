module

public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Wreathed.CentralSL2.AugmentationValues
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Blocks.NormOne
public import CFSG.CharacterTheory.Blocks.RepresentationDecomposition
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.Wreathed.CentralSL2.SumZero
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public noncomputable section

namespace CFSG.Wreathed

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.SemilinearOddExtensions

theorem wreathModulus_pos (n : ℕ) : 0 < 2 ^ n := Nat.two_pow_pos n

theorem wreathModulus_even {n : ℕ} (hn : 2 ≤ n) : Even (2 ^ n) :=
  even_two.pow_of_ne_zero (by omega)

theorem semilinearAction_quotientClass (F : Type) [Field F] (b : Fˣ) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * m)) (σ : Sigma) :
    CentralSL2.semilinearAction F b m hm heven Sigma hSigma ⟨quotientClass F b m hm heven X j, σ⟩ =
      coordinatePGLAction F (ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) * fieldExtension F σ := by
  rw [CentralSL2.semilinearAction_mk, CentralSL2.projAction_quotientClass]
  rfl

theorem mulVec_field_ne_zero {F : Type} [Field F] (M : GeneralLinearGroup (Fin 2) F)
    (σ : F ≃+* F) (v : Fin 2 → F) (hv : v ≠ 0) : M.val *ᵥ (fun i => σ (v i)) ≠ 0 := by
  intro h
  apply hv
  have hσ : (fun i => σ (v i)) = 0 := by
    have h2 : (M⁻¹).val *ᵥ (M.val *ᵥ (fun i => σ (v i))) = fun i => σ (v i) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h2, h, Matrix.mulVec_zero]
  funext i
  have := congrFun hσ i
  simpa using this

variable {G : Type} [Group G] [Finite G]

structure ConditionalCompatibleModelData (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (F : Type) [Field F] [Finite F]
    (Sigma : Subgroup (F ≃+* F)) (b : Fˣ) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e) : Prop where
  card : Nat.card F = p ^ f
  sigma_cyclic : IsCyclic Sigma
  sigma_odd : Odd (Nat.card Sigma)
  sigma_dvd : Nat.card Sigma ∣ f
  nonsquare : ¬ IsSquare b
  rho_injective : Function.Injective ρ
  rho_layer : (centralizerSimpleLayer n hn S e).map ρ = specialLayer F
  rho_range : ρ.range = CFSG.Semidihedral.OddFieldLift.Gamma F Sigma
  action : ∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : Sigma)
      (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0),
    w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
      GeneralLinearGroup (Fin 2) F).val *ᵥ (fun i => (σ : F ≃+* F) (v i)) →
    ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F
      (((ρ (centralizerFullQuotientMap n hn S e (Ψ ⟨quotientClass F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩)) : coordinateE F) :
          Equiv.Perm (Omega F))
        ((ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F).symm
          (Projectivization.mk F v hv))) =
      Projectivization.mk F w hw

namespace ConditionalCompatibleModelData

variable {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)} {p f : ℕ}
  {F : Type} [Field F] [Finite F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
  {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b} {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}

theorem action_eq_semilinearAction
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (g : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma) :
    ((ρ (centralizerFullQuotientMap n hn S e (Ψ g)) : coordinateE F) : Equiv.Perm (Omega F)) =
      CentralSL2.semilinearAction F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
        Sigma hSigma g := by
  obtain ⟨w, σ⟩ := g
  obtain ⟨X, j, rfl⟩ :=
    CentralSL2.quotientClass_surjective F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) w
  refine Equiv.ext fun x => ?_
  apply (ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F).injective
  set y := ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F x with hy
  have hx : x = (ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F).symm
      (Projectivization.mk F y.rep y.rep_nonzero) := by
    rw [Projectivization.mk_rep, hy, Equiv.symm_apply_apply]
  have hw := mulVec_field_ne_zero (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)
    (σ : F ≃+* F) y.rep y.rep_nonzero
  rw [hx, hdata.action X j σ y.rep _ y.rep_nonzero hw rfl]
  exact (CentralSL2.semilinearAction_projective F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) Sigma hSigma X j σ y.rep _ y.rep_nonzero hw rfl).symm

theorem action_eq (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : Sigma) :
    ((ρ (centralizerFullQuotientMap n hn S e
        (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩)) :
        coordinateE F) : Equiv.Perm (Omega F)) =
      coordinatePGLAction F (ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) * fieldExtension F σ := by
  rw [hdata.action_eq_semilinearAction, semilinearAction_quotientClass]

theorem augmentation_comp
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (g : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma) :
    (Nat.card {x : Omega F // ((ρ (centralizerFullQuotientMap n hn S e (Ψ g)) :
        coordinateE F) : Equiv.Perm (Omega F)) x = x} : ℂ) - 1 =
      fixedPointCount (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma) (Omega F) g - 1 := by
  rw [CentralSL2.fixedPointCount_semilinear, hdata.action_eq_semilinearAction]

end ConditionalCompatibleModelData

theorem compatible_action_of_eq_semilinearAction {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] [Finite F] {Sigma : Subgroup (F ≃+* F)}
    {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e}
    (h : ∀ (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : Sigma),
      ((ρ (centralizerFullQuotientMap n hn S e
        (Ψ ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩)) :
        coordinateE F) : Equiv.Perm (Omega F)) =
      coordinatePGLAction F (ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) * fieldExtension F σ)
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : Sigma)
    (v w : Fin 2 → F) (hv : v ≠ 0) (hw : w ≠ 0)
    (hwv : w = (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val :
      GeneralLinearGroup (Fin 2) F).val *ᵥ (fun i => (σ : F ≃+* F) (v i))) :
    ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F
      (((ρ (centralizerFullQuotientMap n hn S e (Ψ ⟨quotientClass F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩)) : coordinateE F) :
          Equiv.Perm (Omega F))
        ((ComponentClassification.CatalogueSchreierLinearTwo.coordinateEquiv F).symm
          (Projectivization.mk F v hv))) =
      Projectivization.mk F w hw := by
  rw [h, ← semilinearAction_quotientClass]
  exact CentralSL2.semilinearAction_projective F b (2 ^ n) (wreathModulus_pos n)
    (wreathModulus_even hn) Sigma hSigma X j σ v w hv hw hwv

theorem exists_conditionalCompatibleModelData
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
      (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≃* centralizerOddCoreQuotient n S e),
      ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ := by
  obtain ⟨F, hfield, hfinite, hcard, hchar, -, theta, rho, eta, hin, hrho, -, hdata⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  let : Field F := hfield
  let : Finite F := hfinite
  let : CharP F p := ringChar.eq_iff.mp hchar
  obtain ⟨b₀, hb₀⟩ := WreathedCentralCover.exists_original_fixed_nonsquare_unit F p
    (hp.odd_of_ne_two hpodd) (ActualCentralizerSemilinear.actualField n hn S e rho)
  obtain ⟨hbF, -, -, -, -, -, -, Phi, -, -, -, -, -, -, hprojPhi, -⟩ :=
    hdata.every_nonsquare b₀ hb₀
  exact ⟨F, hfield, hfinite, _, _, WreathedCentralCover.original_fixed_parameter F _ b₀, rho, Phi,
    hcard, CentralSL2Abelianization.fieldSubgroup_isCyclic F _, hdata.structural.field_odd,
    hdata.structural.field_order_dvd, hbF, hrho, hdata.structural.rho_layer,
    hdata.structural.rho_range, compatible_action_of_eq_semilinearAction hprojPhi⟩

end CFSG.Wreathed
