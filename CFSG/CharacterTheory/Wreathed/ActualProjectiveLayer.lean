module

public import CFSG.CharacterTheory.Wreathed.ActualCentralizerLayer
public import CFSG.Dihedral.GorensteinWalter

public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.CharacterTheory.Semidihedral.SemilinearLayerModel
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public noncomputable section

namespace CFSG.Wreathed.ActualProjectiveLayer

universe u

@[expose] def PSLTwoClassicalModel (D : Type u) [Group D] (p f : ℕ) : Prop :=
  CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (D ≃* CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 K))

theorem pslTwoClassicalModel_iff_stated (D : Type) [Group D] (p f : ℕ) :
    PSLTwoClassicalModel D p f ↔
      CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSL 2 p f := Iff.rfl

theorem nonalternating_simple_dihedral_odd_projective_model
    {D : Type u} [Group D] [Finite D] [IsSimpleGroup D]
    (hnonab : ∃ a b : D, a * b ≠ b * a)
    (P : Sylow 2 D) (m : ℕ) (eP : P ≃* DihedralGroup m)
    (hseven : ¬ Nonempty (D ≃* alternatingGroup (Fin 7))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd p ∧ 1 ≤ f ∧ PSLTwoClassicalModel D p f := by
  obtain ⟨D₀, hD₀, hfin₀, ⟨e₀⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} D
  let : Group D₀ := hD₀
  let : Fintype D₀ := hfin₀
  let : IsSimpleGroup D₀ := e₀.symm.isSimpleGroup
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnonab₀ : ∃ a b : D₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e₀ a, e₀ b, ?_⟩
    intro h
    apply hab
    apply e₀.injective
    simpa only [map_mul] using h
  have hsurj₀ : Function.Surjective e₀.toMonoidHom := e₀.surjective
  let P₀ : Sylow 2 D₀ := P.mapSurjective (f := e₀.toMonoidHom) hsurj₀
  have eP₀ : P₀ ≃* DihedralGroup m := by
    dsimp only [P₀]
    rw [Sylow.coe_mapSurjective]
    exact (e₀.subgroupMap (P : Subgroup D)).symm.trans eP
  rcases CFSG.GorensteinWalter.gorenstein_walter D₀ hnonab₀ P₀ ⟨m, ⟨eP₀⟩⟩ with
    hseven₀ | ⟨p, f, hp, hodd, hfive, ⟨ePSL⟩⟩
  · exact (hseven ⟨e₀.trans hseven₀.some⟩).elim
  · let : Fact p.Prime := hp
    have hf : 1 ≤ f := by
      by_contra h
      have hfzero : f = 0 := by omega
      simp [hfzero] at hfive
    have hpne : p ≠ 2 := by
      intro h
      subst p
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    have hmodel₀ := CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv
      D₀ p f hfive ePSL
    obtain ⟨hadmissible, K, hfield, hfinite, hcard, ⟨eK⟩⟩ := hmodel₀
    exact ⟨p, f, hp.out, hpne, hodd, hf, hadmissible,
      K, hfield, hfinite, hcard, ⟨e₀.trans eK⟩⟩

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

theorem actual_full_center_quotient_layer_odd_projective_model
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd p ∧ 1 ≤ f ∧
      PSLTwoClassicalModel (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) p f := by
  have hL := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at hL
  obtain ⟨hsimple, hnonabL, _, _, _, hSylow, hseven, _, _⟩ := hL
  let : IsSimpleGroup (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) := hsimple
  let P : Sylow 2 (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) :=
    Classical.choice Sylow.nonempty
  obtain ⟨eP⟩ := hSylow P
  exact nonalternating_simple_dihedral_odd_projective_model hnonabL P _ eP hseven

theorem quotient_nonempty_mulEquiv_iff_of_eq {H : Type u} [Group H]
    (A B : Subgroup H) [A.Normal] [B.Normal] (hAB : A = B)
    {D : Type*} [Group D] :
    Nonempty ((H ⧸ A) ≃* D) ↔ Nonempty ((H ⧸ B) ≃* D) := by
  subst B
  rfl

theorem quotient_layer_model_iff_of_eq {H : Type u} [Group H]
    (A B : Subgroup H) [A.Normal] [B.Normal] (hAB : A = B) (p f : ℕ) :
    PSLTwoClassicalModel (CFSG.generalizedFitting (H ⧸ A)) p f ↔
      PSLTwoClassicalModel (CFSG.generalizedFitting (H ⧸ B)) p f := by
  subst B
  rfl

theorem wreathed_actual_nonalternating_dihedral_layer_odd_projective_model_all_universes
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd p ∧ 1 ≤ f ∧
      PSLTwoClassicalModel (CFSG.generalizedFitting
        (centralizerOddCoreQuotient n S e ⧸ Subgroup.center
          (centralizerOddCoreQuotient n S e))) p f := by
  have hA := centralizerOddCoreQuotient_center_eq_fullCenterImage n hn S e
  have hfourA : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)) := by
    intro h
    exact hfour ((quotient_nonempty_mulEquiv_iff_of_eq _ _ hA).mpr h)
  obtain ⟨p, f, hp, hpne, hodd, hf, hmodel⟩ :=
    actual_full_center_quotient_layer_odd_projective_model hnonab n hn S e hfourA
  exact ⟨p, f, hp, hpne, hodd, hf, (quotient_layer_model_iff_of_eq _ _ hA p f).mpr hmodel⟩

theorem wreathed_actual_nonalternating_dihedral_layer_has_odd_projective_model
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty ((centralizerOddCoreQuotient n S e ⧸
      Subgroup.center (centralizerOddCoreQuotient n S e)) ≃* Equiv.Perm (Fin 4))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd p ∧ 1 ≤ f ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (CFSG.generalizedFitting
        (centralizerOddCoreQuotient n S e ⧸ Subgroup.center
          (centralizerOddCoreQuotient n S e))) .PSL 2 p f := by
  obtain ⟨p, f, hp, hpne, hodd, hf, hmodel⟩ :=
    wreathed_actual_nonalternating_dihedral_layer_odd_projective_model_all_universes
      hnonab n hn S e hfour
  exact ⟨p, f, hp, hpne, hodd, hf,
    (pslTwoClassicalModel_iff_stated _ p f).mp hmodel⟩

theorem actual_full_center_quotient_layer_stated_odd_projective_model
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd p ∧ 1 ≤ f ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel
        (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) .PSL 2 p f := by
  obtain ⟨p, f, hp, hpne, hodd, hf, hmodel⟩ :=
    actual_full_center_quotient_layer_odd_projective_model hnonab n hn S e hfour
  exact ⟨p, f, hp, hpne, hodd, hf, (pslTwoClassicalModel_iff_stated _ p f).mp hmodel⟩

end CFSG.Wreathed.ActualProjectiveLayer

public noncomputable section

namespace CFSG.Wreathed.ActualProjectiveLayer

open CFSG.Semidihedral.ProjectiveSL2Cover
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

universe u v

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def centralizerActualLayerEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.layer (centralizerOddCoreQuotient n S e) ≃* centralizerLiftedLayer n hn S e :=
  MulEquiv.subgroupCongr
    (wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer

theorem centralizerActualLayerEquiv_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (v : CFSG.layer (centralizerOddCoreQuotient n S e)) :
    (centralizerActualLayerEquiv hnonab n hn S e hfour v : centralizerOddCoreQuotient n S e) = v :=
  MulEquiv.subgroupCongr_apply _ _

@[expose] def centralizerActualLayerMap
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.layer (centralizerOddCoreQuotient n S e) →* centralizerSimpleLayer n hn S e :=
  (centralizerLiftedLayerMap n hn S e).comp
    (centralizerActualLayerEquiv hnonab n hn S e hfour).toMonoidHom

theorem centralizerActualLayerMap_coe
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (v : CFSG.layer (centralizerOddCoreQuotient n S e)) :
    (centralizerActualLayerMap hnonab n hn S e hfour v : centralizerFullQuotient n hn S e) =
      centralizerFullQuotientMap n hn S e v := by
  change centralizerFullQuotientMap n hn S e
    (centralizerActualLayerEquiv hnonab n hn S e hfour v) = _
  rw [centralizerActualLayerEquiv_coe]

theorem centralizerActualLayer_involution_mem
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      CFSG.layer (centralizerOddCoreQuotient n S e) := by
  rw [(wreathed_centralizer_unique_component_data hnonab n hn S e hfour).layer]
  exact (wreathed_centralizer_unique_component_data hnonab n hn S e hfour).involution_mem

@[expose] def centralizerActualLayerInvolution
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    CFSG.layer (centralizerOddCoreQuotient n S e) :=
  ⟨centralizerOddCoreMap n S e (centralInvolution n S e),
    centralizerActualLayer_involution_mem hnonab n hn S e hfour⟩

theorem exists_compatible_actual_layer_sl2
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F,
      (nativeQuotient F).comp eta.toMonoidHom =
        theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour) ∧
      eta (centralizerActualLayerInvolution hnonab n hn S e hfour) = minusIdentity F := by
  have hU := wreathed_centralizer_unique_component_data hnonab n hn S e hfour
  let c : centralizerLiftedLayer n hn S e :=
    ⟨centralizerOddCoreMap n S e (centralInvolution n S e), hU.involution_mem⟩
  have hc : orderOf c = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe (centralizerResidualInvolution hnonab n hn S e)).trans
      (centralizerResidualInvolution_order hnonab n hn S e)
  have hintersection : (centralizerFullQuotientMap n hn S e).ker ⊓
      centralizerResidualImage n hn S e =
      Subgroup.zpowers (centralizerOddCoreMap n S e (centralInvolution n S e)) := by
    change (QuotientGroup.mk' (centralizerFullCenterImage n hn S e)).ker ⊓ _ = _
    rw [QuotientGroup.ker_mk']
    exact centralizerFullCenterImage_inf_residualImage hnonab n hn S e
  have hker : (centralizerLiftedLayerMap n hn S e).ker = Subgroup.zpowers c :=
    UniqueInvolutionLift.restrictedMap_kernel_zpowers _ _ _ _ hintersection
  have hcenter : c ∈ Subgroup.center (centralizerLiftedLayer n hn S e) := by
    change c ∈ Subgroup.center (UniqueInvolutionLift.liftedSubgroup
      (centralizerFullQuotientMap n hn S e) (centralizerResidualImage n hn S e)
      (centralizerSimpleLayer n hn S e))
    rw [hU.center]
    exact Subgroup.mem_zpowers _
  let pi := theta.toMonoidHom.comp (centralizerLiftedLayerMap n hn S e)
  have hpi : Function.Surjective pi := theta.surjective.comp hU.restriction_surjective
  have hpiker : pi.ker = Subgroup.zpowers c :=
    (MonoidHom.ker_comp_of_injective _ _ theta.injective).trans hker
  have equaternion : centralizerLiftedLayerSylow hnonab n hn S e hfour ≃*
      QuaternionGroup (2 ^ ((n + 1) - 2)) := by
    rw [show n + 1 - 2 = n - 1 by omega, ← wreathed_two_pow_div_two n (by omega)]
    exact (centralizerLiftedLayerQuaternionEquiv hnonab n hn S e hfour).symm
  obtain ⟨etaLift, hprojective, hinvolution⟩ :=
    quaternion_central_double_cover_native F hF c hc hcenter pi hpi hpiker
      (centralizerLiftedLayerSylow hnonab n hn S e hfour) (n + 1) (by omega) equaternion
  let eta := (centralizerActualLayerEquiv hnonab n hn S e hfour).trans etaLift
  refine ⟨eta, ?_, ?_⟩
  · ext v
    have hv := DFunLike.congr_fun hprojective
      (centralizerActualLayerEquiv hnonab n hn S e hfour v)
    exact hv
  · change etaLift (centralizerActualLayerEquiv hnonab n hn S e hfour
      (centralizerActualLayerInvolution hnonab n hn S e hfour)) = _
    have heq : centralizerActualLayerEquiv hnonab n hn S e hfour
        (centralizerActualLayerInvolution hnonab n hn S e hfour) = c := by
      apply Subtype.ext
      exact centralizerActualLayerEquiv_coe hnonab n hn S e hfour _
    rw [heq]
    exact hinvolution

theorem exists_compatible_actual_layer_sl2_action_of_extension
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (rho : centralizerFullQuotient n hn S e →* coordinateE F)
    (hextends : ∀ l : centralizerSimpleLayer n hn S e,
      (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) :
    ∃ eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F,
      (nativeQuotient F).comp eta.toMonoidHom =
        theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour) ∧
      eta (centralizerActualLayerInvolution hnonab n hn S e hfour) = minusIdentity F ∧
      (∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
        coordinatePSLAction F (nativeQuotient F (eta v)) =
          (rho (centralizerFullQuotientMap n hn S e v)).val) := by
  obtain ⟨eta, hprojective, hinvolution⟩ :=
    exists_compatible_actual_layer_sl2 hnonab n hn S e hfour hF theta
  refine ⟨eta, hprojective, hinvolution, ?_⟩
  intro v
  have hv := DFunLike.congr_fun hprojective v
  change nativeQuotient F (eta v) = theta (centralizerActualLayerMap hnonab n hn S e hfour v) at hv
  rw [hv]
  have hvalue := hextends (centralizerActualLayerMap hnonab n hn S e hfour v)
  rw [centralizerActualLayerMap_coe] at hvalue
  exact hvalue.symm

theorem exists_compatible_actual_layer_semilinear_model
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {F : Type v} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (theta : centralizerSimpleLayer n hn S e ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    ∃ (rho : centralizerFullQuotient n hn S e →* coordinateE F)
      (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
        Matrix.SpecialLinearGroup (Fin 2) F),
      Function.Injective rho ∧
      (∀ l : centralizerSimpleLayer n hn S e,
        (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
      (centralizerSimpleLayer n hn S e).map rho =
        (coordinateG F).subgroupOf (coordinateE F) ∧
      (coordinateG F).subgroupOf (coordinateE F) ≤ rho.range ∧
      ((coordinateG F).subgroupOf (coordinateE F)).relIndex rho.range =
        (centralizerSimpleLayer n hn S e).index ∧
      (nativeQuotient F).comp eta.toMonoidHom =
        theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour) ∧
      eta (centralizerActualLayerInvolution hnonab n hn S e hfour) = minusIdentity F ∧
      (∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
        coordinatePSLAction F (nativeQuotient F (eta v)) =
          (rho (centralizerFullQuotientMap n hn S e v)).val) := by
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  let : IsSimpleGroup (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) := h.1
  let thetaCoordinate : CFSG.generalizedFitting (centralizerFullQuotient n hn S e) ≃*
      coordinateG F := theta.trans (pslEquivCoordinateG F)
  obtain ⟨rho, hrho, hextends, hmap, hcontains, hindex⟩ :=
    CFSG.Semidihedral.SemilinearLayerModel.generalizedFitting_semilinear_model_of_equiv
      h.2.1 thetaCoordinate
  obtain ⟨eta, hprojective, hinvolution, hvalues⟩ :=
    exists_compatible_actual_layer_sl2_action_of_extension hnonab n hn S e hfour hF theta rho hextends
  exact ⟨rho, eta, hrho, hextends, hmap, hcontains, hindex, hprojective, hinvolution, hvalues⟩

theorem actual_projective_layer_model_compatible_sl2
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F),
        Function.Injective rho ∧
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        (centralizerSimpleLayer n hn S e).map rho =
          (coordinateG F).subgroupOf (coordinateE F) ∧
        (coordinateG F).subgroupOf (coordinateE F) ≤ rho.range ∧
        ((coordinateG F).subgroupOf (coordinateE F)).relIndex rho.range =
          (centralizerSimpleLayer n hn S e).index ∧
        (nativeQuotient F).comp eta.toMonoidHom =
          theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour) ∧
        eta (centralizerActualLayerInvolution hnonab n hn S e hfour) = minusIdentity F ∧
        (∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
          coordinatePSLAction F (nativeQuotient F (eta v)) =
            (rho (centralizerFullQuotientMap n hn S e v)).val) := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨eModel⟩⟩ := hmodel.2
  let : Field F := hfield
  let : Finite F := hfinite
  let : CharP F p := CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F hp hcard
  have hchar : ringChar F = p := ringChar.eq F p
  have hF : ringChar F ≠ 2 := by rw [hchar]; exact hpodd
  let theta := eModel.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  obtain ⟨rho, eta, hrho, hextends, hmap, hcontains, hindex, hprojective, hinvolution, hvalues⟩ :=
    exists_compatible_actual_layer_semilinear_model hnonab n hn S e hfour hF theta
  exact ⟨F, hfield, hfinite, hcard, hchar, hcard ▸ Nat.one_lt_pow (by omega) hp.one_lt, theta, rho, eta,
    hrho, hextends, hmap, hcontains, hindex, hprojective, hinvolution, hvalues⟩

theorem actual_stated_projective_layer_model_compatible_sl2
    {G₀ : Type} [Group G₀] [Finite G₀] [IsSimpleGroup G₀]
    (hnonab : ∃ a b : G₀, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G₀) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      ringChar F = p ∧ 1 < Nat.card F ∧
      ∃ (theta : centralizerSimpleLayer n hn S e ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
        (rho : centralizerFullQuotient n hn S e →* coordinateE F)
        (eta : CFSG.layer (centralizerOddCoreQuotient n S e) ≃*
          Matrix.SpecialLinearGroup (Fin 2) F),
        Function.Injective rho ∧
        (∀ l : centralizerSimpleLayer n hn S e,
          (rho l.val).val = ((pslEquivCoordinateG F) (theta l)).val) ∧
        (centralizerSimpleLayer n hn S e).map rho =
          (coordinateG F).subgroupOf (coordinateE F) ∧
        (coordinateG F).subgroupOf (coordinateE F) ≤ rho.range ∧
        ((coordinateG F).subgroupOf (coordinateE F)).relIndex rho.range =
          (centralizerSimpleLayer n hn S e).index ∧
        (nativeQuotient F).comp eta.toMonoidHom =
          theta.toMonoidHom.comp (centralizerActualLayerMap hnonab n hn S e hfour) ∧
        eta (centralizerActualLayerInvolution hnonab n hn S e hfour) = minusIdentity F ∧
        (∀ v : CFSG.layer (centralizerOddCoreQuotient n S e),
          coordinatePSLAction F (nativeQuotient F (eta v)) =
            (rho (centralizerFullQuotientMap n hn S e v)).val) :=
  actual_projective_layer_model_compatible_sl2 hnonab n hn S e hfour p f hp hpodd hf
    ((pslTwoClassicalModel_iff_stated _ p f).mpr hmodel)

end CFSG.Wreathed.ActualProjectiveLayer
