module

public import CFSG.CharacterTheory.Wreathed.FourPointResidual
public import CFSG.CharacterTheory.Wreathed.WreathedCentralCover
public import CFSG.CharacterTheory.Wreathed.ActualCentralizerSemilinear
public import CFSG.CharacterTheory.Semidihedral.FourPointQuotient
public import CFSG.LinearAlgebra.LinearGroups.SmallFieldModels

public noncomputable section

namespace CFSG.Wreathed.FourPointCompleteModel

open Equiv CFSG.Semidihedral.FourPointLifts
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CyclicCentralSL2Extension

theorem fourKlein_normal : fourKlein.Normal := by
  constructor
  intro x hx g
  rw [mem_fourKlein] at hx ⊢
  revert g
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem mem_fourKlein_of_commute : ∀ g : Perm (Fin 4),
    (swap 0 1 * swap 2 3) * g = g * (swap 0 1 * swap 2 3) →
    (swap 0 2 * swap 1 3) * g = g * (swap 0 2 * swap 1 3) →
    g = 1 ∨ g = swap 0 1 * swap 2 3 ∨ g = swap 0 2 * swap 1 3 ∨ g = swap 0 3 * swap 1 2 := by
  decide

theorem centralizer_fourKlein :
    Subgroup.centralizer (fourKlein : Set (Perm (Fin 4))) = fourKlein := by
  apply le_antisymm
  · intro g hg
    rw [mem_fourKlein]
    exact mem_fourKlein_of_commute g
      (Subgroup.mem_centralizer_iff.mp hg _ double_transposition_mem_fourKlein)
      (Subgroup.mem_centralizer_iff.mp hg _
        ((mem_fourKlein _).2 (Or.inr (Or.inr (Or.inl rfl)))))
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, mem_fourKlein] at hh
    rw [mem_fourKlein] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;> decide

open scoped Classical

variable {G : Type} [Group G] [Finite G]

theorem quotientMap_comp_surjective (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) :
    Function.Surjective (alpha.toMonoidHom.comp (centralizerFullQuotientMap n hn S e)) :=
  alpha.surjective.comp (centralizerFullQuotientMap_surjective n hn S e)

theorem fourPointQ_normal (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) :
    (fourKlein.comap (alpha.toMonoidHom.comp (centralizerFullQuotientMap n hn S e))).Normal := by
  have := fourKlein_normal
  infer_instance

theorem fourPointQ_centralizer_le (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) :
    Subgroup.centralizer ((fourKlein.comap (alpha.toMonoidHom.comp
        (centralizerFullQuotientMap n hn S e)) : Subgroup _) :
          Set (centralizerOddCoreQuotient n S e)) ≤
      fourKlein.comap (alpha.toMonoidHom.comp (centralizerFullQuotientMap n hn S e)) := by
  set f := alpha.toMonoidHom.comp (centralizerFullQuotientMap n hn S e) with hfdef
  have hf : Function.Surjective f := quotientMap_comp_surjective n hn S e alpha
  intro h hh
  rw [Subgroup.mem_comap, ← centralizer_fourKlein, Subgroup.mem_centralizer_iff]
  intro v hv
  obtain ⟨q, rfl⟩ := hf v
  have hq : q ∈ fourKlein.comap f := hv
  have hc := Subgroup.mem_centralizer_iff.mp hh q hq
  have h' := congrArg f hc
  rwa [map_mul, map_mul] at h'

theorem fourPointQ_card (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4))
    (hH : Nat.card (centralizerOddCoreQuotient n S e) = 96) :
    Nat.card (fourKlein.comap (alpha.toMonoidHom.comp
      (centralizerFullQuotientMap n hn S e))) = 16 := by
  have hidx := Subgroup.index_comap_of_surjective fourKlein
    (quotientMap_comp_surjective n hn S e alpha)
  have hV := Subgroup.card_mul_index fourKlein
  rw [CFSG.Semidihedral.FourPointQuotient.fourKlein_card, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hV
  have hV6 : fourKlein.index = 6 := by
    have : (24 : ℕ) = Nat.factorial 4 := by decide
    omega
  have h := Subgroup.card_mul_index (fourKlein.comap (alpha.toMonoidHom.comp
    (centralizerFullQuotientMap n hn S e)))
  rw [hidx, hV6, hH] at h
  omega

@[expose] def twoUnit : (ZMod 3)ˣ := ⟨2, 2, by decide, by decide⟩

theorem twoUnit_val : (twoUnit : ZMod 3) = 2 := rfl

theorem two_mem_fixedField :
    (2 : ZMod 3) ∈ CFSG.Semidihedral.MatrixCover.FixedField (ZMod 3) ⊥ := by
  show ∀ m : (⊥ : Subgroup (ZMod 3 ≃+* ZMod 3)), m • (2 : ZMod 3) = 2
  rintro ⟨m, hm⟩
  rw [Subgroup.mem_bot] at hm
  subst hm
  rfl

@[expose] def fixedTwoUnit : (CFSG.Semidihedral.MatrixCover.FixedField (ZMod 3) ⊥)ˣ :=
  ⟨⟨2, two_mem_fixedField⟩, ⟨2, two_mem_fixedField⟩,
    Subtype.ext (show (2 : ZMod 3) * 2 = 1 by decide),
    Subtype.ext (show (2 : ZMod 3) * 2 = 1 by decide)⟩

theorem fixedTwoUnit_not_isSquare : ¬ IsSquare fixedTwoUnit := by
  rintro ⟨c, hc⟩
  have h := congrArg (fun v : (CFSG.Semidihedral.MatrixCover.FixedField (ZMod 3) ⊥)ˣ =>
    (((v : CFSG.Semidihedral.MatrixCover.FixedField (ZMod 3) ⊥)) : ZMod 3)) hc
  simp only [Units.val_mul, Subfield.coe_mul] at h
  have key : ∀ y : ZMod 3, (2 : ZMod 3) ≠ y * y := by decide
  exact key _ h

@[expose] def semidirectBotEquiv {N K : Type*} [Group N] [Group K]
    (φ : (⊥ : Subgroup K) →* MulAut N) : N ≃* N ⋊[φ] (⊥ : Subgroup K) :=
  MulEquiv.ofBijective SemidirectProduct.inl ⟨SemidirectProduct.inl_injective, fun x =>
    ⟨x.left, SemidirectProduct.ext rfl (Subsingleton.elim _ _)⟩⟩

theorem semidirectBotEquiv_apply {N K : Type*} [Group N] [Group K]
    (φ : (⊥ : Subgroup K) →* MulAut N) (w : N) :
    semidirectBotEquiv φ w = ⟨w, 1⟩ := rfl

theorem semidirectBotEquiv_trans_sq {N K L : Type*} [Group N] [Group K] [Group L]
    (φ : (⊥ : Subgroup K) →* MulAut N) (Phi : N ⋊[φ] (⊥ : Subgroup K) ≃* L) (w : N) :
    ((semidirectBotEquiv φ).trans Phi) (w ^ 2) = Phi (⟨w, 1⟩ ^ 2) := by
  rw [MulEquiv.trans_apply, map_pow, semidirectBotEquiv_apply]

theorem gamma_three_eq_top : CFSG.Semidihedral.OddFieldLift.Gamma (ZMod 3) ⊥ = ⊤ := by
  apply top_unique
  intro x _
  apply Subgroup.mem_sup_left
  rw [Subgroup.mem_subgroupOf,
    CFSG.LinearGroups.three_element_field_projective_actions.{0, 0}.2.2.1]
  exact Subgroup.mem_top _

@[expose] def fourPointPhi (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) (β : Fin 4 ≃ Omega (ZMod 3)) :
    centralizerOddCoreQuotient n S e →* CFSG.Semidihedral.OddFieldLift.Gamma (ZMod 3) ⊥ :=
  (((FourPointResidual.coordinateAction n hn S e alpha β).toMonoidHom.comp
      (centralizerFullQuotientMap n hn S e)).codRestrict (coordinateE (ZMod 3)) fun h => by
      rw [CFSG.LinearGroups.three_element_field_projective_actions.{0, 0}.2.2.2.1]
      exact Subgroup.mem_top _).codRestrict
    (CFSG.Semidihedral.OddFieldLift.Gamma (ZMod 3) ⊥) fun h => by
      rw [gamma_three_eq_top]
      exact Subgroup.mem_top _

theorem fourPointPhi_coe (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) (β : Fin 4 ≃ Omega (ZMod 3))
    (h : centralizerOddCoreQuotient n S e) :
    (((fourPointPhi n hn S e alpha β h : CFSG.Semidihedral.OddFieldLift.Gamma (ZMod 3) ⊥) :
      coordinateE (ZMod 3)) : Perm (Omega (ZMod 3))) =
      FourPointResidual.coordinateAction n hn S e alpha β (centralizerFullQuotientMap n hn S e h) :=
  rfl

theorem fourPointPhi_surjective (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) (β : Fin 4 ≃ Omega (ZMod 3)) :
    Function.Surjective (fourPointPhi n hn S e alpha β) := by
  intro y
  obtain ⟨h, hh⟩ := centralizerFullQuotientMap_surjective n hn S e
    ((FourPointResidual.coordinateAction n hn S e alpha β).symm
      ((y : coordinateE (ZMod 3)) : Perm (Omega (ZMod 3))))
  refine ⟨h, Subtype.ext (Subtype.ext ?_)⟩
  change FourPointResidual.coordinateAction n hn S e alpha β
    (centralizerFullQuotientMap n hn S e h) = _
  rw [hh, MulEquiv.apply_symm_apply]

theorem fourPointPhi_ker (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) (β : Fin 4 ≃ Omega (ZMod 3)) :
    (fourPointPhi n hn S e alpha β).ker = centralizerFullCenterImage n hn S e := by
  ext h
  rw [MonoidHom.mem_ker]
  have key : fourPointPhi n hn S e alpha β h = 1 ↔ centralizerFullQuotientMap n hn S e h = 1 := by
    constructor
    · intro h1
      have h2 := congrArg (fun y : CFSG.Semidihedral.OddFieldLift.Gamma (ZMod 3) ⊥ =>
        ((y : coordinateE (ZMod 3)) : Perm (Omega (ZMod 3)))) h1
      change FourPointResidual.coordinateAction n hn S e alpha β
        (centralizerFullQuotientMap n hn S e h) = 1 at h2
      exact (map_eq_one_iff _ (FourPointResidual.coordinateAction n hn S e alpha β).injective).mp h2
    · intro h1
      apply Subtype.ext
      apply Subtype.ext
      change FourPointResidual.coordinateAction n hn S e alpha β
        (centralizerFullQuotientMap n hn S e h) = 1
      rw [h1, map_one]
  rw [key]
  exact QuotientGroup.eq_one_iff h

theorem four_point_sylow_inter_residual [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (hn2 : n = 2)
    (hT : Nat.card (centralizerResidualImage n hn S e) = 24) :
    (centralizerOddCoreSylow n hn S e : Subgroup (centralizerOddCoreQuotient n S e)) ⊓
        centralizerResidualImage n hn S e =
      modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) =
      (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) := by
    rw [modelY, centralizerOddCoreModelHom_comp, ← Subgroup.map_map]
    rfl
  have hYT : modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) ≤
      centralizerResidualImage n hn S e := by
    rw [hY]
    exact Subgroup.map_mono (centralizerQuaternion_le_transferKernel hnonab n hn S e)
  have hYP := modelY_le_sylow (centralizerOddCoreSylow n hn S e)
    (centralizerOddCoreCoordinates n hn S e)
  have hYcard : Nat.card (modelY (centralizerOddCoreSylow n hn S e)
      (centralizerOddCoreCoordinates n hn S e)) = 2 * 2 ^ n := by
    rw [modelY, Subgroup.card_map_of_injective (wreathModelHom_injective _ _),
      ← centralizerQuaternion_card n hn S e, centralizerQuaternion, modelY,
      Subgroup.card_map_of_injective (wreathModelHom_injective _ _)]
  have hle : Nat.card ((centralizerOddCoreSylow n hn S e : Subgroup _) ⊓
      centralizerResidualImage n hn S e : Subgroup _) ≤ 2 * 2 ^ n := by
    obtain ⟨k, hk⟩ := ((centralizerOddCoreSylow n hn S e).isPGroup'.to_le
      (inf_le_left : (centralizerOddCoreSylow n hn S e : Subgroup _) ⊓
        centralizerResidualImage n hn S e ≤ _)).exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right : (centralizerOddCoreSylow n hn S e :
      Subgroup _) ⊓ centralizerResidualImage n hn S e ≤ _)
    rw [hT, hk] at hdvd
    rw [hk, hn2]
    have hk3 : k ≤ 3 := by
      by_contra hk3
      push Not at hk3
      have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 hk3
      have h := h16.trans hdvd
      revert h
      decide
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 2 * 2 ^ 2 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge (le_inf hYP hYT) (by rw [hYcard]; exact hle)).symm

theorem exists_four_point_model_equiv [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) :
    ∃ Φ : CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide) ≃*
        centralizerOddCoreQuotient n S e,
      Φ (cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide) ^ 2) =
        centralizerOddCoreMap n S e (wreathModelHom (centralizerSylow n hn S e)
          (centralizerCoordinates n hn S e) (Original.a (2 ^ n))) ∧
      Φ (specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
          (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3))) =
        centralizerOddCoreMap n S e (centralInvolution n S e) := by
  obtain rfl := FourPointResidual.four_point_parameter n hn S e alpha
  have hres := FourPointResidual.four_point_full_center_quotient_actual_sl2_three_residual
    hnonab 2 hn S e alpha
  obtain ⟨β⟩ : Nonempty (Fin 4 ≃ Omega (ZMod 3)) := by
    apply Finite.card_eq.mp
    rw [Nat.card_eq_fintype_card, Fintype.card_fin,
      CFSG.LinearGroups.three_element_field_projective_actions.{0, 0}.1]
  obtain ⟨-, -, eta, heta, hcompat, -⟩ := hres.every_coordinate_bijection β
  have hSM := four_point_sylow_inter_residual hnonab 2 hn S e rfl hres.residual_card
  have hminus : eta (WreathedCentralCover.originalLayerX 2 hn (centralizerOddCoreSylow 2 hn S e)
      (centralizerOddCoreCoordinates 2 hn S e) (centralizerResidualImage 2 hn S e) hSM) =
      CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3) := by
    have hx : WreathedCentralCover.originalLayerX 2 hn (centralizerOddCoreSylow 2 hn S e)
        (centralizerOddCoreCoordinates 2 hn S e) (centralizerResidualImage 2 hn S e) hSM =
        centralizerResidualInvolution hnonab 2 hn S e :=
      Subtype.ext (ActualCentralizerSemilinear.actual_quotient_involution_value 2 hn S e)
    rw [hx]
    exact heta
  have hker := fourPointPhi_ker 2 hn S e alpha β
  have hcentral : (fourPointPhi 2 hn S e alpha β).ker ≤
      Subgroup.center (centralizerOddCoreQuotient 2 S e) := by
    rw [hker, hres.full_center]
  obtain ⟨-, -, -, -, hmodels, -⟩ :=
    WreathedCentralCover.wreathed_central_cover_exact_matrix_field_model_of_finite (ZMod 3)
      3 1 (by norm_num) (by decide) le_rfl (by simp) ⊥ (by simp) 2 hn
      (centralizerOddCoreSylow 2 hn S e) (centralizerOddCoreCoordinates 2 hn S e)
      (fourPointPhi 2 hn S e alpha β) (fourPointPhi_surjective 2 hn S e alpha β)
      (hker.trans (centralizerFullCenterImage_eq_modelCenter 2 hn S e)) hcentral
      (centralizerResidualImage 2 hn S e) hSM eta (fun v => hcompat v) hminus
  obtain ⟨-, -, -, -, -, -, -, Phi, -, hspecial, -, hgensq, -, -, -⟩ :=
    hmodels fixedTwoUnit fixedTwoUnit_not_isSquare
  refine ⟨(semidirectBotEquiv _).trans Phi, ?_, ?_⟩
  · exact (semidirectBotEquiv_trans_sq _ Phi _).trans
      (hgensq.trans (ActualCentralizerSemilinear.actual_quotient_wreath_value 2 hn S e _))
  · have h2 : ((eta.symm (CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity (ZMod 3)) :
        centralizerResidualImage 2 hn S e) : centralizerOddCoreQuotient 2 S e) =
        centralizerOddCoreMap 2 S e (centralInvolution 2 S e) := by
      rw [(MulEquiv.symm_apply_eq eta).mpr hminus.symm]
      exact ActualCentralizerSemilinear.actual_quotient_involution_value 2 hn S e
    exact (hspecial _).trans h2

end CFSG.Wreathed.FourPointCompleteModel
