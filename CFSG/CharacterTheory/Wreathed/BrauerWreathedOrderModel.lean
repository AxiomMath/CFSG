module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderCover
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation

public noncomputable section

open scoped Classical

namespace CFSG.Wreathed.BrauerWreathedOrder

open Matrix CFSG.DesarguesianPlanes CFSG.BrauerLinearThree CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.WreathedCentralCover CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)}
  {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  (φ : Subgroup.centralizer ({wreathModelHom S e (Original.x (2 ^ n))} : Set G) ≃*
    GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hq3 : 3 ≤ Nat.card F)

omit [Finite F] [Z.Normal] in
include hZ in
theorem le_ker_projGenLinGroupMk : Z ≤ (ProjGenLinGroup.mk : GL (Fin 2) F →* _).ker := by
  intro A hA
  rw [ProjGenLinGroup.ker_mk]
  exact le_center_GL hZ hA

@[expose] def pglCentralizer : involutionCentralizer n S e →* ProjGenLinGroup (Fin 2) F :=
  (QuotientGroup.lift Z ProjGenLinGroup.mk (le_ker_projGenLinGroupMk hZ)).comp φ.toMonoidHom

omit [Finite G] [Finite F] in
theorem pglCentralizer_centralizerHom (A : GL (Fin 2) F) :
    pglCentralizer φ hZ (centralizerHom φ A) = ProjGenLinGroup.mk A := by
  change QuotientGroup.lift Z ProjGenLinGroup.mk (le_ker_projGenLinGroupMk hZ)
    (φ (φ.symm (QuotientGroup.mk A))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [Finite G] in
include hZodd h2 hq3 in
theorem oddCore_le_ker_pglCentralizer :
    centralizerOddCore n S e ≤ (pglCentralizer φ hZ).ker := by
  intro c hc
  obtain ⟨A, rfl⟩ := centralizerHom_surjective φ c
  obtain ⟨a, -, rfl⟩ := (centralizerHom_mem_oddCore_iff φ hZ hZodd h2 hq3 A).mp hc
  change pglCentralizer φ hZ (centralizerHom φ _) = 1
  rw [pglCentralizer_centralizerHom, ProjGenLinGroup.mk_scalar]

@[expose] def pglOddQuotient : centralizerOddCoreQuotient n S e →* ProjGenLinGroup (Fin 2) F :=
  QuotientGroup.lift (centralizerOddCore n S e) (pglCentralizer φ hZ)
    (oddCore_le_ker_pglCentralizer φ hZ hZodd h2 hq3)

omit [Finite G] in
theorem pglOddQuotient_quotHom (A : GL (Fin 2) F) :
    pglOddQuotient φ hZ hZodd h2 hq3 (quotHom φ A) = ProjGenLinGroup.mk A :=
  pglCentralizer_centralizerHom φ hZ A

omit [Finite G] in
theorem centralizerFullCenter_generator_coe :
    ((wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n)) : involutionCentralizer n S e) : G) =
        wreathModelHom S e (Original.a (2 ^ n)) := rfl

variable {α₀ : Fˣ}
  (hα₀ : linearCentralizerHom φ (GeneralLinearGroup.scalar (Fin 2) α₀) =
    wreathModelHom S e (Original.a (2 ^ n)))

omit [Finite G] [Finite F] in
include hα₀ in
theorem centralizerFullCenter_generator_eq :
    wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.a (2 ^ n)) = centralizerHom φ (GeneralLinearGroup.scalar (Fin 2) α₀) := by
  apply Subtype.ext
  rw [coe_centralizerHom, hα₀]
  rfl

omit [Finite G] [Finite F] in
include hα₀ in
theorem mem_centralizerFullCenterImage_iff (y : centralizerOddCoreQuotient n S e) :
    y ∈ centralizerFullCenterImage n hn S e ↔
      ∃ k : ℤ, y = quotHom φ (GeneralLinearGroup.scalar (Fin 2) α₀) ^ k := by
  rw [centralizerFullCenterImage, centralizerFullCenter_eq_zpowers,
    centralizerFullCenter_generator_eq hn φ hα₀, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ⟨k, map_zpow (centralizerOddCoreMap n S e) _ k⟩
  · rintro ⟨k, rfl⟩
    exact ⟨_, Subgroup.zpow_mem_zpowers _ k, map_zpow (centralizerOddCoreMap n S e) _ k⟩

omit [Finite G] in
include hα₀ in
theorem fullCenterImage_le_ker_pglOddQuotient :
    centralizerFullCenterImage n hn S e ≤ (pglOddQuotient φ hZ hZodd h2 hq3).ker := by
  intro y hy
  obtain ⟨k, rfl⟩ := (mem_centralizerFullCenterImage_iff hn φ hα₀ y).mp hy
  change pglOddQuotient φ hZ hZodd h2 hq3 (quotHom φ _ ^ k) = 1
  rw [map_zpow, pglOddQuotient_quotHom, ProjGenLinGroup.mk_scalar, _root_.one_zpow]

@[expose] def pglQuotient : centralizerFullQuotient n hn S e →* ProjGenLinGroup (Fin 2) F :=
  QuotientGroup.lift (centralizerFullCenterImage n hn S e) (pglOddQuotient φ hZ hZodd h2 hq3)
    (fullCenterImage_le_ker_pglOddQuotient hn φ hZ hZodd h2 hq3 hα₀)

theorem pglQuotient_mk (A : GL (Fin 2) F) :
    pglQuotient hn φ hZ hZodd h2 hq3 hα₀ (centralizerFullQuotientMap n hn S e (quotHom φ A)) =
      ProjGenLinGroup.mk A :=
  pglOddQuotient_quotHom φ hZ hZodd h2 hq3 A

omit [Finite F] in
theorem exists_quotHom_eq (γ : centralizerFullQuotient n hn S e) :
    ∃ A : GL (Fin 2) F, centralizerFullQuotientMap n hn S e (quotHom φ A) = γ := by
  obtain ⟨y, rfl⟩ := centralizerFullQuotientMap_surjective n hn S e γ
  obtain ⟨A, rfl⟩ := quotHom_surjective φ y
  exact ⟨A, rfl⟩

theorem pglQuotient_surjective : Function.Surjective (pglQuotient hn φ hZ hZodd h2 hq3 hα₀) := by
  intro g
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective g
  exact ⟨_, pglQuotient_mk hn φ hZ hZodd h2 hq3 hα₀ A⟩

variable {d : ℕ} (hqd : Nat.card F - 1 = 2 ^ n * d) (hd : Odd d)

include hqd hd in
theorem pglQuotient_injective (hα₀sq : ¬ IsSquare α₀) :
    Function.Injective (pglQuotient hn φ hZ hZodd h2 hq3 hα₀) := by
  let _ : Fintype F := Fintype.ofFinite F
  have hqd' := hqd
  rw [Nat.card_eq_fintype_card] at hqd'
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨A, rfl⟩ := exists_quotHom_eq hn φ γ
  rw [pglQuotient_mk, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hγ
  obtain ⟨y, rfl⟩ := hγ
  obtain ⟨k, w, hw, rfl⟩ := exists_eq_pow_mul_odd hqd' hd hα₀sq y
  rw [map_mul, map_mul, quotHom_scalar_of_odd φ hZ hZodd h2 hq3 hw, mul_one]
  refine (QuotientGroup.eq_one_iff (N := centralizerFullCenterImage n hn S e) _).mpr ?_
  exact (mem_centralizerFullCenterImage_iff hn φ hα₀ _).mpr ⟨k, by rw [map_pow, map_pow,
    zpow_natCast]⟩

@[expose] def modelRho : centralizerFullQuotient n hn S e →* coordinateE F :=
  ((coordinatePGLAction F).comp (pglQuotient hn φ hZ hZodd h2 hq3 hα₀)).codRestrict
    (coordinateE F) (fun _ => coordinateD_le_E F
      ((coordinatePGLAction_range_eq_D F) ▸ ⟨_, rfl⟩))

theorem modelRho_apply (γ : centralizerFullQuotient n hn S e) :
    (modelRho hn φ hZ hZodd h2 hq3 hα₀ γ : Equiv.Perm (Omega F)) =
      coordinatePGLAction F (pglQuotient hn φ hZ hZodd h2 hq3 hα₀ γ) := rfl

theorem modelRho_mk (A : GL (Fin 2) F) :
    (modelRho hn φ hZ hZodd h2 hq3 hα₀ (centralizerFullQuotientMap n hn S e (quotHom φ A)) :
      Equiv.Perm (Omega F)) = coordinatePGLAction F (ProjGenLinGroup.mk A) := by
  rw [modelRho_apply, pglQuotient_mk]

include hqd hd in
theorem modelRho_injective (hα₀sq : ¬ IsSquare α₀) :
    Function.Injective (modelRho hn φ hZ hZodd h2 hq3 hα₀) := by
  intro γ δ h
  apply pglQuotient_injective hn φ hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq
  apply coordinatePGLAction_injective F
  rw [← modelRho_apply, ← modelRho_apply, h]

omit [Finite F] in
theorem fieldExtension_bot (σ : (⊥ : Subgroup (F ≃+* F))) :
    fieldExtension F (σ : F ≃+* F) = 1 := by
  have hσ : (σ : F ≃+* F) = 1 := Subgroup.mem_bot.mp σ.2
  rw [hσ]
  apply Equiv.ext
  intro x
  cases x <;> rfl

theorem modelRho_range :
    (modelRho hn φ hZ hZodd h2 hq3 hα₀).range = CFSG.Semidihedral.OddFieldLift.Gamma F ⊥ := by
  rw [CFSG.Semidihedral.OddFieldLift.Gamma, CFSG.Semidihedral.SemilinearOddExtensions.liftedField,
    Subgroup.map_bot, sup_bot_eq]
  ext x
  rw [MonoidHom.mem_range, CFSG.Semidihedral.SemilinearOddExtensions.linearLayer,
    Subgroup.mem_subgroupOf, ← coordinatePGLAction_range_eq_D F]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨_, (modelRho_apply hn φ hZ hZodd h2 hq3 hα₀ γ).symm⟩
  · rintro ⟨g, hg⟩
    obtain ⟨γ, rfl⟩ := pglQuotient_surjective hn φ hZ hZodd h2 hq3 hα₀ g
    exact ⟨γ, Subtype.ext ((modelRho_apply hn φ hZ hZodd h2 hq3 hα₀ γ).trans hg)⟩

omit [Finite F] in
theorem pglTopEquiv_symm_mk (A : GL (Fin 2) F) :
    (pglTopEquiv (F := F)).symm
        (QuotientGroup.mk (⟨A, Subgroup.mem_top A⟩ : (⊤ : Subgroup (GL (Fin 2) F)))) =
      ProjGenLinGroup.mk A :=
  (MulEquiv.symm_apply_eq _).mpr rfl

omit [Finite F] in
theorem slCoordinateAction_eq (X : SpecialLinearGroup (Fin 2) F) :
    CFSG.Semidihedral.OddFieldLift.slCoordinateAction F X =
      coordinatePGLAction F (ProjGenLinGroup.mk (SpecialLinearGroup.toGL X)) := by
  rw [CFSG.Semidihedral.OddFieldLift.slCoordinateAction, MonoidHom.comp_apply,
    ← coordinatePGLAction_toPGL]
  rfl

include hqd hd in
theorem modelRho_layer (hα₀sq : ¬ IsSquare α₀) (hF5 : 5 ≤ Nat.card F) :
    (centralizerSimpleLayer n hn S e).map (modelRho hn φ hZ hZodd h2 hq3 hα₀) =
      CFSG.Semidihedral.SemilinearOddExtensions.specialLayer F := by
  set κ := pglQuotient hn φ hZ hZodd h2 hq3 hα₀ with hκdef
  have hκ : Function.Bijective κ :=
    ⟨pglQuotient_injective hn φ hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq,
      pglQuotient_surjective hn φ hZ hZodd h2 hq3 hα₀⟩
  let θ : centralizerFullQuotient n hn S e ≃* (⊤ : Subgroup (GL (Fin 2) F)) ⧸
      CFSG.Wreathed.DegreeThreeModelFullCenter.scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F)) :=
    (MulEquiv.ofBijective κ hκ).trans (pglTopEquiv (F := F))
  have hFodd : Odd (Nat.card F) := by
    let _ : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two (ringChar_ne_two_of h2)
  have hFit := open CFSG.Wreathed.DegreeThreeModelFullCenter in
    matrix_overgroup_generalizedFitting_eq_projectiveSpecial hFodd hF5 (RingHom.id F) 1 ⊤ le_top
      (card_top_GL (F := F))
  have hmap := CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv θ
  have hL : centralizerSimpleLayer n hn S e =
      (CFSG.Wreathed.DegreeThreeModelFullCenter.projectiveSpecialHom (RingHom.id F) 1 ⊤
        le_top).range.map θ.symm.toMonoidHom := by
    rw [← hFit, ← hmap, Subgroup.map_map]
    have hid : θ.symm.toMonoidHom.comp θ.toMonoidHom = MonoidHom.id _ := by
      ext γ
      exact θ.symm_apply_apply γ
    rw [hid, Subgroup.map_id]
    rfl
  have hval : ∀ X : SpecialLinearGroup (Fin 2) F,
      (modelRho hn φ hZ hZodd h2 hq3 hα₀ (θ.symm
        (CFSG.Wreathed.DegreeThreeModelFullCenter.projectiveSpecialHom (RingHom.id F) 1 ⊤
          le_top X)) : Equiv.Perm (Omega F)) =
        CFSG.Semidihedral.OddFieldLift.slCoordinateAction F X := by
    intro X
    rw [modelRho_apply, slCoordinateAction_eq]
    congr 1
    change κ ((MulEquiv.ofBijective κ hκ).symm ((pglTopEquiv (F := F)).symm _)) = _
    rw [show κ ((MulEquiv.ofBijective κ hκ).symm ((pglTopEquiv (F := F)).symm
        (CFSG.Wreathed.DegreeThreeModelFullCenter.projectiveSpecialHom (RingHom.id F) 1 ⊤
          le_top X))) = (pglTopEquiv (F := F)).symm
          (CFSG.Wreathed.DegreeThreeModelFullCenter.projectiveSpecialHom (RingHom.id F) 1 ⊤
            le_top X) from (MulEquiv.ofBijective κ hκ).apply_symm_apply _]
    have hX : CFSG.Wreathed.DegreeThreeModelFullCenter.projectiveSpecialHom (RingHom.id F) 1 ⊤
        le_top X = QuotientGroup.mk (⟨SpecialLinearGroup.toGL X, Subgroup.mem_top _⟩ :
          (⊤ : Subgroup (GL (Fin 2) F))) := by
      change QuotientGroup.mk (CFSG.Wreathed.DegreeThreeModelFullCenter.specialInclusion
        (RingHom.id F) 1 ⊤ le_top X) = _
      congr 1
      apply Subtype.ext
      apply Units.ext
      change ((1 : GL (Fin 2) F) * CFSG.Semidihedral.OddLinearNormals.entrywiseSL (RingHom.id F) X *
        (1 : GL (Fin 2) F)⁻¹ : Matrix (Fin 2) (Fin 2) F) = _
      rw [inv_one, Units.val_one, mul_one, one_mul,
        CFSG.Semidihedral.OddLinearNormals.entrywiseSL_matrix]
      rfl
    rw [hX, pglTopEquiv_symm_mk]
  rw [hL, Subgroup.map_map, ← MonoidHom.range_comp]
  ext x
  rw [MonoidHom.mem_range, CFSG.Semidihedral.SemilinearOddExtensions.specialLayer,
    Subgroup.mem_subgroupOf, ← WreathedCentralCover.slCoordinateAction_range F]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X, (hval X).symm⟩
  · rintro ⟨X, hX⟩
    exact ⟨X, Subtype.ext ((hval X).trans hX)⟩

include hqd hd in
theorem modelRho_action (b : Fˣ) (hb : ¬ IsSquare b) (hnb : ¬ IsSquare (-b))
    (X : SpecialLinearGroup (Fin 2) F) (j : ZMod (2 * 2 ^ n)) (σ : (⊥ : Subgroup (F ≃+* F))) :
    ((modelRho hn φ hZ hZodd h2 hq3 hα₀ (centralizerFullQuotientMap n hn S e
        (semilinearEquiv φ hZ hZodd h2 hq3 hqd hd hn b hb hnb
          ⟨quotientClass F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) X j, σ⟩)) :
        coordinateE F) : Equiv.Perm (Omega F)) =
      coordinatePGLAction F (ProjGenLinGroup.mk
        (SpecialLinearGroup.toGL X * nonsquareMatrix F b ^ j.val)) * fieldExtension F σ := by
  rw [semilinearEquiv_apply, modelRho_mk, fieldExtension_bot, mul_one]

include hqd hd in
theorem conditionalCompatibleModelData (p f : ℕ) (hcard : Nat.card F = p ^ f)
    (hα₀sq : ¬ IsSquare α₀) (hF5 : 5 ≤ Nat.card F) (b : Fˣ) (hb : ¬ IsSquare b)
    (hnb : ¬ IsSquare (-b)) :
    ConditionalCompatibleModelData n hn S e p f F ⊥ b (bot_fixes b)
      (modelRho hn φ hZ hZodd h2 hq3 hα₀)
      (semilinearEquiv φ hZ hZodd h2 hq3 hqd hd hn b hb hnb) where
  card := hcard
  sigma_cyclic := inferInstance
  sigma_odd := by
    rw [Subgroup.card_bot]
    exact odd_one
  sigma_dvd := by
    rw [Subgroup.card_bot]
    exact one_dvd f
  nonsquare := hb
  rho_injective := modelRho_injective hn φ hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq
  rho_layer := modelRho_layer hn φ hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq hF5
  rho_range := modelRho_range hn φ hZ hZodd h2 hq3 hα₀
  action := compatible_action_of_eq_semilinearAction
    (modelRho_action hn φ hZ hZodd h2 hq3 hα₀ hqd hd b hb hnb)

include φ hZ hZodd h2 hq3 hα₀ hqd hd in
theorem centralizerSimpleLayer_sylow_not_isCyclic (hα₀sq : ¬ IsSquare α₀) (p f : ℕ)
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f)
    (hF5 : 5 ≤ Nat.card F) (U : Sylow 2 (centralizerSimpleLayer n hn S e)) :
    ¬ IsCyclic (U : Subgroup (centralizerSimpleLayer n hn S e)) := by
  set κ := pglQuotient hn φ hZ hZodd h2 hq3 hα₀ with hκdef
  have hκ : Function.Bijective κ :=
    ⟨pglQuotient_injective hn φ hZ hZodd h2 hq3 hα₀ hqd hd hα₀sq,
      pglQuotient_surjective hn φ hZ hZodd h2 hq3 hα₀⟩
  let θ : centralizerFullQuotient n hn S e ≃* (⊤ : Subgroup (GL (Fin 2) F)) ⧸
      CFSG.Wreathed.DegreeThreeModelFullCenter.scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F)) :=
    (MulEquiv.ofBijective κ hκ).trans (pglTopEquiv (F := F))
  obtain ⟨hs, hnab, -, -, -, hcardL, -⟩ := open CFSG.Wreathed.DegreeThreeModelFullCenter in
    matrix_overgroup_generalizedFitting_full_conclusions (F := F) (E := F) p f hp hpodd hf
      (hcard ▸ hF5) hcard (RingHom.id F) 1 ⊤ le_top (card_top_GL (F := F))
  set L' := CFSG.generalizedFitting ((⊤ : Subgroup (GL (Fin 2) F)) ⧸
    CFSG.Wreathed.DegreeThreeModelFullCenter.scalarSubgroup (⊤ : Subgroup (GL (Fin 2) F)))
  have hmap : (centralizerSimpleLayer n hn S e).map θ.toMonoidHom = L' :=
    CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv θ
  let eL : centralizerSimpleLayer n hn S e ≃* L' :=
    ((centralizerSimpleLayer n hn S e).equivMapOfInjective θ.toMonoidHom θ.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have : IsSimpleGroup L' := hs
  have : IsSimpleGroup (centralizerSimpleLayer n hn S e) := eL.isSimpleGroup
  have hnabL : ∃ a b : centralizerSimpleLayer n hn S e, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eL.symm a, eL.symm b, fun h => hab (eL.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have : Group.IsPerfect (centralizerSimpleLayer n hn S e) :=
    CFSG.Semidihedral.CoreFreeDihedral.isPerfect_of_simple_nonabelian hnabL
  have heven : Even (Nat.card (centralizerSimpleLayer n hn S e)) := by
    rw [Nat.card_congr eL.toEquiv, hcardL, ← hcard]
    have hqodd : Odd (Nat.card F) := hcard ▸ hpodd.pow
    obtain ⟨k, hk⟩ := hqodd
    rw [hk]
    refine ⟨k * (2 * k + 1) * (k + 1), ?_⟩
    have e1 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
      rw [show (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 by ring]
      omega
    rw [e1, show (2 * k + 1) * (4 * k * (k + 1)) = 2 * (2 * (k * (2 * k + 1) * (k + 1))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    ring
  exact CFSG.TwoRankLowerBound.Helpers.sylow_two_not_isCyclic_of_perfect _ heven U

end CFSG.Wreathed.BrauerWreathedOrder
