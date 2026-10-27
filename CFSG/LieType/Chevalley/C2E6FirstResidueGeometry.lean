module

public import CFSG.LieType.Chevalley.C2E6FirstResidueOrder
public import CFSG.LieType.Chevalley.C2E6NativeF4Building
public import CFSG.LieType.Chevalley.C2E6StandardLeviResidue

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix
  CFSG.LieType.Chevalley.ExteriorCube CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.CosetBuilding
open scoped Pointwise

@[expose] def leviFlag
    (l : stdLevi firstJ) : IsoFlag6 :=
  suOf l • baseFlag

theorem leviFlag_liftSU
    (h : SU6) : leviFlag (liftSU h) = h • baseFlag :=
  suOf_liftSU_smul h baseFlag

theorem leviFlag_mul
    (l l' : stdLevi firstJ) : leviFlag (l * l') = suOf l • leviFlag l' :=
  suOf_mul_smul l l' baseFlag

theorem leviFlag_one :
    leviFlag 1 = baseFlag := by
  rw [← map_one liftSU, leviFlag_liftSU, one_smul]

theorem mem_stdLeviBorel_iff
    (l : stdLevi firstJ) :
    (l : ModGL Tag.E6 K) ∈ stdLeviBorel firstJ ↔ leviFlag l = baseFlag := by
  rw [← liftSU_suOf l, liftSU_mem_stdLeviBorel_iff, leviFlag_liftSU]

theorem leviFlag_eq_iff
    (l l' : stdLevi firstJ) :
    leviFlag l = leviFlag l' ↔ ((l⁻¹ * l' : stdLevi firstJ) : ModGL Tag.E6 K) ∈
      stdLeviBorel firstJ := by
  rw [mem_stdLeviBorel_iff, leviFlag_mul]
  have e : suOf l⁻¹ • leviFlag l' = (suOf l)⁻¹ • leviFlag l' :=
    smul_eq_of_liftSU_eq (by rw [liftSU_suOf, map_inv, liftSU_suOf]) _
  rw [e, inv_smul_eq_iff, eq_comm]
  rfl

@[expose] def leviCosetFlag :
    LeviCosets firstJ → IsoFlag6 :=
  Quotient.lift leviFlag fun x y hxy => by
    have h : x⁻¹ * y ∈ (stdLeviBorel firstJ).subgroupOf (stdLevi firstJ) :=
      QuotientGroup.leftRel_apply.mp hxy
    exact (leviFlag_eq_iff x y).mpr h

theorem leviCosetFlag_mk
    (l : stdLevi firstJ) :
    leviCosetFlag (QuotientGroup.mk l) = leviFlag l :=
  rfl

theorem leviCosetFlag_bijective
    : Function.Bijective leviCosetFlag := by
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [leviCosetFlag_mk, leviCosetFlag_mk, leviFlag_eq_iff] at hxy
    exact QuotientGroup.eq.mpr hxy
  · intro F
    obtain ⟨h, hh⟩ := exists_smul_eq baseFlag F
    exact ⟨QuotientGroup.mk (liftSU h), by rw [leviCosetFlag_mk, leviFlag_liftSU, hh]⟩

@[expose] def residueFlag
    : ParabolicCosets firstJ ≃ IsoFlag6 :=
  Equiv.ofBijective (leviCosetFlag ∘ residueMap two_mem_firstJ)
    (leviCosetFlag_bijective.comp (residueMap_bijective two_mem_firstJ))

theorem residueFlag_mk
    (p : nativeParabolic firstJ) :
    residueFlag (QuotientGroup.mk p) = leviFlag (leviProj two_mem_firstJ p) :=
  rfl

theorem residueFlag_one
    : residueFlag (QuotientGroup.mk 1) = baseFlag := by
  rw [residueFlag_mk, map_one, leviFlag_one]

theorem residueFlag_smul
    (p : nativeParabolic firstJ) {h : SU6}
    (hp : psiA ⟨((leviProj two_mem_firstJ p : stdLevi firstJ) : ModGL Tag.E6 K),
      stdLevi_firstJ_le_groupA (leviProj two_mem_firstJ p).2⟩ =
        cubeHom (h : SpecialLinearGroup (Fin 6) K))
    (x : ParabolicCosets firstJ) : residueFlag (p • x) = h • residueFlag x := by
  induction x using QuotientGroup.induction_on with | H x => ?_
  rw [MulAction.Quotient.smul_mk, residueFlag_mk, residueFlag_mk, smul_eq_mul, map_mul,
    leviFlag_mul,
    ← liftSU_eq_iff.mpr hp, suOf_liftSU_smul]

theorem smul_eq_self_iff
    (p : nativeParabolic firstJ) :
    (∀ x : ParabolicCosets firstJ, p • x = x) ↔ (p : ModGL Tag.E6 K) ∈ stdRadical firstJ := by
  rw [← leviProj_eq_one_iff two_mem_firstJ]
  set l := leviProj two_mem_firstJ p with hl
  have hpl := psiA_suOf l
  constructor
  · intro H
    have hF : ∀ F : IsoFlag6, suOf l • F = F := by
      intro F
      obtain ⟨x, rfl⟩ := residueFlag.surjective F
      rw [← residueFlag_smul p hpl, H x]
    have hz := mem_scalars_of_forall_smul_eq _ hF
    rw [← liftSU_suOf l]
    exact (liftSU_eq_one_iff _).mpr hz
  · intro h1 x
    apply residueFlag.injective
    rw [residueFlag_smul p hpl]
    have hz : (suOf l : SpecialLinearGroup (Fin 6) K) ∈ LinearFlag.scalars 6 K := by
      rw [← liftSU_eq_one_iff, liftSU_suOf]
      exact h1
    exact smul_eq_of_mem_scalars hz _

@[expose] def panelStab (d : Fin 3) : Subgroup SU6 where
  carrier := {h | ∀ k, k ≠ d → (h • baseFlag).sub k = baseFlag.sub k}
  mul_mem' {g h} hg hh k hk := by
    change ((g * h) • baseFlag).sub k = baseFlag.sub k
    rw [mul_smul, smul_sub g (h • baseFlag), hh k hk, ← smul_sub, hg k hk]
  one_mem' k _ := by
    change ((1 : SU6) • baseFlag).sub k = baseFlag.sub k
    rw [one_smul]
  inv_mem' {h} hh k hk := inv_smul_baseFlag_sub (hh k hk)

theorem mem_panelStab {d : Fin 3} {h : SU6} :
    h ∈ panelStab d ↔ ∀ k, k ≠ d → (h • baseFlag).sub k = baseFlag.sub k :=
  Iff.rfl

theorem liftSU_mem_stdLevi_leviParabolic
    {i : Fin 4} {h : SU6} (hh : h • baseFlag = baseFlag) :
    ((liftSU h : stdLevi firstJ) : ModGL Tag.E6 K) ∈ leviParabolic firstJ {i} :=
  Subgroup.subset_closure (Or.inl ((liftSU_mem_stdLeviBorel_iff h).mpr hh))

theorem mem_leviParabolic_iff
    {i : Fin 4} (hi : i ∈ firstJ) (l : stdLevi firstJ) :
    (l : ModGL Tag.E6 K) ∈ leviParabolic firstJ {i} ↔
      ∀ k, k ≠ typeDim i → (leviFlag l).sub k = baseFlag.sub k := by
  constructor
  · intro hl
    let T : Subgroup (ModGL Tag.E6 K) :=
      (panelStab (typeDim i)).map ((stdLevi firstJ).subtype.comp liftSU)
    have hle : leviParabolic firstJ {i} ≤ T := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | ⟨j, hj, rfl⟩)
      · have hxL := stdLeviBorel_le_stdLevi two_mem_firstJ hx
        refine ⟨suOf ⟨x, hxL⟩, fun k _ => ?_, ?_⟩
        · have := (mem_stdLeviBorel_iff ⟨x, hxL⟩).mp hx
          rw [leviFlag] at this
          rw [this]
        · change ((liftSU (suOf ⟨x, hxL⟩) : stdLevi firstJ) : ModGL Tag.E6 K) = x
          rw [liftSU_suOf]
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        refine ⟨weylSU (typeDim j), fun k hk => weylSU_smul_baseFlag_sub hk, ?_⟩
        change ((liftSU (weylSU (typeDim j)) : stdLevi firstJ) : ModGL Tag.E6 K) = nativeRep j
        rw [liftSU_weylSU hi]
    obtain ⟨h, hh, hhl⟩ := hle hl
    have e : liftSU h = l := Subtype.ext hhl
    rw [← e, leviFlag_liftSU]
    exact hh
  · intro H
    have hs : suOf l ∈ panelStab (typeDim i) := H
    rcases panel_factor (typeDim i) (suOf l) hs with h0 | ⟨a, ha, hs'⟩
    · rw [← liftSU_suOf l]
      exact liftSU_mem_stdLevi_leviParabolic h0
    · set g := bUpSU (typeDim i) ha * weylSU (typeDim i) with hg
      have e : suOf l = bUpSU (typeDim i) ha * weylSU (typeDim i) * (g⁻¹ * suOf l) := by
        rw [hg, mul_inv_cancel_left]
      rw [← liftSU_suOf l, e, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      refine mul_mem (mul_mem (liftSU_mem_stdLevi_leviParabolic (bUpSU_smul_baseFlag _ ha)) ?_)
        (liftSU_mem_stdLevi_leviParabolic hs')
      rw [liftSU_weylSU hi]
      exact Subgroup.subset_closure (Or.inr ⟨i, rfl, rfl⟩)

theorem inv_smul_sub_eq_iff (g : SU6) (G F : IsoFlag6) (k : Fin 3) :
    (g⁻¹ • G).sub k = F.sub k ↔ G.sub k = (g • F).sub k := by
  constructor
  · intro e
    rw [← smul_inv_smul g G, smul_sub g (g⁻¹ • G), e, ← smul_sub]
  · intro e
    have e2 : (g⁻¹ • G).sub k = (g⁻¹ • (g • F)).sub k := by
      rw [smul_sub, smul_sub g⁻¹ (g • F), e]
    rw [e2, inv_smul_smul]

theorem mem_nativeParabolic_singleton_iff
    {i : Fin 4} (hi : i ∈ firstJ)
    (x y : nativeParabolic firstJ) :
    ((x⁻¹ * y : nativeParabolic firstJ) : ModGL Tag.E6 K) ∈ nativeParabolic {i} ↔
      ∀ k, k ≠ typeDim i → (residueFlag (QuotientGroup.mk x)).sub k =
        (residueFlag (QuotientGroup.mk y)).sub k := by
  rw [adjacent_iff two_mem_firstJ (Set.singleton_subset_iff.mpr hi), mem_leviParabolic_iff hi,
    residueFlag_mk, residueFlag_mk, leviFlag_mul]
  have e : ∀ G : IsoFlag6, suOf (leviProj two_mem_firstJ x)⁻¹ • G =
      (suOf (leviProj two_mem_firstJ x))⁻¹ • G := fun G =>
    smul_eq_of_liftSU_eq (by rw [liftSU_suOf, map_inv, liftSU_suOf]) G
  refine forall₂_congr fun k _ => ?_
  rw [e, inv_smul_sub_eq_iff, eq_comm]
  rfl

@[expose] def wJ :
    relWeylTwist TwistTag.E6 :=
  (nativeSimple 1 * nativeSimple 2 * nativeSimple 3) ^ 3

abbrev wJword : List (Fin TwistTag.E6.tag.rank) :=
  (TwistTag.E6.orbitWord (foldedIndex 1) ++ TwistTag.E6.orbitWord (foldedIndex 2) ++
    TwistTag.E6.orbitWord (foldedIndex 3)) ++
  (TwistTag.E6.orbitWord (foldedIndex 1) ++ TwistTag.E6.orbitWord (foldedIndex 2) ++
    TwistTag.E6.orbitWord (foldedIndex 3)) ++
  (TwistTag.E6.orbitWord (foldedIndex 1) ++ TwistTag.E6.orbitWord (foldedIndex 2) ++
    TwistTag.E6.orbitWord (foldedIndex 3))

theorem coe_wJ :
    (wJ : WeylGroup TwistTag.E6.tag) = (coxeterSystem TwistTag.E6.tag).wordProd wJword := by
  simp only [wJ, wJword, Subgroup.coe_mul, coe_nativeSimple, TwistTag.orbitReflection,
    CoxeterSystem.wordProd_append, pow_succ, pow_zero, one_mul, mul_assoc]

theorem height_wJ_inv_smul : ∀ i : Fin 4, (i = 1 ∨ i = 2 ∨ i = 3) →
    ∀ j ∈ TwistTag.E6.orbit (foldedIndex i), height (wJword.reverse.foldr
      (reflect TwistTag.E6.tag) (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) < 0 := by
  decide

instance :
    Finite (relWeylTwist TwistTag.E6) :=
  Nat.finite_of_card_ne_zero (by rw [card_relWeylTwist_E6]; norm_num)

theorem isLongest_wJ
    : CFSG.Monster.B.Geometry.IsLongest nativeCoxeterSystem firstJ wJ := by
  refine CFSG.Monster.B.Geometry.isLongest_of_forall_isLeftDescent ?_ fun i hi => ?_
  · have hs : ∀ i ∈ firstJ, nativeSimple i ∈ nativeCoxeterSystem.parabolic firstJ := fun i hi => by
      rw [← nativeCoxeterSystem_simple]
      exact nativeCoxeterSystem.simple_mem_parabolic hi
    exact pow_mem (mul_mem (mul_mem (hs 1 (by simp [firstJ])) (hs 2 (by simp [firstJ])))
      (hs 3 (by simp [firstJ]))) 3
  · have hneg : ∀ j ∈ TwistTag.E6.orbit (foldedIndex i),
        height ((wJ : WeylGroup TwistTag.E6.tag)⁻¹ •
          (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) < 0 := fun j hj => by
      rw [coe_wJ, ← CoxeterSystem.wordProd_reverse, wordProd_smul]
      exact height_wJ_inv_smul i hi j hj
    have h := (length_orbitReflection_mul_of_neg TwistTag.E6 wJ.2 hneg).1
    rw [CoxeterSystem.IsLeftDescent, nativeCoxeterSystem_simple, nativeCoxeterSystem_length,
      nativeCoxeterSystem_length, Subgroup.coe_mul, coe_nativeSimple]
    omega

theorem longest_eq_wJ
    : CFSG.Monster.B.Geometry.longest nativeCoxeterSystem firstJ = wJ :=
  isLongest_wJ.eq_longest.symm

@[expose] def canonicalRepHom
    : WeylGroup Tag.E6 →* ModGL Tag.E6 K where
  toFun := canonicalRep (coxeterSystem Tag.E6) K
  map_one' := canonicalRep_one _ _
  map_mul' := canonicalRep_mul_charTwo

theorem canonicalRep_nativeRefl_cube
    : canonicalRep (coxeterSystem Tag.E6) K
    ((nativeRefl 1 * nativeRefl 2 * nativeRefl 3) ^ 3) =
      (nativeRep 1 * nativeRep 2 * nativeRep 3) ^ 3 := by
  change canonicalRepHom _ = _
  rw [map_pow, map_mul, map_mul]
  rfl

theorem coe_wJ_eq_nativeRefl :
    (wJ : WeylGroup TwistTag.E6.tag) =
    (nativeRefl 1 * nativeRefl 2 * nativeRefl 3) ^ 3 := by
  change ((nativeSimple 1 * nativeSimple 2 * nativeSimple 3 : relWeylTwist TwistTag.E6) :
    WeylGroup TwistTag.E6.tag) ^ 3 = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_nativeSimple_eq_nativeRefl,
    coe_nativeSimple_eq_nativeRefl, coe_nativeSimple_eq_nativeRefl]
  rfl

abbrev weylCube : SU6 := (weylSU 2 * weylSU 1 * weylSU 0) ^ 3

theorem suLin_weylSU_uVec (d : Fin 3) (j : Fin 6) :
    suLin (weylSU d) (uVec j) = uVec (weylPerm d j) :=
  weylMat_mulVec_uVec d j

theorem weylPerm_cube : ∀ j : Fin 6, weylPerm 2 (weylPerm 1 (weylPerm 0 (weylPerm 2
    (weylPerm 1 (weylPerm 0 (weylPerm 2 (weylPerm 1 (weylPerm 0 j)))))))) = Fin.rev j := by
  decide

theorem suLin_weylCube_uVec (j : Fin 6) : suLin weylCube (uVec j) = uVec (Fin.rev j) := by
  simp only [weylCube, pow_succ, pow_zero, one_mul, suLin_mul_apply, suLin_weylSU_uVec,
    weylPerm_cube]

theorem weylCube_eq_revSU : weylCube = revSU := by
  refine Subtype.ext (Subtype.ext ?_)
  ext i j
  have h := congrFun (suLin_weylCube_uVec j) i
  rw [suLin_apply, mulVec_uVec] at h
  rw [h, ← suLin_revSU_uVec, suLin_apply, mulVec_uVec]

theorem liftSU_weylCube :
    ((liftSU weylCube : stdLevi firstJ) : ModGL Tag.E6 K) =
      (nativeRep 1 * nativeRep 2 * nativeRep 3) ^ 3 := by
  have h1 : liftSU (weylSU 2) = ⟨nativeRep 1, nativeRep_mem_stdLevi (by simp [firstJ])⟩ :=
    liftSU_weylSU (i := 1) (by simp [firstJ])
  have h2 : liftSU (weylSU 1) = ⟨nativeRep 2, nativeRep_mem_stdLevi (by simp [firstJ])⟩ :=
    liftSU_weylSU (i := 2) (by simp [firstJ])
  have h3 : liftSU (weylSU 0) = ⟨nativeRep 3, nativeRep_mem_stdLevi (by simp [firstJ])⟩ :=
    liftSU_weylSU (i := 3) (by simp [firstJ])
  rw [weylCube, map_pow, map_mul, map_mul, h1, h2, h3]
  rfl

abbrev wJLongest :
    WeylGroup TwistTag.E6.tag :=
  ((CFSG.Monster.B.Geometry.longest nativeCoxeterSystem firstJ : relWeylTwist TwistTag.E6) :
    WeylGroup TwistTag.E6.tag)

theorem canonicalRep_longest :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K wJLongest =
      ((liftSU revSU : stdLevi firstJ) : ModGL Tag.E6 K) := by
  rw [wJLongest, longest_eq_wJ, coe_wJ_eq_nativeRefl, ← weylCube_eq_revSU, liftSU_weylCube]
  exact canonicalRep_nativeRefl_cube

theorem canonicalRep_longest_mem :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K wJLongest ∈ nativeParabolic firstJ := by
  rw [canonicalRep_longest]
  exact stdLevi_le_nativeParabolic two_mem_firstJ (liftSU revSU).2

theorem residueFlag_longest :
    residueFlag (QuotientGroup.mk ⟨_, canonicalRep_longest_mem⟩) = oppFlag := by
  rw [residueFlag_mk]
  have e : (⟨_, canonicalRep_longest_mem⟩ : nativeParabolic firstJ) =
      ⟨_, stdLevi_le_nativeParabolic two_mem_firstJ (liftSU revSU).2⟩ :=
    Subtype.ext canonicalRep_longest
  rw [e, leviProj_of_mem two_mem_firstJ (liftSU revSU).2]
  exact leviFlag_liftSU revSU

theorem liftSU_barSU
    (l : stdLevi firstJ) :
    liftSU (barSU (suOf l)) = ⟨betaGL l, betaGL_mem_stdLevi l.2⟩ := by
  refine liftSU_eq_iff.mpr ?_
  have e : (⟨betaGL (l : ModGL Tag.E6 K), stdLevi_firstJ_le_groupA
      (betaGL_mem_stdLevi l.2)⟩ : groupA) = betaA ⟨l, stdLevi_firstJ_le_groupA l.2⟩ := rfl
  rw [e]
  exact psiA_betaA (psiA_suOf l)

theorem residueFlag_betaGL
    (p : nativeParabolic firstJ) :
    residueFlag (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) =
      frobFlag (residueFlag (QuotientGroup.mk p)) := by
  change leviCosetFlag (residueMap two_mem_firstJ (QuotientGroup.mk ⟨betaGL p, _⟩)) = _
  rw [residueMap_betaGL, leviCosetFlag_mk, residueFlag_mk, ← liftSU_barSU, leviFlag_liftSU,
    leviFlag, frobFlag_smul, frobFlag_baseFlag]

@[expose] def nativeBaseIdx : Fin 3 → Finset (Fin 6) := ![{2}, {1, 2}, {0, 1, 2}]

@[expose] def nativeOppIdx : Fin 3 → Finset (Fin 6) := ![{5}, {4, 5}, {3, 4, 5}]

theorem map_nativeCoord_span (S : Set (Fin 6)) :
    (Submodule.span K (uVec '' S)).map (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Submodule.span K (uVec '' (Equiv.swap (0 : Fin 6) 2 '' S)) := by
  rw [Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun j _ => nativeCoord_uVec j

theorem swap_image_base : ∀ k : Fin 3, ∀ x : Fin 6,
    ((Equiv.swap (0 : Fin 6) 2).symm x : ℕ) < k + 1 ↔ x ∈ nativeBaseIdx k := by
  decide

theorem swap_image_opp : ∀ k : Fin 3, ∀ x : Fin 6,
    5 - (k : ℕ) ≤ ((Equiv.swap (0 : Fin 6) 2).symm x : ℕ) ↔ x ∈ nativeOppIdx k := by
  decide

theorem nativeCoord_baseFlag (k : Fin 3) :
    (baseFlag.sub k).map (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Submodule.span K (uVec '' (nativeBaseIdx k : Set (Fin 6))) := by
  rw [baseFlag_sub, preSpan_eq_span, map_nativeCoord_span]
  congr 2
  ext x
  rw [Set.mem_image_equiv, Set.mem_ofPred_eq, Finset.mem_coe]
  exact swap_image_base k x

theorem nativeCoord_oppFlag (k : Fin 3) :
    (oppFlag.sub k).map (nativeCoord : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Submodule.span K (uVec '' (nativeOppIdx k : Set (Fin 6))) := by
  rw [oppFlag_sub, map_nativeCoord_span]
  congr 2
  ext x
  rw [Set.mem_image_equiv, Set.mem_ofPred_eq, Finset.mem_coe]
  exact swap_image_opp k x

theorem nativeCoord_frob6 (v : Fin 6 → K) : nativeCoord (frob6 v) = frob6 (nativeCoord v) :=
  rfl

theorem baseFlag_sub_eq_span (k : Fin 3) :
    baseFlag.sub k = Submodule.span K (uVec '' {j | (j : ℕ) ≤ k}) := by
  rw [baseFlag_sub, preSpan_eq_span]
  congr 2
  ext j
  simp only [Set.mem_ofPred_eq]
  omega

theorem nativeParabolic_le_stdGroup
    (J : Set (Fin 4)) : nativeParabolic J ≤ stdGroup := by
  rw [nativeParabolic_eq]
  exact graphFixedParabolic_le _ _ _ _

@[expose] def parabolicToChamber
    : ParabolicCosets firstJ → stdChamber :=
  Quotient.lift (fun p : nativeParabolic firstJ =>
    ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber)) fun x y hxy => by
    have h : x⁻¹ * y ∈ stdBorel.subgroupOf (nativeParabolic firstJ) :=
      QuotientGroup.leftRel_apply.mp hxy
    exact QuotientGroup.eq.mpr h

theorem parabolicToChamber_mk
    (p : nativeParabolic firstJ) :
    parabolicToChamber (QuotientGroup.mk p) =
      ((⟨p, nativeParabolic_le_stdGroup _ p.2⟩ : stdGroup) : stdChamber) :=
  rfl

theorem parabolicToChamber_injective
    : Function.Injective parabolicToChamber := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [parabolicToChamber_mk, parabolicToChamber_mk, QuotientGroup.eq] at hxy
  exact QuotientGroup.eq.mpr hxy

theorem range_parabolicToChamber :
    Set.range parabolicToChamber =
    residue nativeCoxeterSystem stdDistance firstJ ((1 : stdGroup) : stdChamber) := by
  rw [residue_stdDistance, one_smul]
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with | H x => ?_
    exact ⟨⟨x, nativeParabolic_le_stdGroup _ x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk ⟨x, hx⟩, rfl⟩

theorem firstJ_eq : firstJ = {i : Fin 4 | (i : ℕ) ≠ 0} := by
  ext i
  fin_cases i <;> simp [firstJ]

theorem card_parabolicCosets_firstJ
    : Nat.card (ParabolicCosets firstJ) = 93555 := by
  rw [← Set.ncard_range_of_injective parabolicToChamber_injective, range_parabolicToChamber,
    firstJ_eq]
  exact ncard_residue_compl_stdDistance.1 _

theorem card_stdLevi_firstJ
    : Nat.card (stdLevi firstJ) = 9196830720 := by
  rw [← ((stdLeviBorel firstJ).subgroupOf (stdLevi firstJ)).index_mul_card, Subgroup.index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (stdLeviBorel_le_stdLevi two_mem_firstJ)).toEquiv, card_stdLeviBorel_firstJ,
    ← Nat.card_congr (Equiv.ofBijective _ (residueMap_bijective two_mem_firstJ)),
    card_parabolicCosets_firstJ]
  norm_num

end CFSG.LieType.Chevalley.C2E6Std
