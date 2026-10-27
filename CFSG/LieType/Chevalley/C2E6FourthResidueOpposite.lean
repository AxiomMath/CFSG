module

public import CFSG.LieType.Chevalley.C2E6FourthResidueWeyl

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Chevalley.CosetBuilding

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def wJ :
    relWeylTwist TwistTag.E6 :=
  (nativeSimple 0 * nativeSimple 1 * nativeSimple 2) ^ 3

abbrev wJword : List (Fin TwistTag.E6.tag.rank) :=
  (TwistTag.E6.orbitWord (foldedIndex 0) ++ TwistTag.E6.orbitWord (foldedIndex 1) ++
    TwistTag.E6.orbitWord (foldedIndex 2)) ++
  (TwistTag.E6.orbitWord (foldedIndex 0) ++ TwistTag.E6.orbitWord (foldedIndex 1) ++
    TwistTag.E6.orbitWord (foldedIndex 2)) ++
  (TwistTag.E6.orbitWord (foldedIndex 0) ++ TwistTag.E6.orbitWord (foldedIndex 1) ++
    TwistTag.E6.orbitWord (foldedIndex 2))

theorem coe_wJ :
    (wJ : WeylGroup TwistTag.E6.tag) = (coxeterSystem TwistTag.E6.tag).wordProd wJword := by
  simp only [wJ, wJword, Subgroup.coe_mul, coe_nativeSimple, TwistTag.orbitReflection,
    CoxeterSystem.wordProd_append, pow_succ, pow_zero, one_mul, mul_assoc]

theorem height_wJ_inv_smul : ∀ i : Fin 4, (i = 0 ∨ i = 1 ∨ i = 2) →
    ∀ j ∈ TwistTag.E6.orbit (foldedIndex i), height (wJword.reverse.foldr
      (reflect TwistTag.E6.tag) (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) < 0 := by
  decide

theorem isLongest_wJ
    : CFSG.Monster.B.Geometry.IsLongest nativeCoxeterSystem fourthJ wJ := by
  refine CFSG.Monster.B.Geometry.isLongest_of_forall_isLeftDescent ?_ fun i hi => ?_
  · have hs : ∀ i ∈ fourthJ, nativeSimple i ∈ nativeCoxeterSystem.parabolic fourthJ :=
      fun i hi => by
        rw [← nativeCoxeterSystem_simple]
        exact nativeCoxeterSystem.simple_mem_parabolic hi
    exact pow_mem (mul_mem (mul_mem (hs 0 (by simp [fourthJ])) (hs 1 (by simp [fourthJ])))
      (hs 2 (by simp [fourthJ]))) 3
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
    : CFSG.Monster.B.Geometry.longest nativeCoxeterSystem fourthJ = wJ :=
  isLongest_wJ.eq_longest.symm

theorem coe_wJ_eq_nativeRefl :
    (wJ : WeylGroup TwistTag.E6.tag) =
    (nativeRefl 0 * nativeRefl 1 * nativeRefl 2) ^ 3 := by
  change ((nativeSimple 0 * nativeSimple 1 * nativeSimple 2 : relWeylTwist TwistTag.E6) :
    WeylGroup TwistTag.E6.tag) ^ 3 = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_nativeSimple_eq_nativeRefl,
    coe_nativeSimple_eq_nativeRefl, coe_nativeSimple_eq_nativeRefl]
  rfl

abbrev wJLongest :
    WeylGroup TwistTag.E6.tag :=
  ((CFSG.Monster.B.Geometry.longest nativeCoxeterSystem fourthJ : relWeylTwist TwistTag.E6) :
    WeylGroup TwistTag.E6.tag)

theorem canonicalRep_nativeRefl_cube
    : canonicalRep (coxeterSystem Tag.E6) K
    ((nativeRefl 0 * nativeRefl 1 * nativeRefl 2) ^ 3) =
      (((natLevi 0 * natLevi 1 * natLevi 2) ^ 3 : stdLevi fourthJ) : ModGL Tag.E6 K) := by
  change canonicalRepHom _ = _
  rw [map_pow, map_mul, map_mul]
  rfl

theorem canonicalRep_longest :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K wJLongest =
      (((natLevi 0 * natLevi 1 * natLevi 2) ^ 3 : stdLevi fourthJ) : ModGL Tag.E6 K) := by
  rw [wJLongest, longest_eq_wJ, coe_wJ_eq_nativeRefl]
  exact canonicalRep_nativeRefl_cube

theorem canonicalRep_longest_mem :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K wJLongest ∈ nativeParabolic fourthJ := by
  rw [canonicalRep_longest]
  exact stdLevi_le_nativeParabolic two_mem_fourthJ ((natLevi 0 * natLevi 1 * natLevi 2) ^ 3).2

abbrev coxPerm : Equiv.Perm (Fin 3 ⊕ Fin 3) :=
  hypPerm 0 * hypPerm 1 * hypPerm 2

theorem rhoMinus_longest_hypVec
    (c : Fin 3 ⊕ Fin 3) :
    rhoMinus ((natLevi 0 * natLevi 1 * natLevi 2) ^ 3) (hypVec (ZMod 2) (Fin 2 → ZMod 2) c) =
      hypVec (ZMod 2) (Fin 2 → ZMod 2) ((coxPerm ^ 3) c) := by
  simp only [map_mul, pow_succ, pow_zero, one_mul, LinearEquiv.mul_apply, Equiv.Perm.mul_apply,
    rhoMinus_natLevi_hypVec]

theorem coxPerm_cube : ∀ j : Fin 3, (coxPerm ^ 3) (.inl j) = .inr j := by
  decide

theorem residueFlag_longest
    (k : Fin 3) :
    (residueFlag (QuotientGroup.mk ⟨_, canonicalRep_longest_mem⟩) :
        Fin 3 → Submodule (ZMod 2) V0) k =
      Submodule.span (ZMod 2)
        ((fun j : Fin 3 => hypVec (ZMod 2) (Fin 2 → ZMod 2) (.inr j)) '' {j | j ≤ k}) := by
  have e : (⟨_, canonicalRep_longest_mem⟩ : nativeParabolic fourthJ) =
      ⟨_, stdLevi_le_nativeParabolic two_mem_fourthJ
        ((natLevi 0 * natLevi 1 * natLevi 2) ^ 3).2⟩ :=
    Subtype.ext canonicalRep_longest
  rw [e, residueFlag_mk,
    leviProj_of_mem two_mem_fourthJ ((natLevi 0 * natLevi 1 * natLevi 2) ^ 3).2,
    Subtype.coe_eta, leviFlag_apply, baseFlag_apply, tailFlag, Submodule.map_span,
    Set.image_image]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe, rhoMinus_longest_hypVec,
    coxPerm_cube]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Fin.le_iff_val_le_val.mpr (by omega), rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := Fin.le_iff_val_le_val.mp hj; omega, rfl⟩

theorem map_baseFlag_sMinus (k : Fin 3) :
    (baseFlag k).map (sMinus : V0 →ₗ[ZMod 2] V0) = baseFlag k :=
  map_tailFlag_eq_of_hypVec (π := 1) (fun c => sMinus_hypVec c) fun j hj => ⟨j, hj, rfl⟩

theorem residueFlag_betaGL
    (p : nativeParabolic fourthJ) (k : Fin 3) :
    (residueFlag (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) :
        Fin 3 → Submodule (ZMod 2) V0) k =
      ((residueFlag (QuotientGroup.mk p) : Fin 3 → Submodule (ZMod 2) V0) k).map
        (sMinus : V0 →ₗ[ZMod 2] V0) := by
  change (leviCosetFlag (residueMap two_mem_fourthJ (QuotientGroup.mk ⟨betaGL p, _⟩)) :
    Fin 3 → Submodule (ZMod 2) V0) k = _
  rw [residueMap_betaGL, leviCosetFlag_mk, residueFlag_mk, leviFlag_apply, leviFlag_apply,
    rhoMinus_betaGL]
  have e : ∀ g : V0 ≃ₗ[ZMod 2] V0, (baseFlag k).map ((sMinus * g * sMinus : V0 ≃ₗ[ZMod 2] V0) :
      V0 →ₗ[ZMod 2] V0) = (((baseFlag k).map (sMinus : V0 →ₗ[ZMod 2] V0)).map
        (g : V0 →ₗ[ZMod 2] V0)).map (sMinus : V0 →ₗ[ZMod 2] V0) := fun g => by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  rw [e, map_baseFlag_sMinus]

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue
