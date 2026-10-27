module

public import CFSG.LieType.Chevalley.E7Three.Centralizer
public import CFSG.LieType.Chevalley.E7Three.FourCube

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KA5L CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.FourCube CFSG.LieType.Chevalley.E7Three.Weyl

open scoped MatrixGroups Kronecker

variable {K L : Type} [Field K] [Field L]

theorem baseChangeGL_comp_a5Frame (f : K →+* L) :
    (baseChangeGL (τ := .E7) f).comp (a5Frame K) =
      (a5Frame L).comp (Matrix.SpecialLinearGroup.map f) := by
  refine CFSG.LieType.CurtisTits.hom_ext_of_iSup_eq_top (iSup_range_blockSL2 (K := K) 5) ?_
  rintro i ⟨_, A, rfl⟩
  have hb : Matrix.SpecialLinearGroup.map f (blockSL2 K 5 i A) =
      blockSL2 L 5 i (Matrix.SpecialLinearGroup.map f A) := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.map_apply_coe, blockSL2, coe_blockSL, blockSL2, coe_blockSL,
      Matrix.SpecialLinearGroup.map_apply_coe]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      CFSG.ClassicalInvolution.Phan.blockMat_apply]
    split_ifs with h
    · rfl
    · simp only [Matrix.one_apply]
      split_ifs <;> simp
  have h := DFunLike.congr_fun (a5Frame_comp_blockSL2 K i) A
  have h' := DFunLike.congr_fun (a5Frame_comp_blockSL2 L i) (Matrix.SpecialLinearGroup.map f A)
  simp only [MonoidHom.comp_apply] at h h' ⊢
  rw [h, hb, h', CFSG.RankThree.Chevalley.baseChangeGL_simpleRootSL2_of_field]

theorem baseChangeGL_a5Frame (f : K →+* L) (M : SL(6, K)) :
    baseChangeGL f (a5Frame K M) = a5Frame L (Matrix.SpecialLinearGroup.map f M) :=
  DFunLike.congr_fun (baseChangeGL_comp_a5Frame f) M

theorem map_kronSL2 (f : K →+* L) (M : SL(2, K)) :
    Matrix.SpecialLinearGroup.map f (kronSL2 K M) =
      kronSL2 L (Matrix.SpecialLinearGroup.map f M) := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_kronSL2, coe_kronSL2,
    Matrix.SpecialLinearGroup.map_apply_coe]
  ext p q
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.one_apply, apply_ite f]

variable [CharP K 2] [CharP L 2]

theorem baseChangeGL_cubeSL2 (f : K →+* L) (M : SL(2, K)) :
    baseChangeGL f (cubeSL2 K M) = cubeSL2 L (Matrix.SpecialLinearGroup.map f M) := by
  change baseChangeGL f (a5Frame K (kronSL2 K M)) = a5Frame L (kronSL2 L _)
  rw [baseChangeGL_a5Frame, map_kronSL2]

theorem baseChangeGL_rootDiagUnit_cubeChar (f : K →+* L) (ζ : Kˣ) (a : Fin Tag.E7.rank → ℤ) :
    baseChangeGL f (rootDiagUnit .E7 (cubeChar ζ a)) =
      rootDiagUnit .E7 (cubeChar (Units.map f.toMonoidHom ζ) a) := by
  rw [baseChangeGL_rootDiagUnit]
  congr 1
  funext i
  exact map_zpow _ ζ (a i)

theorem baseChangeGL_scalarWord (f : K →+* L) (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    baseChangeGL f (scalarWord ζ : ModGL .E7 K) = scalarWord (Units.map f.toMonoidHom ζ) := by
  rw [scalarWord_val ζ hζ, scalarWord_val _ (by rw [← map_pow, hζ, map_one]),
    baseChangeGL_rootDiagUnit_cubeChar]

theorem baseChangeGL_pairedWord (f : K →+* L) (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    baseChangeGL f (pairedWord ζ : ModGL .E7 K) = pairedWord (Units.map f.toMonoidHom ζ) := by
  rw [pairedWord_val ζ hζ, pairedWord_val _ (by rw [← map_pow, hζ, map_one]),
    baseChangeGL_rootDiagUnit_cubeChar]

theorem baseChangeGL_cyclic (f : K →+* L) :
    baseChangeGL f (cyclic (K := K) : ModGL .E7 K) = cyclic (K := L) := by
  change baseChangeGL f (canonicalRep (coxeterSystem .E7) K gamma) =
    canonicalRep (coxeterSystem .E7) L gamma
  exact baseChangeGL_canonicalRep f gamma

theorem baseChangeGL_cubeHom (f : K →+* L) (ζ : Kˣ) (hζ : ζ ^ 3 = 1)
    (x : Fin 3 → Multiplicative (ZMod 3)) :
    baseChangeGL f (cubeHom ζ hζ x : ModGL .E7 K) =
      cubeHom (Units.map f.toMonoidHom ζ) (by rw [← map_pow, hζ, map_one]) x := by
  rw [cubeHom_apply, cubeHom_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow, baseChangeGL_scalarWord f ζ hζ,
    baseChangeGL_pairedWord f ζ hζ, baseChangeGL_cyclic]

theorem map_baseChangeGL_cubeE (f : K →+* L) (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (cubeE ζ hζ).map (baseChangeGL f) =
      cubeE (Units.map f.toMonoidHom ζ) (by rw [← map_pow, hζ, map_one]) := by
  ext g
  constructor
  · rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, (baseChangeGL_cubeHom f ζ hζ x).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, baseChangeGL_cubeHom f ζ hζ x⟩

theorem cubeE_congr {ζ ζ' : Kˣ} (h : ζ = ζ') (hζ : ζ ^ 3 = 1) (hζ' : ζ' ^ 3 = 1) :
    cubeE ζ hζ = cubeE ζ' hζ' := by
  subst h
  rfl

theorem scalarWord_inv (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (scalarWord ζ⁻¹ : ModGL .E7 K) = (scalarWord ζ : ModGL .E7 K)⁻¹ := by
  rw [scalarWord_val _ (by rw [inv_pow, hζ, inv_one]), scalarWord_val ζ hζ,
    ← rootDiagUnit_cubeChar_neg]
  congr 1
  funext i
  change ζ⁻¹ ^ scalarExp i = ζ ^ (-scalarExp i)
  exact inv_zpow' ζ (scalarExp i)

theorem pairedWord_inv (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    (pairedWord ζ⁻¹ : ModGL .E7 K) = (pairedWord ζ : ModGL .E7 K)⁻¹ := by
  rw [pairedWord_val _ (by rw [inv_pow, hζ, inv_one]), pairedWord_val ζ hζ,
    ← rootDiagUnit_cubeChar_neg]
  congr 1
  funext i
  change ζ⁻¹ ^ pairedExp i = ζ ^ (-pairedExp i)
  exact inv_zpow' ζ (pairedExp i)

theorem cubeE_inv_le (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cubeE ζ⁻¹ (by rw [inv_pow, hζ, inv_one]) ≤ cubeE ζ hζ := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have h0 : (scalarWord ζ : ModGL .E7 K) ∈ cubeE ζ hζ := generators_mem_cubeE ζ hζ 0
  have h1 : (pairedWord ζ : ModGL .E7 K) ∈ cubeE ζ hζ := generators_mem_cubeE ζ hζ 1
  have h2 : (cyclic (K := K) : ModGL .E7 K) ∈ cubeE ζ hζ := generators_mem_cubeE ζ hζ 2
  change ((cubeHom ζ⁻¹ _ x : adjointGroup .E7 K) : ModGL .E7 K) ∈ cubeE ζ hζ
  rw [cubeHom_apply]
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, scalarWord_inv ζ hζ, pairedWord_inv ζ hζ]
  exact mul_mem (mul_mem (pow_mem (inv_mem h0) _) (pow_mem (inv_mem h1) _)) (pow_mem h2 _)

theorem cubeE_inv (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cubeE ζ⁻¹ (by rw [inv_pow, hζ, inv_one]) = cubeE ζ hζ := by
  refine le_antisymm (cubeE_inv_le ζ hζ) ?_
  have h := cubeE_inv_le ζ⁻¹ (by rw [inv_pow, hζ, inv_one])
  rwa [cubeE_congr (inv_inv ζ) _ hζ] at h

theorem units_map_eq_or_eq_inv (σ : K →+* K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    Units.map σ.toMonoidHom ζ = ζ ∨ Units.map σ.toMonoidHom ζ = ζ⁻¹ := by
  have hζK : IsPrimitiveRoot (ζ : K) 3 := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hξ : (σ (ζ : K)) ^ 3 = 1 := by rw [← map_pow, hζK.pow_eq_one, map_one]
  obtain ⟨i, hi, he⟩ := hζK.eq_pow_of_pow_eq_one hξ
  have hval : ((Units.map σ.toMonoidHom ζ : Kˣ) : K) = σ (ζ : K) := rfl
  interval_cases i
  · exfalso
    rw [pow_zero] at he
    exact hζK.ne_one (by norm_num) (σ.injective (by rw [← he, map_one]))
  · left
    exact Units.ext (by rw [hval, ← he, pow_one])
  · right
    refine Units.ext ?_
    rw [hval, ← he, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hζK.pow_eq_one])

theorem map_baseChangeGL_cubeE_self (σ : K →+* K) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    (cubeE ζ hζ.pow_eq_one).map (baseChangeGL σ) = cubeE ζ hζ.pow_eq_one := by
  rw [map_baseChangeGL_cubeE]
  rcases units_map_eq_or_eq_inv σ hζ with h | h
  · exact cubeE_congr h _ _
  · rw [cubeE_congr h _ (by rw [inv_pow, hζ.pow_eq_one, inv_one]), cubeE_inv]

end CFSG.LieType.Chevalley.E7Three.Centralizer
