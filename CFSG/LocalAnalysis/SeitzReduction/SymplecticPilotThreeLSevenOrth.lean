module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeLSevenGen
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOrthPlane
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeShortRows
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear consecutiveBlock)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open scoped MatrixGroups

section Iota

variable {F : Type} [Field F]

variable (F) in
@[expose] noncomputable def iota3 : SL(3, F) →* SL(2 * 2 + 1, F) :=
  (LinearPilot.reindexSpecialLinear (K := F) (Equiv.swap (3 : Fin (2 * 2 + 1)) 4)).toMonoidHom.comp
    (blockSL F (2 * 2 + 1) 3 2 (by norm_num))

theorem coe_iota3_apply (x : SL(3, F)) (a b : Fin (2 * 2 + 1)) :
    ((iota3 F x : SL(2 * 2 + 1, F)) : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) a b =
      CFSG.ClassicalInvolution.Phan.blockMat (2 * 2 + 1) 2 (x : Matrix (Fin 3) (Fin 3) F)
        (Equiv.swap (3 : Fin (2 * 2 + 1)) 4 a) (Equiv.swap (3 : Fin (2 * 2 + 1)) 4 b) := by
  change (reindex _ _ _) a b = _
  rw [reindex_apply, submatrix_apply, Equiv.symm_swap]
  rfl

end Iota

section IotaVals

variable {F : Type} [Field F]

theorem iota3_tr3_02 (c : F) :
    iota3 F (tr3 0 2 (by decide) c) =
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide) c := by
  apply Subtype.ext
  ext a b
  rw [coe_iota3_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply, coe_tr3,
    SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.swap_apply_def]

theorem iota3_tr3_20 (c : F) :
    iota3 F (tr3 2 0 (by decide) c) =
      SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 2 by decide) c := by
  apply Subtype.ext
  ext a b
  rw [coe_iota3_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply, coe_tr3,
    SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.swap_apply_def]

theorem iota3_tr3_01 (c : F) :
    iota3 F (tr3 0 1 (by decide) c) =
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 4 by decide) c := by
  apply Subtype.ext
  ext a b
  rw [coe_iota3_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply, coe_tr3,
    SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.swap_apply_def]

theorem iota3_tr3_12 (c : F) :
    iota3 F (tr3 1 2 (by decide) c) =
      SpecialLinearGroup.transvection (show (4 : Fin (2 * 2 + 1)) ≠ 3 by decide) c := by
  apply Subtype.ext
  ext a b
  rw [coe_iota3_apply, CFSG.ClassicalInvolution.Phan.blockMat_apply, coe_tr3,
    SpecialLinearGroup.transvection_coe]
  fin_cases a <;> fin_cases b <;>
    simp [Equiv.swap_apply_def]

theorem iota3_regUnip3 [CharP F 2] : iota3 F (regUnip3 F) = oddRegUnip F := by
  rw [regUnip3, map_mul, map_mul, iota3_tr3_01, iota3_tr3_12, iota3_tr3_02, oddRegUnip]

theorem range_iota3 : (iota3 F).range = blockSpecialLinear (K := F) oddFixBlock := by
  rw [iota3, MonoidHom.range_comp, LinearPilot.range_blockSL_eq, map_reindex_blockSpecialLinear]
  congr 1
  decide

end IotaVals

section OrthModel

variable {F : Type} [Field F] [CharP F 2]

theorem ctEmbed_longBlock_one_sl2Upper (c : F) :
    ctEmbed 1 (longBlock F 2 1 (CFSG.LieType.Steinberg.sl2Upper c)) =
      SpecialLinearGroup.transvection (show (2 : Fin (2 * 2 + 1)) ≠ 3 by decide) c := by
  apply Subtype.ext
  rw [coe_ctEmbed_longBlock_upper, SpecialLinearGroup.transvection_coe]
  rfl

theorem ctEmbed_longBlock_one_sl2Lower (c : F) :
    ctEmbed 1 (longBlock F 2 1 (CFSG.LieType.Steinberg.sl2Lower c)) =
      SpecialLinearGroup.transvection (show (3 : Fin (2 * 2 + 1)) ≠ 2 by decide) c := by
  apply Subtype.ext
  rw [coe_ctEmbed_longBlock_lower, SpecialLinearGroup.transvection_coe]
  rfl

omit [CharP F 2] in
theorem oddRegUnip_mul_oddZ : oddRegUnip F * oddZ F = oddZ F * oddRegUnip F := by
  apply Subtype.ext
  simp only [oddRegUnip, oddZ, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]; try ring)

end OrthModel

section Orth

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem phi_ctEmbed_longBlock_one [CharP K 2] (e : L ≃* StatedSp 3 K) {F : Type} [Field F]
    [CharP F 2] (σ : K ≃+* F) (Φ : SL(2 * 2 + 1, F) →* G)
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G)) (B : SL(2, F)) :
    Φ (ctEmbed 1 (longBlock F 2 1 B)) =
      ((e.symm (longBlock K 3 2 (Matrix.SpecialLinearGroup.map (σ.symm : F →+* K) B)) : L) :
        G) := by
  have hB : B = Matrix.SpecialLinearGroup.map (σ : K →+* F)
      (Matrix.SpecialLinearGroup.map (σ.symm : F →+* K) B) := by
    ext i j
    simp
  conv_lhs => rw [hB]
  rw [← spFieldMap_longBlock, spFieldMap_eq_statedSpMap, hN1, coe_complSpEquiv_apply,
    spEmbed_longBlock]
  rfl

theorem pieceCore_two_le_centralizer_simpleRootSL2_zero (hset : SeitzSetting G L)
    (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {F : Type} [Field F] [Finite F]
    [CharP F 2] (σ : K ≃+* F) (Φ : SL(2 * 2 + 1, F) →* G)
    (hrange : Φ.range = neighbourCore e 0) (hker : Φ.ker ≤ center SL(2 * 2 + 1, F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 0 x : complSp K 0) : L) : G))
    (hN3 : ∀ y, t * Φ y * t⁻¹ = Φ (ctGraph 1 y)) :
    pieceCore e ({2} : Finset (Fin 3)) ≤
      centralizer (modelToG e (simpleRootSL2 K (0 : Fin 3)) : Set G) := by
  classical
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  set J := modelToG e (longRootSp2 K 3 (2 : Fin 3)) with hJdef
  set J0 := modelToG e (simpleRootSL2 K (0 : Fin 3)) with hJ0def
  have hJ0J : J0 ≤ centralizer (J : Set G) :=
    modelToG_simpleRootSL2_zero_le_centralizer_longRootSp2_two e
  have hJJ0 : J ≤ centralizer (J0 : Set G) := le_centralizer_iff.1 hJ0J
  have hM2 := pieceCore_two_eq_of_oddStd hK e σ Φ hrange hker hN1
  set z : G := ((e.symm (siegDiag K 2 1) : L) : G) with hzdef
  have hz : Φ (oddZ F) = z := by
    have h1 : oddZ F = ctEmbed 1 (longBlock F 2 1 (CFSG.LieType.Steinberg.sl2Upper 1)) :=
      (ctEmbed_longBlock_one_sl2Upper 1).symm
    have h2 : Matrix.SpecialLinearGroup.map (σ.symm : F →+* K)
        (CFSG.LieType.Steinberg.sl2Upper (1 : F)) = CFSG.LieType.Steinberg.sl2Upper 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.SpecialLinearGroup.map_apply_coe]
    rw [h1, phi_ctEmbed_longBlock_one e σ Φ hN1, h2, hzdef, siegDiag_eq_longBlock,
      upperUnit_eq_sl2Upper]
  set g : G := Φ (oddRegUnip F) with hgdef
  have hgz : g * z = z * g := by
    rw [hgdef, ← hz, ← map_mul, ← map_mul, oddRegUnip_mul_oddZ]
  have hzL : z ∈ L := (e.symm _).2
  have hzt : z * t = t * z := mem_centralizer_iff.1 htC z hzL
  have hg : g⁻¹ * t * g = t * z := by
    have h1 : t * g * t⁻¹ = g * z := by
      rw [hgdef, hN3, ctGraph_oddRegUnip, map_mul, hz]
    calc g⁻¹ * t * g = g⁻¹ * (t * g * t⁻¹) * t := by group
      _ = z * t := by rw [h1]; group
      _ = t * z := hzt
  have hgM : g ∈ pieceCore e ({2} : Finset (Fin 3)) := by
    rw [hM2]
    exact ⟨_, oddRegUnip_mem, rfl⟩
  have hT02 : modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) ≤
      modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) :=
    UnitaryPilot.modelToG_mono e (leviTorusSp_anti (by decide))
  have hgY : g ∈ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) :=
    centralizer_le hT02 (centralizerPerfectCore_le_centralizer _ hgM)
  have hJY : J ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) := by
    rw [hJdef, ← simpleRootSL2_of_not_lt (by decide)]
    exact UnitaryPilot.modelToG_le_centralizer e
      (simpleRootSL2_le_centralizer_leviTorusSp (by decide))
  have hJ0Y : J0 ≤ centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) :=
    UnitaryPilot.modelToG_le_centralizer e (simpleRootSL2_le_centralizer_leviTorusSp (by decide))
  set φ' : StatedSp 3 K →* G :=
    (MulAut.conj g⁻¹).toMonoidHom.comp (L.subtype.comp e.symm.toMonoidHom) with hφ'def
  have hφ' : Function.Injective φ' :=
    (MulAut.conj g⁻¹).injective.comp (L.subtype_injective.comp e.symm.injective)
  have hφ'r : φ'.range = CFSG.conjugate L g := by
    rw [hφ'def, MonoidHom.range_comp, EPilot.range_subtype_comp_mulEquiv_symm]
    rfl
  have hφ'z : φ' (siegDiag K 2 1) = z := by
    change g⁻¹ * z * g⁻¹⁻¹ = z
    rw [((show Commute g z from hgz).inv_left).eq, mul_inv_cancel_right]
  set j : SL(2, K) →* G := φ'.comp (longBlock K 3 (2 : Fin 3)) with hjdef
  have := LinearPilot.isSimpleGroup_specialLinearGroup_two (K := K) hK
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have hj : ∀ A, j A = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g := by
    intro A
    change g⁻¹ * _ * g⁻¹⁻¹ = _
    rw [inv_inv]
    rfl
  have hjJ : ∀ A, ((e.symm (longBlock K 3 2 A) : L) : G) ∈ J := fun A =>
    symm_mem_modelToG e ⟨A, rfl⟩
  have hSt : j.range ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, hj]
    have hyt : ((e.symm (longBlock K 3 2 A) : L) : G) * t =
        t * ((e.symm (longBlock K 3 2 A) : L) : G) :=
      mem_centralizer_iff.1 htC _ (e.symm _).2
    have key : g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g * (g⁻¹ * t * g) =
        g⁻¹ * t * g * (g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g) := by
      calc g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g * (g⁻¹ * t * g) =
          g⁻¹ * (((e.symm (longBlock K 3 2 A) : L) : G) * t) * g := by group
        _ = g⁻¹ * (t * ((e.symm (longBlock K 3 2 A) : L) : G)) * g := by rw [hyt]
        _ = g⁻¹ * t * g * (g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g) := by group
    exact key
  have hSY : j.range ≤
      centralizer (modelToG e (leviTorusSp K ({0, 2} : Finset (Fin 3))) : Set G) := by
    rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    rw [hj]
    have h1 : w * g = g * w := mem_centralizer_iff.1 hgY w hw
    have h1' : w * g⁻¹ = g⁻¹ * w := (show Commute w g from h1).inv_right.eq
    have h2 : w * ((e.symm (longBlock K 3 2 A) : L) : G) =
        ((e.symm (longBlock K 3 2 A) : L) : G) * w :=
      mem_centralizer_iff.1 (hJY (hjJ A)) w hw
    calc w * (g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g) =
        g⁻¹ * (w * ((e.symm (longBlock K 3 2 A) : L) : G)) * g := by
          rw [← mul_assoc, ← mul_assoc, h1']
          group
      _ = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * (w * g) := by rw [h2]; group
      _ = g⁻¹ * ((e.symm (longBlock K 3 2 A) : L) : G) * g * w := by rw [h1]; group
  have hzS : z ∈ j.range := by
    refine ⟨LinearPilot.upperUnit 1, ?_⟩
    rw [hj, ← siegDiag_eq_longBlock, ← hzdef, mul_assoc, ← hgz, inv_mul_cancel_left]
  have hBperf : ⁅J0, J0⁆ = J0 := by
    rw [hJ0def, UnitaryPilot.modelToG_def, ← map_commutator, ← map_commutator,
      commutator_simpleRootSL2_eq_of_four_le hK 0]
  have hBL : J0 ≤ L := by
    rw [hJ0def, UnitaryPilot.modelToG_def]
    exact map_subtype_le _
  have hBz : J0 ≤ centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have hzJ : z ∈ J := symm_mem_modelToG e (siegDiag_mem_longRootSp2 2 1)
    exact (mem_centralizer_iff.1 (hJ0J hx) z hzJ).symm
  have hcore := le_centralizer_of_conj_eq_mul_three_two hset.standardSetting hOut hK e htC ht hg
    hφ' hφ'r hφ'z (LinearPilot.commutator_range_eq_self_of_isPerfect j)
    (LinearPilot.eq_bot_or_eq_top_of_normal_range j) hSt hSY hzS hBperf hBL hBz hJ0Y
  set H : Subgroup SL(3, F) := ((centralizer (J0 : Set G)).comap Φ).comap (iota3 F) with hH
  have hJF : ∀ B : SL(2, F), Φ (ctEmbed 1 (longBlock F 2 1 B)) ∈ centralizer (J0 : Set G) :=
    fun B => by rw [phi_ctEmbed_longBlock_one e σ Φ hN1]; exact hJJ0 (hjJ _)
  have hH02 : ∀ c : F, tr3 0 2 (by decide) c ∈ H := by
    intro c
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, iota3_tr3_02,
      ← ctEmbed_longBlock_one_sl2Upper]
    exact hJF _
  have hH20 : ∀ c : F, tr3 2 0 (by decide) c ∈ H := by
    intro c
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap, iota3_tr3_20,
      ← ctEmbed_longBlock_one_sl2Lower]
    exact hJF _
  have hHg : (regUnip3 F)⁻¹ * tr3 2 0 (by decide) 1 * regUnip3 F ∈ H := by
    rw [hH, Subgroup.mem_comap, Subgroup.mem_comap]
    simp only [map_mul, map_inv]
    rw [iota3_regUnip3, iota3_tr3_20, ← ctEmbed_longBlock_one_sl2Lower,
      phi_ctEmbed_longBlock_one e σ Φ hN1, ← hgdef, ← hj]
    exact hcore ⟨_, rfl⟩
  have htop := eq_top_of_block_conj hH02 hH20 hHg
  rw [hM2, ← range_iota3]
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  have hx : x ∈ H := htop ▸ Subgroup.mem_top x
  exact hx

end Orth

section PairModel

variable {F : Type} [Field F]

@[expose] noncomputable def diagA (a : Fˣ) : SL(2 * 2 + 1, F) :=
  ⟨diagonal ![(a : F), 1, 1, 1, ((a⁻¹ : Fˣ) : F)], by simp [det_diagonal, Fin.prod_univ_five]⟩

@[expose] noncomputable def diagB (a : Fˣ) : SL(2 * 2 + 1, F) :=
  ⟨diagonal ![1, 1, 1, (a : F), ((a⁻¹ : Fˣ) : F)], by simp [det_diagonal, Fin.prod_univ_five]⟩

theorem coe_diagA (a : Fˣ) : ((diagA a : SL(2 * 2 + 1, F)) : Matrix (Fin (2 * 2 + 1))
    (Fin (2 * 2 + 1)) F) = diagonal ![(a : F), 1, 1, 1, ((a⁻¹ : Fˣ) : F)] := rfl

theorem coe_diagB (a : Fˣ) : ((diagB a : SL(2 * 2 + 1, F)) : Matrix (Fin (2 * 2 + 1))
    (Fin (2 * 2 + 1)) F) = diagonal ![1, 1, 1, (a : F), ((a⁻¹ : Fˣ) : F)] := rfl

noncomputable abbrev tr5 (i j : Fin (2 * 2 + 1)) (h : i ≠ j) (c : F) : SL(2 * 2 + 1, F) :=
  SpecialLinearGroup.transvection h c

theorem q2Coord_e0 : q2Coord 2 1 (Sum.inl (Sum.inl 0)) = (0 : Fin (2 * 2 + 1)) :=
  Fin.ext (by rw [q2Coord_inl_inl]; rfl)

theorem q2Coord_e1 : q2Coord 2 1 (Sum.inl (Sum.inl 1)) = (2 : Fin (2 * 2 + 1)) :=
  Fin.ext (by rw [q2Coord_inl_inl]; rfl)

theorem q2Coord_f0 : q2Coord 2 1 (Sum.inl (Sum.inr 0)) = (1 : Fin (2 * 2 + 1)) :=
  Fin.ext (by rw [q2Coord_inl_inr]; rfl)

theorem q2Coord_f1 : q2Coord 2 1 (Sum.inl (Sum.inr 1)) = (3 : Fin (2 * 2 + 1)) :=
  Fin.ext (by rw [q2Coord_inl_inr]; rfl)

theorem ctEmbed_shortBlock_sl2Upper [CharP F 2] (c : F) :
    ctEmbed 1 (shortBlock F (show (0 : Fin 2) ≠ 1 by decide) (CFSG.LieType.Steinberg.sl2Upper c)) =
      tr5 0 2 (by decide) c * tr5 3 1 (by decide) c := by
  apply Subtype.ext
  rw [shortBlock_sl2Upper, coe_ctEmbed_elt_difference, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply, ctE, ctF,
      q2Coord_e0, q2Coord_e1, q2Coord_f0, q2Coord_f1]

theorem ctEmbed_shortBlock_sl2Lower [CharP F 2] (c : F) :
    ctEmbed 1 (shortBlock F (show (0 : Fin 2) ≠ 1 by decide) (CFSG.LieType.Steinberg.sl2Lower c)) =
      tr5 2 0 (by decide) c * tr5 1 3 (by decide) c := by
  apply Subtype.ext
  rw [shortBlock_sl2Lower, coe_ctEmbed_elt_difference, Matrix.SpecialLinearGroup.coe_mul,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply, ctE, ctF,
      q2Coord_e0, q2Coord_e1, q2Coord_f0, q2Coord_f1]

end PairModel

section PairDiag

variable {F : Type} [Field F]

theorem diagA_mul_P (a : Fˣ) (c : F) :
    diagA a * (tr5 0 2 (by decide) c * tr5 3 1 (by decide) c) =
      (tr5 0 2 (by decide) ((a : F) * c) * tr5 3 1 (by decide) c) * diagA a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, coe_diagA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply,
      Matrix.diagonal_apply]

theorem diagA_mul_Q (a : Fˣ) (c : F) :
    diagA a * (tr5 2 0 (by decide) c * tr5 1 3 (by decide) c) =
      (tr5 2 0 (by decide) (((a⁻¹ : Fˣ) : F) * c) * tr5 1 3 (by decide) c) * diagA a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, coe_diagA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  all_goals field_simp

theorem diagB_mul_P (a : Fˣ) (c : F) :
    diagB a * (tr5 0 2 (by decide) c * tr5 3 1 (by decide) c) =
      (tr5 0 2 (by decide) c * tr5 3 1 (by decide) ((a : F) * c)) * diagB a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, coe_diagB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply,
      Matrix.diagonal_apply]

theorem diagB_mul_Q (a : Fˣ) (c : F) :
    diagB a * (tr5 2 0 (by decide) c * tr5 1 3 (by decide) c) =
      (tr5 2 0 (by decide) c * tr5 1 3 (by decide) (((a⁻¹ : Fˣ) : F) * c)) * diagB a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe, coe_diagB]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  all_goals field_simp

omit [Field F] in
theorem commute_tr5_02_31 [Field F] (c d : F) :
    tr5 0 2 (by decide) c * tr5 3 1 (by decide) d =
      tr5 3 1 (by decide) d * tr5 0 2 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]

omit [Field F] in
theorem commute_tr5_20_13 [Field F] (c d : F) :
    tr5 2 0 (by decide) c * tr5 1 3 (by decide) d =
      tr5 1 3 (by decide) d * tr5 2 0 (by decide) c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_five, Matrix.single_apply, Matrix.one_apply]

end PairDiag

section Pair

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem pieceCore_zero_le_centralizer_of_oddStd (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K)
    {F : Type} [Field F] [Finite F] [CharP F 2] (σ : K ≃+* F)
    (Φ : SL(2 * 2 + 1, F) →* G) (hrange : Φ.range = neighbourCore e 2)
    (hker : Φ.ker ≤ center SL(2 * 2 + 1, F))
    (hN1 : ∀ x : StatedSp 2 K, Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 x)) =
      ((e.symm (complSpEquiv 2 x : complSp K 2) : L) : G))
    (hJ0 : modelToG e (simpleRootSL2 K (0 : Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G)) :
    pieceCore e ({0} : Finset (Fin 3)) ≤
      centralizer (pieceCore e ({2} : Finset (Fin 3)) : Set G) := by
  have hF4 : 4 ≤ Nat.card F := (Nat.card_congr σ.toEquiv) ▸ hK
  set M := pieceCore e ({2} : Finset (Fin 3)) with hMdef
  set H : Subgroup SL(2 * 2 + 1, F) := (centralizer (M : Set G)).comap Φ with hH
  have hdiag : ∀ d : SL(2 * 2 + 1, F),
      (∀ i j, i ≠ j → (d : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) i j = 0) →
        ∀ x ∈ H, d * x * d⁻¹ ∈ H := by
    intro d hd x hx
    have hdY : Φ d ∈ centralizer (modelToG e (leviTorusSp K ({2} : Finset (Fin 3))) : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hw
      have hu2 : u 2 = 1 := (hu 2 (Finset.mem_singleton_self 2)).2 (by decide)
      have hw' : ((e.symm (diagSp K 3 u) : L) : G) =
          Φ (ctEmbed 1 (statedSpMap (σ : K →+* F) 2 (diagSp K 2 ![u 0, u 1]))) := by
        rw [hN1, coe_complSpEquiv_two_diagSp]
        congr 3
        funext i
        fin_cases i <;> simp [hu2]
      change ((e.symm (diagSp K 3 u) : L) : G) * Φ d = Φ d * ((e.symm (diagSp K 3 u) : L) : G)
      rw [hw', ← map_mul, ← map_mul]
      congr 1
      rw [statedSpMap_diagSp]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        coe_ctEmbed_diagSp_two]
      have hdd : (d : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) =
          diagonal fun i => (d : Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) i i := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · rw [hd i j hij, diagonal_apply_ne _ hij]
      rw [hdd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    have hdN : Φ d ∈ normalizer (M : Set G) :=
      LinearPilot.mem_normalizer_centralizerPerfectCore (centralizer_le_normalizer _ hdY)
    change Φ (d * x * d⁻¹) ∈ centralizer (M : Set G)
    rw [map_mul, map_mul, map_inv, mem_centralizer_iff]
    intro m hm
    have hm' : (Φ d)⁻¹ * m * (Φ d)⁻¹⁻¹ ∈ M := (mem_normalizer_iff.1 (inv_mem hdN) m).1 hm
    have hc := mem_centralizer_iff.1 hx _ hm'
    rw [inv_inv] at hc
    calc m * (Φ d * Φ x * (Φ d)⁻¹) = Φ d * ((Φ d)⁻¹ * m * Φ d * Φ x) * (Φ d)⁻¹ := by group
      _ = Φ d * (Φ x * ((Φ d)⁻¹ * m * Φ d)) * (Φ d)⁻¹ := by rw [hc]
      _ = Φ d * Φ x * (Φ d)⁻¹ * m := by group
  have hJ : ∀ A : SL(2, K), Φ (ctEmbed 1 (shortBlock F (show (0 : Fin 2) ≠ 1 by decide)
      (Matrix.SpecialLinearGroup.map (σ : K →+* F) A))) ∈ centralizer (M : Set G) := by
    intro A
    rw [← spFieldMap_shortBlock, spFieldMap_eq_statedSpMap, hN1, coe_complSpEquiv_apply]
    have h1 := congrArg (fun φ : SL(2, K) →* StatedSp 3 K => φ A)
      (spEmbed_comp_shortBlock_of_injective (K := K)
        (Fin.succAbove_right_injective (p := (2 : Fin 3)))
        (show (0 : Fin 2) ≠ 1 by decide))
    simp only [MonoidHom.comp_apply] at h1
    rw [h1]
    refine hJ0 (symm_mem_modelToG e ⟨A, ?_⟩)
    rw [simpleRootHom_of_lt (by decide)]
    rfl
  have hmapU : ∀ c : K, Matrix.SpecialLinearGroup.map (σ : K →+* F)
      (CFSG.LieType.Steinberg.sl2Upper c) = CFSG.LieType.Steinberg.sl2Upper (σ c) := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Steinberg.coe_sl2Upper, Matrix.SpecialLinearGroup.map_apply_coe]
  have hmapL : ∀ c : K, Matrix.SpecialLinearGroup.map (σ : K →+* F)
      (CFSG.LieType.Steinberg.sl2Lower c) = CFSG.LieType.Steinberg.sl2Lower (σ c) := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.LieType.Steinberg.coe_sl2Lower, Matrix.SpecialLinearGroup.map_apply_coe]
  have hP : ∀ c : F, tr5 0 2 (by decide) c * tr5 3 1 (by decide) c ∈ H := by
    intro c
    have h := hJ (CFSG.LieType.Steinberg.sl2Upper (σ.symm c))
    rwa [hmapU, RingEquiv.apply_symm_apply, ctEmbed_shortBlock_sl2Upper] at h
  have hQ : ∀ c : F, tr5 2 0 (by decide) c * tr5 1 3 (by decide) c ∈ H := by
    intro c
    have h := hJ (CFSG.LieType.Steinberg.sl2Lower (σ.symm c))
    rwa [hmapL, RingEquiv.apply_symm_apply, ctEmbed_shortBlock_sl2Lower] at h
  obtain ⟨a, ha⟩ := exists_units_ne_one_of_four_le hF4
  have hne : ∀ b : Fˣ, b ≠ 1 → (b : F) + 1 ≠ 0 := by
    intro b hb h
    apply hb
    apply Units.ext
    rw [Units.val_one]
    have : (b : F) = -1 := eq_neg_of_add_eq_zero_left h
    rw [this, CharTwo.neg_eq]
  have ha' : a⁻¹ ≠ 1 := fun h => ha (inv_eq_one.1 h)
  have hdA : ∀ i j, i ≠ j → ((diagA a : SL(2 * 2 + 1, F)) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) i j = 0 := fun i j hij => by
    rw [coe_diagA, diagonal_apply_ne _ hij]
  have hdB : ∀ i j, i ≠ j → ((diagB a : SL(2 * 2 + 1, F)) :
      Matrix (Fin (2 * 2 + 1)) (Fin (2 * 2 + 1)) F) i j = 0 := fun i j hij => by
    rw [coe_diagB, diagonal_apply_ne _ hij]
  have hconj : ∀ (d : SL(2 * 2 + 1, F)) (x y : SL(2 * 2 + 1, F)), d * x = y * d →
      d * x * d⁻¹ = y := fun d x y h => by rw [h, mul_inv_cancel_right]
  have h02 : ∀ c : F, tr5 0 2 (by decide) c ∈ H := by
    intro c
    set c' := c / ((a : F) + 1) with hc'
    have h1 := hdiag _ hdA _ (hP c')
    rw [hconj _ _ _ (diagA_mul_P a c')] at h1
    have h2 := mul_mem h1 (inv_mem (hP c'))
    have he : tr5 0 2 (by decide) ((a : F) * c') * tr5 3 1 (by decide) c' *
        (tr5 0 2 (by decide) c' * tr5 3 1 (by decide) c')⁻¹ = tr5 0 2 (by decide) c := by
      rw [_root_.mul_inv_rev, transvection_inv_charTwo, transvection_inv_charTwo, mul_assoc,
        ← mul_assoc (tr5 3 1 _ c'), transvection_mul_self_charTwo, one_mul,
        ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      calc (a : F) * c' + c' = ((a : F) + 1) * c' := by ring
        _ = c := by rw [hc', mul_div_cancel₀ _ (hne a ha)]
    rwa [he] at h2
  have h31 : ∀ c : F, tr5 3 1 (by decide) c ∈ H := by
    intro c
    set c' := c / ((a : F) + 1) with hc'
    have h1 := hdiag _ hdB _ (hP c')
    rw [hconj _ _ _ (diagB_mul_P a c')] at h1
    have h2 := mul_mem h1 (inv_mem (hP c'))
    have he : tr5 0 2 (by decide) c' * tr5 3 1 (by decide) ((a : F) * c') *
        (tr5 0 2 (by decide) c' * tr5 3 1 (by decide) c')⁻¹ = tr5 3 1 (by decide) c := by
      rw [commute_tr5_02_31, commute_tr5_02_31 c' c', _root_.mul_inv_rev, transvection_inv_charTwo,
        transvection_inv_charTwo, mul_assoc, ← mul_assoc (tr5 0 2 _ c'),
        transvection_mul_self_charTwo, one_mul, ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      calc (a : F) * c' + c' = ((a : F) + 1) * c' := by ring
        _ = c := by rw [hc', mul_div_cancel₀ _ (hne a ha)]
    rwa [he] at h2
  have h20 : ∀ c : F, tr5 2 0 (by decide) c ∈ H := by
    intro c
    set c' := c / (((a⁻¹ : Fˣ) : F) + 1) with hc'
    have h1 := hdiag _ hdA _ (hQ c')
    rw [hconj _ _ _ (diagA_mul_Q a c')] at h1
    have h2 := mul_mem h1 (inv_mem (hQ c'))
    have he : tr5 2 0 (by decide) (((a⁻¹ : Fˣ) : F) * c') * tr5 1 3 (by decide) c' *
        (tr5 2 0 (by decide) c' * tr5 1 3 (by decide) c')⁻¹ = tr5 2 0 (by decide) c := by
      rw [_root_.mul_inv_rev, transvection_inv_charTwo, transvection_inv_charTwo, mul_assoc,
        ← mul_assoc (tr5 1 3 _ c'), transvection_mul_self_charTwo, one_mul,
        ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      calc ((a⁻¹ : Fˣ) : F) * c' + c' = (((a⁻¹ : Fˣ) : F) + 1) * c' := by ring
        _ = c := by rw [hc', mul_div_cancel₀ _ (hne _ ha')]
    rwa [he] at h2
  have h13 : ∀ c : F, tr5 1 3 (by decide) c ∈ H := by
    intro c
    set c' := c / (((a⁻¹ : Fˣ) : F) + 1) with hc'
    have h1 := hdiag _ hdB _ (hQ c')
    rw [hconj _ _ _ (diagB_mul_Q a c')] at h1
    have h2 := mul_mem h1 (inv_mem (hQ c'))
    have he : tr5 2 0 (by decide) c' * tr5 1 3 (by decide) (((a⁻¹ : Fˣ) : F) * c') *
        (tr5 2 0 (by decide) c' * tr5 1 3 (by decide) c')⁻¹ = tr5 1 3 (by decide) c := by
      rw [commute_tr5_20_13, commute_tr5_20_13 c' c', _root_.mul_inv_rev, transvection_inv_charTwo,
        transvection_inv_charTwo, mul_assoc, ← mul_assoc (tr5 2 0 _ c'),
        transvection_mul_self_charTwo, one_mul, ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      calc ((a⁻¹ : Fˣ) : F) * c' + c' = (((a⁻¹ : Fˣ) : F) + 1) * c' := by ring
        _ = c := by rw [hc', mul_div_cancel₀ _ (hne _ ha')]
    rwa [he] at h2
  have hA : blockSpecialLinear (K := F) oddTwA ≤ H := by
    have hI : oddTwA = ({0, 2} : Finset (Fin (2 * 2 + 1))) := rfl
    rw [hI, ← LinearPilot.range_pairEmbed (show (0 : Fin (2 * 2 + 1)) ≠ 2 by decide)]
    rintro _ ⟨X, rfl⟩
    have hX := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 X
    refine (Subgroup.closure_le (H.comap (LinearPilot.pairEmbed _))).2 ?_ hX
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change LinearPilot.pairEmbed _ (CFSG.LieType.Steinberg.sl2Upper c) ∈ H
      rw [pairEmbed_sl2Upper]
      exact h02 c
    · change LinearPilot.pairEmbed _ (CFSG.LieType.Steinberg.sl2Lower c) ∈ H
      rw [pairEmbed_sl2Lower]
      exact h20 c
  have hB : blockSpecialLinear (K := F) oddTwB ≤ H := by
    have hI : oddTwB = ({3, 1} : Finset (Fin (2 * 2 + 1))) := by decide
    rw [hI, ← LinearPilot.range_pairEmbed (show (3 : Fin (2 * 2 + 1)) ≠ 1 by decide)]
    rintro _ ⟨X, rfl⟩
    have hX := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 X
    refine (Subgroup.closure_le (H.comap (LinearPilot.pairEmbed _))).2 ?_ hX
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change LinearPilot.pairEmbed _ (CFSG.LieType.Steinberg.sl2Upper c) ∈ H
      rw [pairEmbed_sl2Upper]
      exact h31 c
    · change LinearPilot.pairEmbed _ (CFSG.LieType.Steinberg.sl2Lower c) ∈ H
      rw [pairEmbed_sl2Lower]
      exact h13 c
  rw [pieceCore_zero_eq_of_oddStd hK e σ Φ hrange hker hN1, Subgroup.map_le_iff_le_comap]
  exact sup_le hA hB

end Pair

theorem spThreeLinearOddOrthInput_holds :
    SpThreeLinearOddOrthInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hroot hstd
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hK : 4 ≤ Nat.card K := hKc ▸ four_le_two_pow hf
  obtain ⟨F₀, _, _, _, σ₀, Φ₀, -, hr₀, hk₀, hN1₀, hN3₀⟩ :=
    spThreeOddGraphNormalized_of_standard hset hKc hf e htC ht 0 (hroot 0) hstd
  obtain ⟨F₂, _, _, _, σ₂, Φ₂, -, hr₂, hk₂, hN1₂, -⟩ :=
    spThreeOddGraphNormalized_of_standard hset hKc hf e htC ht 2 (hroot 2) hstd
  have h1 := pieceCore_two_le_centralizer_simpleRootSL2_zero hset hK e htC ht σ₀ Φ₀ hr₀ hk₀
    (fun x => hN1₀ x) hN3₀
  exact pieceCore_zero_le_centralizer_of_oddStd hK e σ₂ Φ₂ hr₂ hk₂ (fun x => hN1₂ x)
    (le_centralizer_iff.1 h1)

theorem spThreeLinearOddStandardInput_of_clauses
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3) :
    SpThreeLinearOddStandardInput :=
  spThreeLinearOddStandardInput_of_orth hcat hdet spThreeLinearOddOrthInput_holds

theorem spThreeKindCoverInput_linearOdd_of_catSL3
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) (hdet : LinearPilot.SLmEvenTypeDetAt 3) :
    SpThreeKindCoverInput .linearOdd :=
  spThreeKindCoverInput_linearOdd_of_orth hcat hdet spThreeLinearOddOrthInput_holds

section TypeDet


theorem spThreeKindCoverInput_linearOdd_of_catalogue
    (hcat : LinearPilot.SLmCatalogueClausesAt 3) : SpThreeKindCoverInput .linearOdd :=
  spThreeKindCoverInput_linearOdd_of_catSL3 hcat (LinearPilot.slmEvenTypeDetAt le_rfl)

end TypeDet

end CFSG.SeitzReduction.SymplecticPilot
