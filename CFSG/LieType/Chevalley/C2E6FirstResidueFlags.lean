module

public import CFSG.LieType.Chevalley.C2E6FirstResidueForm
public import CFSG.LieType.Chevalley.C2E6UnitaryFourFrobenius
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherFlagExtension
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap Matrix Module
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def preSpan (k : ℕ) : Submodule K (Fin 6 → K) where
  carrier := {v | ∀ j : Fin 6, k ≤ (j : ℕ) → v j = 0}
  add_mem' {v w} hv hw j hj := by
    rw [Pi.add_apply, hv j hj, hw j hj, add_zero]
  zero_mem' _ _ := rfl
  smul_mem' c v hv j hj := by
    rw [Pi.smul_apply, hv j hj, smul_zero]

theorem mem_preSpan {k : ℕ} {v : Fin 6 → K} :
    v ∈ preSpan k ↔ ∀ j : Fin 6, k ≤ (j : ℕ) → v j = 0 :=
  Iff.rfl

theorem uVec_mem_preSpan {k : ℕ} {i : Fin 6} (hi : (i : ℕ) < k) : uVec i ∈ preSpan k :=
  fun j hj => Pi.single_eq_of_ne (fun h => by rw [h] at hj; omega) 1

@[expose] def preSpanOf (k : ℕ) (w : Fin k → K) : preSpan k :=
  ⟨fun i => if h : (i : ℕ) < k then w ⟨i, h⟩ else 0, fun _ hj => dite_eq_right (by omega)⟩

@[expose] def preSpanEquiv (k : ℕ) (hk : k ≤ 6) : preSpan k ≃ₗ[K] (Fin k → K) where
  toFun v j := (v : Fin 6 → K) (Fin.castLE hk j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := preSpanOf k
  left_inv v := by
    refine Subtype.ext (funext fun i => ?_)
    change (if h : (i : ℕ) < k then (v : Fin 6 → K) (Fin.castLE hk ⟨i, h⟩) else 0) =
      (v : Fin 6 → K) i
    by_cases h : (i : ℕ) < k
    · rw [dite_eq_left h]
      rfl
    · rw [dite_eq_right h]
      exact (v.2 i (by omega)).symm
  right_inv w := by
    funext j
    change (if h : ((Fin.castLE hk j : Fin 6) : ℕ) < k then w ⟨_, h⟩ else 0) = w j
    rw [dite_eq_left (by simp)]
    rfl

theorem finrank_preSpan {k : ℕ} (hk : k ≤ 6) : finrank K (preSpan k) = k := by
  rw [(preSpanEquiv k hk).finrank_eq, Module.finrank_fin_fun]

theorem preSpan_eq_span (k : ℕ) : preSpan k = Submodule.span K (uVec '' {j | (j : ℕ) < k}) := by
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < k
    · rw [show Pi.single j (v j) = v j • uVec j by rw [← Pi.single_smul, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hv j (by omega), Pi.single_zero]
      exact zero_mem _
  · rintro _ ⟨j, hj, rfl⟩
    exact uVec_mem_preSpan hj

theorem mulVec_uVec (M : Matrix (Fin 6) (Fin 6) K) (j i : Fin 6) : (M *ᵥ uVec j) i = M i j := by
  rw [mulVec_single_one, col_apply]

theorem map_preSpan_eq_iff (h : SpecialLinearGroup (Fin 6) K) (k : ℕ) :
    (preSpan k).map (SpecialLinearGroup.toLin' h : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
        preSpan k ↔
      ∀ i j : Fin 6, (j : ℕ) < k → k ≤ (i : ℕ) → (h : Matrix (Fin 6) (Fin 6) K) i j = 0 := by
  constructor
  · intro e i j hj hi
    have hmem : (h : Matrix (Fin 6) (Fin 6) K) *ᵥ uVec j ∈ preSpan k := by
      rw [← e]
      exact Submodule.mem_map_of_mem (uVec_mem_preSpan hj)
    have := hmem i hi
    rwa [mulVec_uVec] at this
  · intro H
    have hle : (preSpan k).map
        (SpecialLinearGroup.toLin' h : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) ≤ preSpan k := by
      rintro _ ⟨v, hv, rfl⟩ i hi
      change ((h : Matrix (Fin 6) (Fin 6) K) *ᵥ v) i = 0
      simp only [mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj : (j : ℕ) < k
      · rw [H i j hj hi, zero_mul]
      · rw [hv j (by omega), mul_zero]
    exact Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq _ _)

@[ext] structure IsoFlag6 where
  sub : Fin 3 → Submodule K (Fin 6 → K)
  finrank_sub : ∀ k, finrank K (sub k) = k + 1
  mono : Monotone sub
  isotropic : ∀ v ∈ sub 2, ∀ w ∈ sub 2, herm6 v w = 0

abbrev suLin (h : SU6) : (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) :=
  SpecialLinearGroup.toLin' (h : SpecialLinearGroup (Fin 6) K)

theorem suLin_apply (h : SU6) (v : Fin 6 → K) :
    suLin h v = ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *ᵥ v :=
  rfl

theorem suLin_mul (h h' : SU6) : suLin (h * h') = suLin h * suLin h' := by
  rw [suLin, suLin, suLin, Subgroup.coe_mul, map_mul]

theorem suLin_one : suLin (1 : SU6) = 1 := by
  rw [suLin, OneMemClass.coe_one, map_one]

@[expose] def flagSmul (h : SU6) (F : IsoFlag6) : IsoFlag6 where
  sub k := (F.sub k).map (suLin h : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
  finrank_sub k := by rw [LinearEquiv.finrank_map_eq, F.finrank_sub]
  mono _ _ hab := Submodule.map_mono (F.mono hab)
  isotropic := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe, suLin_apply, suLin_apply, herm6_mulVec_of_mem_SU6 h.2]
    exact F.isotropic v hv w hw

instance : MulAction SU6 IsoFlag6 where
  smul := flagSmul
  one_smul F := IsoFlag6.ext (funext fun k => by
    change (F.sub k).map (suLin 1 : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) = F.sub k
    rw [suLin_one, LinearEquiv.one_eq_refl, LinearEquiv.refl_toLinearMap, Submodule.map_id])
  mul_smul h h' F := IsoFlag6.ext (funext fun k => by
    change (F.sub k).map (suLin (h * h') : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      ((F.sub k).map (suLin h' : (Fin 6 → K) →ₗ[K] (Fin 6 → K))).map
        (suLin h : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    rw [suLin_mul, LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans, Submodule.map_comp])

theorem smul_sub (h : SU6) (F : IsoFlag6) (k : Fin 3) :
    (h • F).sub k = (F.sub k).map (suLin h : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) :=
  rfl

@[expose] def flagChain (F : IsoFlag6) (i : ℕ) : Submodule K (Fin 6 → K) :=
  if h : 0 < i ∧ i ≤ 3 then F.sub ⟨i - 1, by omega⟩ else ⊥

theorem flagChain_succ (F : IsoFlag6) (k : Fin 3) : flagChain F (k + 1) = F.sub k := by
  rw [flagChain, dite_eq_left (by omega)]
  rfl

theorem flagChain_zero (F : IsoFlag6) : flagChain F 0 = ⊥ := by
  rw [flagChain, dite_eq_right (by omega)]

theorem flagChain_le (F : IsoFlag6) (i : ℕ) : flagChain F i ≤ F.sub 2 := by
  rw [flagChain]
  split_ifs with h
  · exact F.mono (Fin.le_iff_val_le_val.mpr (show i - 1 ≤ 2 by omega))
  · exact bot_le

theorem isIsotropicChain_flagChain (F : IsoFlag6) : IsIsotropicChain form6 3 (flagChain F) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i _ x hx y hy => ?_⟩
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [flagChain_zero, finrank_bot]
    · obtain ⟨k, rfl⟩ : ∃ k : Fin 3, i = k + 1 := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
      rw [flagChain_succ, F.finrank_sub]
  · rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [flagChain_zero]
      exact bot_le
    · obtain ⟨k, rfl⟩ : ∃ k : Fin 3, i = k + 1 := ⟨⟨i - 1, by omega⟩, by simp; omega⟩
      have hk : (k : ℕ) + 1 < 3 := by omega
      rw [flagChain_succ, show (k : ℕ) + 1 + 1 = ((⟨k + 1, hk⟩ : Fin 3) : ℕ) + 1 from rfl,
        flagChain_succ]
      exact F.mono (Fin.le_iff_val_le_val.mpr (show (k : ℕ) ≤ k + 1 by omega))
  · rw [← herm6_eq_form6]
    exact F.isotropic y (flagChain_le F i hy) x (flagChain_le F i hx)

theorem exists_smul_eq (F F' : IsoFlag6) : ∃ h : SU6, h • F = F' := by
  obtain ⟨g, hg, hgW⟩ := (isotropic_flag_extension unitaryFieldData_K form6_isSymm
    form6_separatingLeft (Module.finrank_fin_fun K)).2.1 3 (flagChain F) (flagChain F')
    (isIsotropicChain_flagChain F) (isIsotropicChain_flagChain F')
  set M := Matrix.GeneralLinearGroup.toLin.symm g with hM
  have hgM : g = Matrix.GeneralLinearGroup.toLin M := by rw [hM, MulEquiv.apply_symm_apply]
  rw [hgM, toLin_mem_sesqSpecialUnitaryGroup_iff, mem_gramSU, coe_unitaryFieldData_K_bar] at hg
  let hSL : SpecialLinearGroup (Fin 6) K := ⟨M, hg.2⟩
  have hSU : hSL ∈ SU6 := (mem_SU6_iff hSL).mpr hg.1
  refine ⟨⟨hSL, hSU⟩, IsoFlag6.ext (funext fun k => ?_)⟩
  rw [smul_sub, ← flagChain_succ, ← flagChain_succ, ← hgW _ (by omega), hgM]
  rfl

theorem map_scalar_eq {W : Submodule K (Fin 6 → K)} {z : SpecialLinearGroup (Fin 6) K} {c : K}
    (hc : c ≠ 0) (hz : (z : Matrix (Fin 6) (Fin 6) K) = scalar (Fin 6) c) :
    W.map (SpecialLinearGroup.toLin' z : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) = W := by
  have hzv : ∀ v : Fin 6 → K, (SpecialLinearGroup.toLin' z : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) v =
      c • v := fun v => by
    rw [LinearEquiv.coe_coe, SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, hz]
    funext i
    rw [scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [hzv]
    exact W.smul_mem c hw
  · intro hv
    exact ⟨c⁻¹ • v, W.smul_mem _ hv, by rw [hzv, smul_smul, mul_inv_cancel₀ hc, one_smul]⟩

theorem smul_eq_of_mem_scalars {z : SU6}
    (hz : (z : SpecialLinearGroup (Fin 6) K) ∈ LinearFlag.scalars 6 K) (F : IsoFlag6) :
    z • F = F := by
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp hz
  exact IsoFlag6.ext (funext fun k => map_scalar_eq c.ne_zero hc)

theorem herm6_eq_zero_of_mem_preSpan {v w : Fin 6 → K} (hv : v ∈ preSpan 3)
    (hw : w ∈ preSpan 3) : herm6 v w = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : (i : ℕ) < 3
  · rw [hw (Fin.rev i) (by rw [Fin.val_rev]; omega), bar_zero, mul_zero]
  · rw [hv i (by omega), zero_mul]

@[expose] def baseFlag : IsoFlag6 where
  sub k := preSpan (k + 1)
  finrank_sub k := finrank_preSpan (by omega)
  mono a b hab := fun v hv j hj => hv j (by have : (a : ℕ) ≤ b := hab; omega)
  isotropic v hv w hw := herm6_eq_zero_of_mem_preSpan hv hw

theorem baseFlag_sub (k : Fin 3) : baseFlag.sub k = preSpan (k + 1) :=
  rfl

theorem smul_baseFlag_eq_iff_pattern (h : SU6) :
    h • baseFlag = baseFlag ↔ ∀ i j : Fin 6, (j : ℕ) < 3 → (j : ℕ) < i →
      ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0 := by
  constructor
  · intro e i j hj hji
    have ek := congrArg (fun F : IsoFlag6 => F.sub ⟨j, hj⟩) e
    simp only [smul_sub, baseFlag_sub] at ek
    exact (map_preSpan_eq_iff (h : SpecialLinearGroup (Fin 6) K) _).mp ek i j
      (by simp) (by simp; omega)
  · intro H
    refine IsoFlag6.ext (funext fun k => ?_)
    rw [smul_sub, baseFlag_sub]
    exact (map_preSpan_eq_iff (h : SpecialLinearGroup (Fin 6) K) _).mpr
      fun i j hj hi => H i j (by omega) (by omega)

theorem smul_baseFlag_eq_iff (h : SU6) :
    h • baseFlag = baseFlag ↔ ∀ i j : Fin 6, j < i →
      ((h : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) i j = 0 := by
  refine ⟨fun e i j hji => ?_, fun H => (smul_baseFlag_eq_iff_pattern h).mpr
    fun i j _ hji => H i j hji⟩
  have e' : h⁻¹ • baseFlag = baseFlag := by
    rw [inv_smul_eq_iff, e]
  by_cases hj : (j : ℕ) < 3
  · exact (smul_baseFlag_eq_iff_pattern h).mp e i j hj hji
  · have h0 := (smul_baseFlag_eq_iff_pattern h⁻¹).mp e' (Fin.rev j) (Fin.rev i)
      (by rw [Fin.val_rev]; omega) (by rw [Fin.val_rev, Fin.val_rev]; omega)
    obtain ⟨g, hg⟩ := h
    have hinv := inv_apply_of_mem_SU6 (inv_mem hg) i j
    rw [inv_inv] at hinv
    change (g : Matrix (Fin 6) (Fin 6) K) i j = 0
    rw [hinv]
    have h0' : ((g⁻¹ : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)
        (Fin.rev j) (Fin.rev i) = 0 := h0
    rw [h0', bar_zero]

theorem det_J6 : J6.det = 1 := by
  have h := congrArg det J6_mul_J6
  rw [det_mul, det_one] at h
  have hsq : ∀ x : K, x * x = 1 → x = 1 := by decide
  exact hsq _ h

theorem J6_map_bar : J6.map bar = J6 := by
  ext i j
  rw [map_apply, J6_apply]
  split_ifs
  exacts [bar_one, bar_zero]

theorem J6_mem_SU6 : (⟨J6, det_J6⟩ : SpecialLinearGroup (Fin 6) K) ∈ SU6 := by
  refine (mem_SU6_iff _).mpr ?_
  change (J6.map bar)ᵀ * J6 * J6 = J6
  rw [J6_map_bar, J6_transpose, Matrix.mul_assoc, J6_mul_J6, Matrix.mul_one]

@[expose] def revSU : SU6 :=
  ⟨⟨J6, det_J6⟩, J6_mem_SU6⟩

abbrev oppFlag : IsoFlag6 := revSU • baseFlag

theorem suLin_revSU_uVec (i : Fin 6) : suLin revSU (uVec i) = uVec (Fin.rev i) := by
  funext j
  rw [suLin_apply, mulVec_uVec]
  change J6 j i = uVec (Fin.rev i) j
  rw [J6_apply, uVec, Pi.single_apply]
  exact if_congr ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [h, Fin.rev_rev]⟩ rfl rfl

theorem oppFlag_sub (k : Fin 3) :
    oppFlag.sub k = Submodule.span K (uVec '' {j | 5 - (k : ℕ) ≤ (j : ℕ)}) := by
  rw [smul_sub, baseFlag_sub, preSpan_eq_span, Submodule.map_span, Set.image_image]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, LinearEquiv.coe_coe, suLin_revSU_uVec]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.rev j, by rw [Fin.val_rev]; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.rev j, by rw [Fin.val_rev]; omega, by rw [Fin.rev_rev]⟩

@[expose] def frob6 : (Fin 6 → K) →ₛₗ[barHom] (Fin 6 → K) where
  toFun v i := bar (v i)
  map_add' _ _ := funext fun _ => bar_add _ _
  map_smul' _ _ := funext fun _ => bar_mul _ _

theorem frob6_apply (v : Fin 6 → K) (i : Fin 6) : frob6 v i = bar (v i) :=
  rfl

theorem bar_sum {ι : Type*} (s : Finset ι) (f : ι → K) : bar (∑ i ∈ s, f i) = ∑ i ∈ s, bar (f i) :=
  map_sum barHom f s

theorem barHom_bijective : Function.Bijective barHom :=
  Function.Involutive.bijective (f := barHom) bar_bar

theorem frob6_frob6 (v : Fin 6 → K) : frob6 (frob6 v) = v :=
  funext fun i => bar_bar (v i)

theorem herm6_frob6 (v w : Fin 6 → K) : herm6 (frob6 v) (frob6 w) = bar (herm6 v w) := by
  simp only [herm6, frob6_apply, bar_sum, bar_mul]

theorem finrank_map_frob6 (W : Submodule K (Fin 6 → K)) :
    finrank K (W.map frob6) = finrank K W := by
  let j : W ≃+ W.map frob6 :=
    { toFun := fun w => ⟨frob6 (w : Fin 6 → K), Submodule.mem_map_of_mem w.2⟩
      invFun := fun w => ⟨frob6 (w : Fin 6 → K), by
        obtain ⟨v, hv, hvw⟩ := Submodule.mem_map.mp w.2
        rw [← hvw, frob6_frob6]
        exact hv⟩
      left_inv := fun w => Subtype.ext (frob6_frob6 (w : Fin 6 → K))
      right_inv := fun w => Subtype.ext (frob6_frob6 (w : Fin 6 → K))
      map_add' := fun v w => Subtype.ext (map_add frob6 (v : Fin 6 → K) w) }
  have hrank := rank_eq_of_equiv_equiv (R := K) (R' := K) barHom j barHom_bijective
    fun c w => Subtype.ext (map_smulₛₗ frob6 c (w : Fin 6 → K))
  exact congrArg Cardinal.toNat hrank.symm

@[expose] def frobFlag (F : IsoFlag6) : IsoFlag6 where
  sub k := (F.sub k).map frob6
  finrank_sub k := by rw [finrank_map_frob6, F.finrank_sub]
  mono _ _ hab := Submodule.map_mono (F.mono hab)
  isotropic := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [herm6_frob6, F.isotropic v hv w hw, bar_zero]

theorem frobFlag_sub (F : IsoFlag6) (k : Fin 3) : (frobFlag F).sub k = (F.sub k).map frob6 :=
  rfl

theorem frobFlag_baseFlag : frobFlag baseFlag = baseFlag := by
  refine IsoFlag6.ext (funext fun k => le_antisymm ?_ fun v hv => ?_)
  · rintro _ ⟨v, hv, rfl⟩ j hj
    rw [frob6_apply, hv j hj, bar_zero]
  · refine ⟨frob6 v, fun j hj => ?_, frob6_frob6 v⟩
    rw [frob6_apply, hv j hj, bar_zero]

theorem map_bar_conjTranspose {M : Matrix (Fin 6) (Fin 6) K} (hM : (M.map bar)ᵀ * J6 * M = J6) :
    ((M.map bar).map bar)ᵀ * J6 * M.map bar = J6 := by
  have e := congrArg (fun X : Matrix (Fin 6) (Fin 6) K => X.map barHom) hM
  simp only [Matrix.map_mul, transpose_map] at e
  have hb : (⇑barHom : K → K) = bar := rfl
  rw [hb, J6_map_bar] at e
  exact e

theorem barSL_mem_SU6 {g : SpecialLinearGroup (Fin 6) K} (hg : g ∈ SU6) : barSL g ∈ SU6 := by
  refine (mem_SU6_iff _).mpr ?_
  have e := map_bar_conjTranspose ((mem_SU6_iff g).mp hg)
  rwa [← coe_barSL] at e

@[expose] def barSU (h : SU6) : SU6 :=
  ⟨barSL h.1, barSL_mem_SU6 h.2⟩

theorem frob6_mulVec (g : SpecialLinearGroup (Fin 6) K) (v : Fin 6 → K) :
    frob6 ((g : Matrix (Fin 6) (Fin 6) K) *ᵥ v) =
      (barSL g : Matrix (Fin 6) (Fin 6) K) *ᵥ frob6 v := by
  funext i
  simp only [frob6_apply, mulVec, dotProduct, bar_sum, bar_mul, coe_barSL, map_apply]

theorem frob6_suLin (h : SU6) (v : Fin 6 → K) :
    frob6 (suLin h v) = suLin (barSU h) (frob6 v) :=
  frob6_mulVec h.1 v

theorem frobFlag_smul (h : SU6) (F : IsoFlag6) : frobFlag (h • F) = barSU h • frobFlag F := by
  refine IsoFlag6.ext (funext fun k => ?_)
  rw [frobFlag_sub, smul_sub, smul_sub, frobFlag_sub, ← Submodule.map_comp,
    ← Submodule.map_comp]
  congr 1
  ext v i
  exact congrFun (frob6_suLin h v) i

end CFSG.LieType.Chevalley.C2E6Std
