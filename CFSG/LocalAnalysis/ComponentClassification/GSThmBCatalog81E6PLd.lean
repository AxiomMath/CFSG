module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PLt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
import CFSG.LieType.SteinbergBROddLinearThreeParabolic

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4 InvClassL TBlocks HBlocks
open scoped commutatorElement

variable {F : Type} [Field F]

theorem negOne4_sq : (negOne4 : SpecialLinearGroup (Fin 4) F) ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (-1 : Matrix (Fin 4) (Fin 4) F) * (-1) = 1
  rw [neg_mul_neg, Matrix.one_mul]

theorem orderOf_negOne4 (h2 : (2 : F) ≠ 0) :
    orderOf (negOne4 : SpecialLinearGroup (Fin 4) F) = 2 := by
  refine orderOf_eq_prime negOne4_sq fun h => h2 ?_
  have h00 : (-1 : Matrix (Fin 4) (Fin 4) F) 0 0 = (1 : Matrix (Fin 4) (Fin 4) F) 0 0 :=
    congrArg (fun g : SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h
  rw [Matrix.neg_apply, Matrix.one_apply_eq] at h00
  linear_combination -h00

theorem two_mul_card_map_proj_dvd (h2 : (2 : F) ≠ 0)
    {R : Subgroup (SpecialLinearGroup (Fin 4) F)} (hR : negOne4 ∈ R) :
    2 * Nat.card (R.map (proj 4 F)) ∣ Nat.card R := by
  set f := (proj 4 F).comp R.subtype with hf
  have hrange : f.range = R.map (proj 4 F) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hx : (⟨negOne4, hR⟩ : R) ∈ f.ker := by
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact proj_negOne4
  have ho : orderOf (⟨⟨negOne4, hR⟩, hx⟩ : f.ker) = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact orderOf_negOne4 h2
  have h2k : 2 ∣ Nat.card f.ker := ho ▸ orderOf_dvd_natCard _
  rw [← Subgroup.card_ker_mul_card_range f, hrange]
  exact Nat.mul_dvd_mul h2k dvd_rfl

theorem exists_fixed_of_frame {A P D : GL (Fin 4) F} {μ : Fˣ}
    (hAP : A * P = GeneralLinearGroup.scalar (Fin 4) μ * (P * D))
    {M : Subgroup (projectiveSL 4 F)} (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, conjAut 4 F A x = x) :
    ∃ M' : Subgroup (projectiveSL 4 F), ⁅M', M'⁆ = M' ∧ Nat.card M' = Nat.card M ∧
      ∀ x ∈ M', conjAut 4 F D x = x := by
  have hc : GeneralLinearGroup.scalar (Fin 4) μ ∈ center (GL (Fin 4) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨μ, rfl⟩
  have hPA : P⁻¹ * A = GeneralLinearGroup.scalar (Fin 4) μ * (D * P⁻¹) := by
    calc P⁻¹ * A = P⁻¹ * (A * P) * P⁻¹ := by group
      _ = (P⁻¹ * GeneralLinearGroup.scalar (Fin 4) μ) * P * D * P⁻¹ := by rw [hAP]; group
      _ = (GeneralLinearGroup.scalar (Fin 4) μ * P⁻¹) * P * D * P⁻¹ := by
          rw [mem_center_iff.mp hc P⁻¹]
      _ = GeneralLinearGroup.scalar (Fin 4) μ * (D * P⁻¹) := by group
  have h1 : conjAut 4 F D * conjAut 4 F P⁻¹ = conjAut 4 F P⁻¹ * conjAut 4 F A := by
    rw [← map_mul, ← map_mul, hPA, map_mul (conjAut 4 F) (GeneralLinearGroup.scalar (Fin 4) μ),
      conjAut_scalar, one_mul]
  refine ⟨M.map (conjAut 4 F P⁻¹).toMonoidHom, ?_, Subgroup.card_map_of_injective
    (conjAut 4 F P⁻¹).injective, ?_⟩
  · rw [← Subgroup.map_commutator, hM]
  · rintro _ ⟨y, hy, rfl⟩
    have h2 := congrArg (fun ψ : MulAut (projectiveSL 4 F) => ψ y) h1
    simp only [MulAut.mul_apply] at h2
    rw [MulEquiv.coe_toMonoidHom, h2, hfix y hy]

theorem comm_of_mem_fixOf {D : GL (Fin 4) F} {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D)) :
    (g : Matrix (Fin 4) (Fin 4) F) * D = D * g := by
  have h := congrArg (fun x : SpecialLinearGroup (Fin 4) F => (x : Matrix (Fin 4) (Fin 4) F))
    (CatFactsSp4.mem_fixOf.mp hg)
  simp only [coe_slConjugation] at h
  calc (g : Matrix (Fin 4) (Fin 4) F) * D =
        (D : Matrix (Fin 4) (Fin 4) F) * g * ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          D := by rw [h]
    _ = (D : Matrix (Fin 4) (Fin 4) F) * g := by
        rw [Matrix.mul_assoc _ ((D⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem isBD_of_mem_fixOf_t2 (h2 : (2 : F) ≠ 0) {D : GL (Fin 4) F}
    (hD : (D : Matrix (Fin 4) (Fin 4) F) = X1 1) {g : SpecialLinearGroup (Fin 4) F}
    (hg : g ∈ CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D)) :
    IsBD (g : Matrix (Fin 4) (Fin 4) F) := by
  have h := comm_of_mem_fixOf hg
  rw [hD] at h
  exact isBD_of_comm_X1 h2 one_ne_zero h

theorem commutator_le_range_bdSL (h2 : (2 : F) ≠ 0) {D : GL (Fin 4) F}
    (hD : (D : Matrix (Fin 4) (Fin 4) F) = X1 1) :
    ⁅CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D),
      CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D)⁆ ≤
      (bdSL (F := F)).range := by
  set C := CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D) with hC
  have hBD : ∀ x ∈ C, IsBD (x : Matrix (Fin 4) (Fin 4) F) := fun x hx =>
    isBD_of_mem_fixOf_t2 h2 hD hx
  have hul : ∀ x ∈ C, ∀ y ∈ C,
      ul ((x * y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ul (x : Matrix (Fin 4) (Fin 4) F) * ul (y : Matrix (Fin 4) (Fin 4) F) :=
    fun x hx y hy => by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact ul_mul (hBD x hx) (hBD y hy)
  have hinv : ∀ x ∈ C,
      (ul ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det *
        (ul (x : Matrix (Fin 4) (Fin 4) F)).det = 1 := fun x hx => by
    rw [← det_mul, ← hul _ (C.inv_mem hx) _ hx, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      ul_one, det_one]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hg' : g * h * g⁻¹ ∈ C := C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)
  have hc : ⁅g, h⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem hg' (C.inv_mem hh)
  have hc1 : (ul ((⁅g, h⁆ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det =
      1 := by
    rw [commutatorElement_def, hul _ hg' _ (C.inv_mem hh), hul _ (C.mul_mem hg hh) _ (C.inv_mem hg),
      hul _ hg _ hh, det_mul, det_mul, det_mul]
    calc (ul (g : Matrix (Fin 4) (Fin 4) F)).det * (ul (h : Matrix (Fin 4) (Fin 4) F)).det *
          (ul ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det *
          (ul ((h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det =
        ((ul ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det *
          (ul (g : Matrix (Fin 4) (Fin 4) F)).det) *
        ((ul ((h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det *
          (ul (h : Matrix (Fin 4) (Fin 4) F)).det) := by ring
      _ = 1 := by rw [hinv g hg, hinv h hh, one_mul]
  have hc2 : (lr ((⁅g, h⁆ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).det =
      1 := by
    have h3 := det_of_isBD (hBD _ hc)
    rw [Matrix.SpecialLinearGroup.det_coe, hc1, one_mul] at h3
    exact h3.symm
  rw [MonoidHom.mem_range]
  refine ⟨(⟨ul _, hc1⟩, ⟨lr _, hc2⟩), Subtype.ext ?_⟩
  rw [coe_bdSL]
  exact (eq_bd (hBD _ hc)).symm

theorem bdSL_injective : Function.Injective (bdSL (F := F)) := by
  intro x y hxy
  have h := congrArg (fun z : SpecialLinearGroup (Fin 4) F => (z : Matrix (Fin 4) (Fin 4) F)) hxy
  simp only [coe_bdSL] at h
  have h1 := congrArg ul h
  have h2 := congrArg lr h
  rw [ul_bd, ul_bd] at h1
  rw [lr_bd, lr_bd] at h2
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem card_SL_two [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.LieType.SteinbergBR.BlockPar.card_SL_two'

theorem card_range_bdSL [Finite F] :
    Nat.card (bdSL (F := F)).range = (Nat.card F * (Nat.card F ^ 2 - 1)) ^ 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (bdSL_injective (F := F))).toEquiv, Nat.card_prod,
    card_SL_two, ← sq]

theorem two_mul_card_dvd_of_t2 [Finite F] (h2 : (2 : F) ≠ 0) {D : GL (Fin 4) F}
    (hD : (D : Matrix (Fin 4) (Fin 4) F) = X1 1) {M : Subgroup (projectiveSL 4 F)}
    (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, conjAut 4 F D x = x) :
    2 * Nat.card M ∣ (Nat.card F * (Nat.card F ^ 2 - 1)) ^ 2 := by
  have h1 : M ≤ (bdSL (F := F)).range.map (proj 4 F) :=
    (perfect_le_map_commutator hM (perfect_le_map_fixOf_proj _ (conjAut_proj D) hM hfix)).trans
      (Subgroup.map_mono (commutator_le_range_bdSL h2 hD))
  have h3 := two_mul_card_map_proj_dvd h2 (R := (bdSL (F := F)).range) ⟨_, bdSL_negOne⟩
  rw [← card_range_bdSL]
  exact (Nat.mul_dvd_mul_left 2 (Subgroup.card_dvd_of_le h1)).trans h3

theorem eq_zero_of_comm_dOne (h2 : (2 : F) ≠ 0) {g : Matrix (Fin 4) (Fin 4) F}
    (hg : g * dOne = dOne * g) {i : Fin 4} (hi : i ≠ 3) : g i 3 = 0 ∧ g 3 i = 0 := by
  have hi3 : (i : ℕ) < 3 := by
    have h1 := i.isLt
    have h3 : (i : ℕ) ≠ 3 := fun h => hi (Fin.ext h)
    omega
  have h33 : ¬ ((3 : Fin 4) : ℕ) < 3 := by decide
  have e1 := congrFun (congrFun hg i) 3
  have e2 := congrFun (congrFun hg 3) i
  simp only [dOne, mul_diagonal, diagonal_mul, hi3, h33, ↓reduceIte] at e1 e2
  constructor
  · have h4 : (2 : F) * g i 3 = 0 := by linear_combination -e1
    exact (mul_eq_zero.mp h4).resolve_left h2
  · have h4 : (2 : F) * g 3 i = 0 := by linear_combination e2
    exact (mul_eq_zero.mp h4).resolve_left h2

theorem mul_apply_three {g h : Matrix (Fin 4) (Fin 4) F} (hg : ∀ i : Fin 4, i ≠ 3 → g 3 i = 0) :
    (g * h) 3 3 = g 3 3 * h 3 3 := by
  rw [Matrix.mul_apply, Fin.sum_univ_four, hg 0 (by decide), hg 1 (by decide), hg 2 (by decide)]
  ring

variable (F) in
@[expose] noncomputable def blockSL4 :
    SpecialLinearGroup (Fin 3) F →* SpecialLinearGroup (Fin 4) F :=
  blockSL F 3 1

theorem eq_diagBlock_of {x : Matrix (Fin 4) (Fin 4) F}
    (hx : ∀ i : Fin 4, i ≠ 3 → x i 3 = 0 ∧ x 3 i = 0) (h33 : x 3 3 = 1) :
    x = diagBlock (Matrix.of fun i j : Fin 3 => x (Fin.castSucc i) (Fin.castSucc j))
      (1 : Matrix (Fin 1) (Fin 1) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | exact (hx _ (by decide)).1
    | exact (hx _ (by decide)).2
    | exact h33

theorem mem_range_blockSL4 {x : SpecialLinearGroup (Fin 4) F}
    (hx : ∀ i : Fin 4, i ≠ 3 →
      (x : Matrix (Fin 4) (Fin 4) F) i 3 = 0 ∧ (x : Matrix (Fin 4) (Fin 4) F) 3 i = 0)
    (h33 : (x : Matrix (Fin 4) (Fin 4) F) 3 3 = 1) : x ∈ (blockSL4 F).range := by
  have he := eq_diagBlock_of hx h33
  set Y := Matrix.of fun i j : Fin 3 =>
    (x : Matrix (Fin 4) (Fin 4) F) (Fin.castSucc i) (Fin.castSucc j) with hYdef
  have hY : Y.det = 1 := by
    have h1 : (x : Matrix (Fin 4) (Fin 4) F).det =
        (diagBlock Y (1 : Matrix (Fin 1) (Fin 1) F)).det := by rw [← he]
    rw [Matrix.SpecialLinearGroup.det_coe, diagBlock, det_reindex_self, det_fromBlocks_zero₁₂,
      det_one, mul_one] at h1
    exact h1.symm
  refine ⟨(⟨Y, hY⟩ : SpecialLinearGroup (Fin 3) F), Subtype.ext ?_⟩
  exact he.symm

theorem commutator_le_range_blockSL4 (h2 : (2 : F) ≠ 0) {D : GL (Fin 4) F}
    (hD : (D : Matrix (Fin 4) (Fin 4) F) = dOne) :
    ⁅CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D),
      CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D)⁆ ≤
      (blockSL4 F).range := by
  set C := CatFactsSp4.fixOf (CatalogueBHigherLinearAction.slConjugation 4 F D) with hC
  have hz : ∀ x ∈ C, ∀ i : Fin 4, i ≠ 3 → (x : Matrix (Fin 4) (Fin 4) F) i 3 = 0 ∧
      (x : Matrix (Fin 4) (Fin 4) F) 3 i = 0 := fun x hx i hi => by
    have h := comm_of_mem_fixOf hx
    rw [hD] at h
    exact eq_zero_of_comm_dOne h2 h hi
  have h33 : ∀ x ∈ C, ∀ y : SpecialLinearGroup (Fin 4) F,
      ((x * y : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 =
        (x : Matrix (Fin 4) (Fin 4) F) 3 3 * (y : Matrix (Fin 4) (Fin 4) F) 3 3 :=
    fun x hx y => by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      exact mul_apply_three fun i hi => (hz x hx i hi).2
  have hinv : ∀ x ∈ C, ((x⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 *
      (x : Matrix (Fin 4) (Fin 4) F) 3 3 = 1 := fun x hx => by
    rw [← h33 _ (C.inv_mem hx), inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_apply_eq]
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hg' : g * h * g⁻¹ ∈ C := C.mul_mem (C.mul_mem hg hh) (C.inv_mem hg)
  have hc : ⁅g, h⁆ ∈ C := by
    rw [commutatorElement_def]
    exact C.mul_mem hg' (C.inv_mem hh)
  refine mem_range_blockSL4 (hz _ hc) ?_
  rw [commutatorElement_def, h33 _ hg', h33 _ (C.mul_mem hg hh), h33 _ hg]
  calc (g : Matrix (Fin 4) (Fin 4) F) 3 3 * (h : Matrix (Fin 4) (Fin 4) F) 3 3 *
        ((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 *
        ((h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 =
      (((g⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 *
        (g : Matrix (Fin 4) (Fin 4) F) 3 3) *
      (((h⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) 3 3 *
        (h : Matrix (Fin 4) (Fin 4) F) 3 3) := by ring
    _ = 1 := by rw [hinv g hg, hinv h hh, one_mul]

theorem blockSL4_injective : Function.Injective (blockSL4 F) := by
  intro Y Y' h
  ext i j
  have h1 := congrArg (fun z : SpecialLinearGroup (Fin 4) F =>
    (z : Matrix (Fin 4) (Fin 4) F) (finSumFinEquiv (m := 3) (n := 1) (Sum.inl i))
      (finSumFinEquiv (m := 3) (n := 1) (Sum.inl j))) h
  have e1 := blockGL_apply_inl (K := F) (m := 1) (SpecialLinearGroup.toGL Y) i j
  have e2 := blockGL_apply_inl (K := F) (m := 1) (SpecialLinearGroup.toGL Y') i j
  exact e1.symm.trans (h1.trans e2)

theorem card_range_blockSL4 [Finite F] :
    Nat.card (blockSL4 F).range =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (blockSL4_injective (F := F))).toEquiv,
    card_SL_eq (by norm_num), show 3 * (3 - 1) / 2 = 3 by rfl,
    show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]

theorem card_dvd_of_t1 [Finite F] (h2 : (2 : F) ≠ 0) {D : GL (Fin 4) F}
    (hD : (D : Matrix (Fin 4) (Fin 4) F) = dOne) {M : Subgroup (projectiveSL 4 F)}
    (hM : ⁅M, M⁆ = M) (hfix : ∀ x ∈ M, conjAut 4 F D x = x) :
    Nat.card M ∣ Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  have h1 : M ≤ (blockSL4 F).range.map (proj 4 F) :=
    (perfect_le_map_commutator hM (perfect_le_map_fixOf_proj _ (conjAut_proj D) hM hfix)).trans
      (Subgroup.map_mono (commutator_le_range_blockSL4 h2 hD))
  rw [← card_range_blockSL4]
  exact (Subgroup.card_dvd_of_le h1).trans (Subgroup.card_map_dvd _ _)

end CFSG.ComponentClassification.GSThmB.P211
