module

public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowOData
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorRowS
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitCase

public noncomputable section

namespace CFSG.ComponentClassification.OddSelector

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

theorem mem_center_sl_two_iff {F : Type} [Field F] (g : SpecialLinearGroup (Fin 2) F) :
    g ∈ center (SpecialLinearGroup (Fin 2) F) ↔ g = 1 ∨ g = -1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨r, hr, hg⟩
    rcases sq_eq_one_iff.mp hr with rfl | rfl
    · left
      ext i j
      have := congrFun (congrFun hg i) j
      fin_cases i <;> fin_cases j <;> simpa using this.symm
    · right
      ext i j
      have := congrFun (congrFun hg i) j
      fin_cases i <;> fin_cases j <;> simpa using this.symm
  · rintro (rfl | rfl)
    · exact ⟨1, one_pow 2, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩
    · exact ⟨-1, by rw [neg_one_sq], by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

section Row

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem isometryGroup_smul_eq {m : ℕ} (R : GL (Fin m) k) (c : kˣ) :
    CatalogueBGraphForm.isometryGroup m k (R * GeneralLinearGroup.scalar (Fin m) c) =
      CatalogueBGraphForm.isometryGroup m k R := by
  ext g
  rw [CatalogueBGraphForm.mem_isometryGroup, CatalogueBGraphForm.mem_isometryGroup,
    Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_eq_smul_one, Matrix.mul_smul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_right_injective _ c.ne_zero |>.eq_iff

variable {A : Type} [Group A] {W : Subgroup A} {a : A} {L : Subgroup A}

theorem selectorRowO_of_nonsplit (hodd : Odd (Nat.card k))
    {ρ : A →* MulAut (projectiveSL 4 k)} (hinj : Function.Injective ρ)
    (hCA : (centralizer {a}).map ρ = ρ.range ⊓ centralizer {ρ a})
    (hCW : (W ⊓ centralizer {a}).map ρ =
      OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a})
    (hL₁ : CFSG.Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hns : ¬ ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0) :
    SelectorRowO 4 k ρ W a L ∧
      ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card k ^ 2 ∧
        Nonempty (L ≃* projectiveSL 2 E) := by
  classical
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hk2 : ringChar k ≠ 2 := CatalogueBOddQuadratic.char_ne_two_of_odd_card hodd
  set R₀ : GL (Fin 4) k := B⁻¹ with hR₀def
  have hR₀ : (R₀ : Matrix (Fin 4) (Fin 4) k)ᵀ = R₀ := transpose_inv_eq_of_transpose_eq hB
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R₀ with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R₀ hR₀
  have hdim : Module.finrank k (Fin 4 → k) = 4 := Module.finrank_fin_fun k
  obtain ⟨-, -, -, -, hnon, -, -⟩ := orthogonal_low_dimensional_fixed_derived_component_coverage
    Q hQ (Or.inl ⟨hodd, Or.inr (Or.inl hdim)⟩)
  obtain ⟨δ, hδ, d, ψ, e, hψ, he, hc, hq⟩ := hnon hodd hdim hns
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  have : Finite (extension (δ : k)) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (δ : k) 0).symm
  set R : GL (Fin 4) k := R₀ * GeneralLinearGroup.scalar (Fin 4) d⁻¹ with hRdef
  have hRm : (R : Matrix (Fin 4) (Fin 4) k) =
      ((d⁻¹ : kˣ) : k) • (R₀ : Matrix (Fin 4) (Fin 4) k) := by
    rw [hRdef, Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_eq_smul_one, Matrix.mul_smul,
      Matrix.mul_one]
  have hR : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R := by rw [hRm, transpose_smul, hR₀]
  have hRinv : conjAut 4 k R⁻¹ = conjAut 4 k B := by
    rw [hRdef, _root_.mul_inv_rev, map_mul, ← map_inv (GeneralLinearGroup.scalar (Fin 4)),
      conjAut_scalar, one_mul, hR₀def, inv_inv]
  have hρa' : ρ a = conjAut 4 k R⁻¹ * dualAut 4 k := by rw [hRinv, hρa]
  have hgram : ∀ v : Fin 4 → k, v ⬝ᵥ ((R : Matrix (Fin 4) (Fin 4) k) *ᵥ v) =
      hermitianForm (δ : k) (ψ v) := by
    intro v
    have h3 : Q v = v ⬝ᵥ ((R₀ : Matrix (Fin 4) (Fin 4) k) *ᵥ v) := by
      change (CatalogueBLinearHigherB.matrixForm R₀).toQuadraticMap v = _
      rw [LinearMap.BilinMap.toQuadraticMap_apply, CatalogueBLinearHigherB.matrixForm_apply]
    rw [hRm, smul_mulVec, dotProduct_smul, ← h3, hψ v, smul_eq_mul, ← mul_assoc,
      Units.inv_mul, one_mul]
  set O := CatalogueBGraphForm.isometryGroup 4 k R₀ with hOdef
  set eO := matrixOrthogonalEquiv hk2 R₀ hR₀ with heO
  set f : TauCeti.QuadraticMap.orthogonalGroup Q →* GL (Fin 4) k :=
    O.subtype.comp eO.toMonoidHom with hf
  have hfi : Function.Injective f := O.subtype_injective.comp eO.injective
  have hfe : ∀ d' : HermitianIsometries (δ : k), f (e.symm d') = linearConjGL ψ d'.val := by
    intro d'
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec]
    change ((eO (e.symm d') : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
    rw [matrixOrthogonalEquiv_mulVec]
    have h1 := he (e.symm d') (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = ⁅O, O⁆ := by
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_subtype_commutator]
    congr 1
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hD : ⁅O, O⁆ = (rowOHom δ ψ).range := by
    rw [← hcommO, hc, Subgroup.map_map, specialImage, MonoidHom.range_eq_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext g : 1
    exact hfe _
  set D : Subgroup (GL (Fin 4) k) := ⁅O, O⁆ with hDdef
  have hqD : CFSG.IsQuasisimple D :=
    (isQuasisimple_congr (((commutator _).equivMapOfInjective f hfi).trans
      (MulEquiv.subgroupCongr hcommO))).1 hq
  have hlift : ∀ X, CFSG.Assembly.IsComponentOf X
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}) → X = rowOJ δ ψ := by
    intro X hX
    rw [hρa] at hX
    obtain ⟨hXh, hmap, -⟩ := graph_component_lift (by norm_num) B hX
    set Xh := ⁅X.comap (conjAut 4 k), X.comap (conjAut 4 k)⁆ with hXhdef
    have hXhD : Xh ≤ D := by
      have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
      rw [← Subgroup.commutator_eq_self (H := Xh)]
      exact Subgroup.commutator_mono hXh.1 hXh.1
    have hDO : D ≤ O := by
      rw [hDdef, ← Subgroup.map_subtype_commutator]
      exact Subgroup.map_subtype_le _
    have hXD : Xh = D := by
      have hc' := isComponentOf_of_le hXh hXhD hDO
      have hcomp := (isComponentOf_iff_isComponent_subgroupOf hXhD).mp hc'
      have htop := eq_top_of_isComponent_quasisimple hqD hcomp
      exact le_antisymm hXhD fun x hx => by
        have : (⟨x, hx⟩ : D) ∈ Xh.subgroupOf D := htop ▸ mem_top _
        exact this
    rw [← hmap, hXD, hD, rowOJ]
    exact (MonoidHom.range_comp _ _).symm
  have hLJ : L.map ρ = rowOJ δ ψ := hlift _ hL₁
  have hone : ∀ g, rowOHom δ ψ g = 1 ↔ g = 1 ∨ g = -1 := by
    intro g
    rw [← specialRho_eq_one_iff_sign (δ : k) h2]
    constructor
    · intro h
      apply Subtype.ext
      apply linearConjGL_injective ψ
      rw [Subgroup.coe_one, map_one]
      exact h
    · intro h
      change linearConjGL ψ (specialRho (δ : k) h2 g).val = 1
      rw [h]
      exact map_one _
  have hE9 : 9 ≤ Nat.card (extension (δ : k)) := by
    rw [extension_card]
    have := ProjectiveEigenspace.three_le_card_of_two_ne_zero h2
    nlinarith
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) (extension (δ : k))) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 (extension (δ : k)) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  have hker : ∀ g, conjAut 4 k (rowOHom δ ψ g) = 1 ↔ g = 1 ∨ g = -1 := by
    intro g
    constructor
    · intro h1
      obtain ⟨c, hc'⟩ := (conjAut_eq_one_iff (by norm_num) _).mp h1
      have hcen : (rowOHom δ ψ).rangeRestrict g ∈ center (rowOHom δ ψ).range := by
        rw [mem_center_iff]
        intro y
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
        rw [← hc']
        exact (GeneralLinearGroup.scalar_commute c (y : GL (Fin 4) k)).symm
      have hkerc : (rowOHom δ ψ).rangeRestrict.ker ≤
          center (SpecialLinearGroup (Fin 2) (extension (δ : k))) := by
        intro x hx
        rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hone] at hx
        rw [mem_center_sl_two_iff]
        exact hx
      exact (mem_center_sl_two_iff g).mp (mem_center_of_map_mem_center _ hkerc hcen)
    · intro h
      rw [(hone g).mpr h, map_one]
  have hmap1 : ∀ X : GL (Fin 4) k, GeneralLinearGroup.map ((1 : k ≃+* k) : k →+* k) X = X :=
    fun X => Units.ext (by ext i j; rfl)
  have hfix : OuterAutomorphisms.inner (projectiveSL 4 k) ⊓
      centralizer {conjAut 4 k R⁻¹ * dualAut 4 k} = (rowOFixed R).map (conjAut 4 k) := by
    apply le_antisymm
    · intro α hα
      obtain ⟨hαI, hαC⟩ := mem_inf.mp hα
      obtain ⟨Y, rfl⟩ := exists_conjAut_of_mem_inner hαI
      have h1 : conjAut 4 k (SpecialLinearGroup.toGL Y) * fieldAut 4 k 1 ∈
          centralizer {conjAut 4 k R⁻¹ * dualAut 4 k} := by
        rw [map_one, mul_one]
        exact hαC
      obtain ⟨c, hc'⟩ :=
        (mem_centralizer_conjAut_inv_dualAut_iff (by norm_num) R hR _ 1).1.mp h1
      rw [hmap1] at hc'
      refine ⟨SpecialLinearGroup.toGL Y, mem_inf.mpr
        ⟨(CatalogueBGraphForm.mem_similitudeGroup 4 k R _).mpr ⟨c, hc'⟩, ⟨1, ?_⟩⟩, rfl⟩
      apply Units.ext
      rw [powMonoidHom_apply, one_pow, Units.val_one, GeneralLinearGroup.val_det_apply,
        SpecialLinearGroup.coe_GL_coe_matrix, Y.2]
    · rintro _ ⟨X, hX, rfl⟩
      obtain ⟨hXs, ⟨c, hc'⟩⟩ := mem_inf.mp hX
      obtain ⟨mu, hmu⟩ := (CatalogueBGraphForm.mem_similitudeGroup 4 k R X).mp hXs
      refine mem_inf.mpr ⟨conjAut_mem_inner (c := c) hc'.symm, ?_⟩
      have := (mem_centralizer_conjAut_inv_dualAut_iff (by norm_num) R hR X 1).1.mpr
        ⟨mu, by rw [hmap1]; exact hmu⟩
      rwa [map_one, mul_one] at this
  have hid := map_mulAut_one_eq (G := MulAut (projectiveSL 4 k))
  have hc1 : MulAut.conj (conjAut 4 k 1) = 1 := by rw [map_one, map_one]
  refine ⟨⟨δ, hδ, ψ, R, 1, hR, hgram, ?_, ?_, ?_, ?_, ?_, hker, ?_,
    centralizer_conjAut_inv_dualAut_eq (by norm_num) R hR, ?_, ?_⟩, ?_⟩
  · rw [map_one, one_mul, inv_one, mul_one, hρa']
  · rw [hc1, hid, hρa', hfix]
  · intro X
    rw [hc1, hid]
    exact ⟨hlift X, fun h => h ▸ hLJ ▸ hL₁⟩
  · rw [hc1, hid, hLJ]
  · rw [← hD, hRdef, isometryGroup_smul_eq, hDdef, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  · rw [hc1, hid, hρa']
  · rw [hc1, hid, hCA, hρa']
  · rw [hc1, hid, hCW, hρa']
  ·
    set θ := (conjAut 4 k).comp (rowOHom δ ψ) with hθ
    have hθker : θ.ker = scalars 2 (extension (δ : k)) := by
      ext g
      rw [MonoidHom.mem_ker, scalars_eq_center 2 (extension (δ : k)), mem_center_sl_two_iff]
      exact hker g
    exact ⟨extension (δ : k), inferInstance, inferInstance, extension_card (δ : k),
      ⟨(L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hLJ).trans
        ((QuotientGroup.quotientKerEquivRange θ).symm.trans
          (QuotientGroup.quotientMulEquivOfEq hθker)))⟩⟩

end Row

end CFSG.ComponentClassification.OddSelector
