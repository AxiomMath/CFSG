module

public import CFSG.LieType.Chevalley.E7Three.Centralizer
public import CFSG.LieType.AlgebraicGroups.PolynomialCurveImage
public import CFSG.LieType.AlgebraicGroups.ClosedIdentityComponentFunctorial

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KA5L CFSG.LieType.Chevalley.E7Three.Cube

open scoped MatrixGroups Kronecker Pointwise

variable {K : Type} [Field K] [CharP K 2]

theorem e6_table : e6 (0, 0) = 0 ∧ e6 (0, 1) = 1 ∧ e6 (0, 2) = 2 ∧ e6 (1, 0) = 3 ∧
    e6 (1, 1) = 4 ∧ e6 (1, 2) = 5 := by
  decide

theorem kronSL2_transvection_zero_one (t : K) :
    kronSL2 K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 3 by decide) t *
        Matrix.SpecialLinearGroup.transvection (show (1 : Fin 6) ≠ 4 by decide) t *
          Matrix.SpecialLinearGroup.transvection (show (2 : Fin 6) ≠ 5 by decide) t := by
  apply Subtype.ext
  change reindex e6 e6 _ = _
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := e6.surjective p
  obtain ⟨⟨i', j'⟩, rfl⟩ := e6.surjective q
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply]
  obtain ⟨t00, t01, t02, t10, t11, t12⟩ := e6_table
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [t00, t01, t02, t10, t11, t12, Matrix.SpecialLinearGroup.coe_mul,
      CFSG.LinearGroups.coe_transvection, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.one_apply, Matrix.single_apply]

theorem kronSL2_transvection_one_zero (t : K) :
    kronSL2 K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t) =
      Matrix.SpecialLinearGroup.transvection (show (3 : Fin 6) ≠ 0 by decide) t *
        Matrix.SpecialLinearGroup.transvection (show (4 : Fin 6) ≠ 1 by decide) t *
          Matrix.SpecialLinearGroup.transvection (show (5 : Fin 6) ≠ 2 by decide) t := by
  apply Subtype.ext
  change reindex e6 e6 _ = _
  ext p q
  obtain ⟨⟨i, j⟩, rfl⟩ := e6.surjective p
  obtain ⟨⟨i', j'⟩, rfl⟩ := e6.surjective q
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply]
  obtain ⟨t00, t01, t02, t10, t11, t12⟩ := e6_table
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [t00, t01, t02, t10, t11, t12, Matrix.SpecialLinearGroup.coe_mul,
      CFSG.LinearGroups.coe_transvection, Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.one_apply, Matrix.single_apply]

@[expose] def cubeCurve (b : Bool) (t : K) : ModGL .E7 K :=
  if b then cubeSL2 K (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) t)
  else cubeSL2 K (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) t)

theorem cubeCurve_zero (b : Bool) : cubeCurve b (0 : K) = 1 := by
  have h0 : ∀ (i j : Fin 2) (h : i ≠ j), Matrix.SpecialLinearGroup.transvection h (0 : K) = 1 :=
    fun i j h => Subtype.ext (by
      rw [CFSG.LinearGroups.coe_transvection, Matrix.single_zero, add_zero]
      rfl)
  cases b <;> simp [cubeCurve, h0]

theorem isPolynomialCurve_cubeCurve (b : Bool) : IsPolynomialCurve (cubeCurve (K := K) b) := by
  have key : ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : Fin 6) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂) (h₃ : a₃ ≠ b₃),
      IsPolynomialCurve fun t : K => a5Frame K (Matrix.SpecialLinearGroup.transvection h₁ t) *
        a5Frame K (Matrix.SpecialLinearGroup.transvection h₂ t) *
          a5Frame K (Matrix.SpecialLinearGroup.transvection h₃ t) := by
    intro a₁ b₁ a₂ b₂ a₃ b₃ h₁ h₂ h₃
    obtain ⟨ε₁, he₁⟩ := a5Frame_transv (L := K) a₁ b₁ h₁
    obtain ⟨ε₂, he₂⟩ := a5Frame_transv (L := K) a₂ b₂ h₂
    obtain ⟨ε₃, he₃⟩ := a5Frame_transv (L := K) a₃ b₃ h₃
    have hp (α : Fin Tag.E7.rank → ℤ) (ε : Kˣ) :
        IsPolynomialCurve fun t : K => pinnedX .E7 K α ((ε : K) * t) := by
      have := isPolynomialCurve_pinnedX (τ := .E7) (k := K) α
        (Polynomial.C (ε : K) * Polynomial.X)
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using this
    simp only [he₁, he₂, he₃]
    exact ((hp _ ε₁).mul (hp _ ε₂)).mul (hp _ ε₃)
  cases b
  · have h := key 3 0 4 1 5 2 (by decide) (by decide) (by decide)
    refine (funext fun t => ?_ : (cubeCurve (K := K) false) = _) ▸ h
    simp only [cubeCurve, Bool.false_eq_true, if_false, cubeSL2, MonoidHom.comp_apply,
      kronSL2_transvection_one_zero, map_mul]
  · have h := key 0 3 1 4 2 5 (by decide) (by decide) (by decide)
    refine (funext fun t => ?_ : (cubeCurve (K := K) true) = _) ▸ h
    simp only [cubeCurve, if_true, cubeSL2, MonoidHom.comp_apply,
      kronSL2_transvection_zero_one, map_mul]

theorem range_cubeSL2_eq_closure :
    (cubeSL2 K).range = Subgroup.closure (⋃ b, Set.range (cubeCurve (K := K) b)) := by
  rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2)
    (K := K), MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact Set.mem_iUnion.2 ⟨true, c, rfl⟩
    · exact Set.mem_iUnion.2 ⟨false, c, rfl⟩
    · exact absurd rfl hij
  · intro hg
    obtain ⟨b, c, rfl⟩ := Set.mem_iUnion.1 hg
    cases b
    · exact ⟨_, CFSG.LinearGroups.transvection_mem_elementarySet _ c, rfl⟩
    · exact ⟨_, CFSG.LinearGroups.transvection_mem_elementarySet _ c, rfl⟩

theorem isPointClosed_isPointIrreducible_range_cubeSL2 [IsAlgClosed K] :
    IsPointClosed K (transportPoints (modGLPoint .E7 K) ((cubeSL2 K).range : Set (ModGL .E7 K))) ∧
      IsPointIrreducible K
        (transportPoints (modGLPoint .E7 K) ((cubeSL2 K).range : Set (ModGL .E7 K))) := by
  let W : Bool → Set (SeminaireExp3.ZariskiGL (Label .E7) K) := fun b =>
    modGLZariski .E7 K '' Set.range (cubeCurve (K := K) b)
  have hW : ∀ b, SeminaireExp3.IsDomainImage K (SeminaireExp3.ZariskiGL.pt '' W b) := fun b =>
    isDomainImage_of_isPolynomialCurve (isPolynomialCurve_cubeCurve b)
  have h1 : ∀ b, (1 : SeminaireExp3.ZariskiGL (Label .E7) K) ∈ W b := fun b =>
    ⟨1, ⟨0, cubeCurve_zero b⟩, map_one _⟩
  obtain ⟨-, -, a, ha⟩ := SeminaireExp3.ZariskiGL.closure_eq_wordSet W hW h1
  have hS : modGLZariski .E7 K '' (⋃ b, Set.range (cubeCurve (K := K) b)) = ⋃ b, W b :=
    Set.image_iUnion
  have himg : modGLZariski .E7 K '' ((cubeSL2 K).range : Set (ModGL .E7 K)) =
      SeminaireExp3.ZariskiGL.wordSet W a := by
    rw [← ha, ← hS, range_cubeSL2_eq_closure]
    change (modGLZariski .E7 K).toMonoidHom ''
        ((Subgroup.closure (⋃ b, Set.range (cubeCurve (K := K) b)) : Subgroup (ModGL .E7 K)) :
          Set (ModGL .E7 K)) =
      ↑(Subgroup.closure ((modGLZariski .E7 K).toMonoidHom ''
        (⋃ b, Set.range (cubeCurve (K := K) b))))
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
  have hdom : SeminaireExp3.IsDomainImage K
      (transportPoints (modGLPoint .E7 K) ((cubeSL2 K).range : Set (ModGL .E7 K))) := by
    rw [transportPoints_eq_image_modGLZariski, himg]
    exact SeminaireExp3.ZariskiGL.isDomainImage_wordSet W hW a
  exact ⟨(isConnectedAlgebraicSubgroup_map (modGLPoint .E7 K) (cubeSL2 K).range
    hdom.isPointConstructible hdom.isPointIrreducible).1, hdom.isPointIrreducible⟩

theorem cubeE_le_normalizer_range_cubeSL2 (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    cubeE ζ hζ ≤ Subgroup.normalizer ((cubeSL2 K).range : Set (ModGL .E7 K)) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hcomm : ∀ {y : ModGL .E7 K}, y ∈ (cubeSL2 K).range → e * y = y * e := fun hy =>
    (Subgroup.mem_centralizer_iff.1 (range_cubeSL2_le_cubeCent ζ hζ hy).2) e he
  constructor
  · intro hx
    rw [hcomm hx, mul_inv_cancel_right]
    exact hx
  · intro hx
    have h := hcomm hx
    have hx' : x = e * x * e⁻¹ := by
      calc x = e⁻¹ * ((e * x * e⁻¹) * e) := by group
        _ = e⁻¹ * (e * (e * x * e⁻¹)) := by rw [h]
        _ = e * x * e⁻¹ := by group
    rw [hx']
    exact hx

section Steinberg

variable [IsAlgClosed K]

theorem coe_cubeCent_eq_mul {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    (cubeCent ζ hζ.pow_eq_one : Set (ModGL .E7 K)) =
      ((cubeSL2 K).range : Set (ModGL .E7 K)) * (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := by
  rw [cubeCent_eq_sup hζ]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (cubeE_le_normalizer_range_cubeSL2 ζ hζ.pow_eq_one)

theorem bijective_cubeE_toQuotient {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    Function.Bijective fun e : cubeE ζ hζ.pow_eq_one =>
      (QuotientGroup.mk ⟨(e : ModGL .E7 K), cubeE_le_cubeCent ζ _ e.2⟩ :
        cubeCent ζ hζ.pow_eq_one ⧸ (cubeSL2 K).range.subgroupOf (cubeCent ζ hζ.pow_eq_one)) := by
  constructor
  · rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have hmem : e₁⁻¹ * e₂ ∈ (cubeSL2 K).range ⊓ cubeE ζ hζ.pow_eq_one :=
      ⟨h, (cubeE ζ _).mul_mem ((cubeE ζ _).inv_mem he₁) he₂⟩
    rw [range_cubeSL2_inf_cubeE hζ, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      have hg : (g : ModGL .E7 K) ∈ ((cubeSL2 K).range : Set (ModGL .E7 K)) *
          (cubeE ζ hζ.pow_eq_one : Set (ModGL .E7 K)) := by
        rw [← coe_cubeCent_eq_mul hζ]
        exact g.2
      obtain ⟨σ, hσ, e, he, hσe⟩ := hg
      dsimp only at hσe
      refine ⟨⟨e, he⟩, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hc : σ * e = e * σ :=
        ((Subgroup.mem_centralizer_iff.1 (range_cubeSL2_le_cubeCent ζ _ hσ).2) e he).symm
      change (e : ModGL .E7 K)⁻¹ * (g : ModGL .E7 K) ∈ (cubeSL2 K).range
      rw [← hσe, hc, inv_mul_cancel_left]
      exact hσ

theorem card_cubeE {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    Nat.card (cubeE ζ hζ.pow_eq_one) = 27 := by
  rw [cubeE, Subgroup.card_map_of_injective Subtype.val_injective, card_range_cubeHom ζ hζ]
  norm_num

theorem closedIdentityComponent_cubeCent {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 3) :
    closedIdentityComponent (cubeCent ζ hζ.pow_eq_one) = (cubeSL2 K).range := by
  obtain ⟨hcl, hirr⟩ := isPointClosed_isPointIrreducible_range_cubeSL2 (K := K)
  have : Finite (cubeE ζ hζ.pow_eq_one) := Nat.finite_of_card_ne_zero (by rw [card_cubeE hζ]; norm_num)
  have : Finite (cubeCent ζ hζ.pow_eq_one ⧸
      (cubeSL2 K).range.subgroupOf (cubeCent ζ hζ.pow_eq_one)) :=
    Finite.of_surjective _ (bijective_cubeE_toQuotient hζ).2
  have : ((cubeSL2 K).range.subgroupOf (cubeCent ζ hζ.pow_eq_one)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  refine le_antisymm (closedIdentityComponent_le_of_isPointClosed_finiteIndex hcl) ?_
  exact subset_closedIdentityComponent (range_cubeSL2_le_cubeCent ζ _) (Subgroup.one_mem _) hirr

end Steinberg

end CFSG.LieType.Chevalley.E7Three.Centralizer
