module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.GH74.Generic.S1.Exo.HermOddDefs

public section

namespace CFSG.GH74.Generic.S1.Exo

open Module Matrix
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F]

theorem sl2_isPerfect_of_four_le (h4 : 4 ≤ Nat.card F) : Group.IsPerfect SL(2, F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  refine CFSG.LinearGroups.special_linear_dimension_two_perfect ?_
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem natCard_sl2_eq_of_finite [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_SL_field, Fin.prod_univ_two, ← Nat.card_eq_fintype_card]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  set q := Nat.card F with hq
  have hq1 : 2 ≤ q := by
    have := Fintype.one_lt_card (α := F)
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have h1 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, _root_.sq]
  rw [h1, show (q ^ 2 - 1) * (q * (q - 1)) = q * (q ^ 2 - 1) * (q - 1) by ring,
    Nat.mul_div_cancel _ (by omega)]

theorem natCard_center_sl2_eq_two (h2 : (2 : F) ≠ 0) :
    Nat.card (Subgroup.center SL(2, F)) = 2 := by
  have hp : ringChar F ≠ 2 := fun h => h2 (by
    have := CharP.cast_eq_zero F (ringChar F)
    rw [h] at this
    exact_mod_cast this)
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 2)).toEquiv,
    Fintype.card_fin]
  exact (IsPrimitiveRoot.neg_one (ringChar F) hp).card_rootsOfUnity

end SL2

section Kernel

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

@[expose] noncomputable def hermOddElt (x y : K) (z : E) : hermOddSpace D.σ :=
  ⟨hermOddMat D.σ x y z, hermOddMat_mem D x y z⟩

omit [Finite K] in
theorem two_ne_zero_of_two_ne_zero (h2 : (2 : K) ≠ 0) : (2 : E) ≠ 0 := fun h => h2 (by
  apply (algebraMap K E).injective
  rw [map_ofNat, map_zero]
  exact h)

theorem hermOddRho_scalar_entries (g : SL(2, E)) (c : K)
    (h : ∀ X : hermOddSpace D.σ, hermOddRho D g X = c • X) :
    g.1 0 1 = 0 ∧ g.1 1 0 = 0 ∧ g.1 0 0 * g.1 1 1 = 1 ∧
      g.1 0 0 * D.σ (g.1 0 0) = algebraMap K E c ∧ g.1 1 1 * D.σ (g.1 1 1) = algebraMap K E c ∧
      g.1 0 0 * D.σ (g.1 1 1) = algebraMap K E c ∧ g.1 1 1 * D.σ (g.1 0 0) = algebraMap K E c := by
  have hE11 := congrArg Subtype.val (h (hermOddElt D 1 0 0))
  have hE22 := congrArg Subtype.val (h (hermOddElt D 0 1 0))
  have hU := congrArg Subtype.val (h (hermOddElt D 0 0 1))
  rw [coe_hermOddRho, Submodule.coe_smul] at hE11 hE22 hU
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  have a11 := congrFun (congrFun hE11 0) 0
  have a21 := congrFun (congrFun hE11 1) 0
  have a22 := congrFun (congrFun hE11 1) 1
  have b11 := congrFun (congrFun hE22 0) 0
  have b22 := congrFun (congrFun hE22 1) 1
  have u12 := congrFun (congrFun hU 0) 1
  have u21 := congrFun (congrFun hU 1) 0
  simp only [Matrix.smul_apply] at a11 a21 a22 b11 b22 u12 u21
  simp [hermOddElt, hermOddMat, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def] at a11 a21 a22
  simp [hermOddElt, hermOddMat, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def] at b11 b22
  simp [hermOddElt, hermOddMat, Matrix.mul_apply, Fin.sum_univ_two, Algebra.smul_def] at u12 u21
  refine ⟨b11, a22, ?_, a11, b22, ?_, ?_⟩
  · rw [b11, a22] at hdet
    simpa using hdet
  · simpa [b11, a22] using u12
  · simpa [b11, a22] using u21

theorem mem_center_of_hermOddRho_eq_one (g : SL(2, E)) (h : hermOddRho D g = 1) :
    g ∈ Subgroup.center SL(2, E) := by
  have h' : ∀ X : hermOddSpace D.σ, hermOddRho D g X = (1 : K) • X := fun X => by
    rw [h, one_smul]
    rfl
  obtain ⟨hb, hc, had, h11, h22, h12, h21⟩ := hermOddRho_scalar_entries D g 1 h'
  rw [map_one] at h11 h22 h12 h21
  have ha0 : g.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hdσ : D.σ (g.1 1 1) = g.1 1 1 := by
    have : g.1 0 0 * (D.σ (g.1 1 1) - g.1 1 1) = 0 := by
      rw [mul_sub, h12, had, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha0)
  have hd2 : g.1 1 1 * g.1 1 1 = 1 := by
    have := h22
    rwa [hdσ] at this
  have had' : g.1 0 0 = g.1 1 1 := by
    calc g.1 0 0 = g.1 0 0 * (g.1 1 1 * g.1 1 1) := by rw [hd2, mul_one]
      _ = (g.1 0 0 * g.1 1 1) * g.1 1 1 := by ring
      _ = g.1 1 1 := by rw [had, one_mul]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨g.1 0 0, ?_, ?_⟩
  · rw [Fintype.card_fin, sq]
    nth_rewrite 2 [had']
    exact had
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hb, hc, had']

theorem hermOddRho_eq_one_of_mem_center (g : SL(2, E)) (hg : g ∈ Subgroup.center SL(2, E)) :
    hermOddRho D g = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hg
  obtain ⟨r, hr, hrg⟩ := hg
  rw [Fintype.card_fin, sq] at hr
  have hσ : D.σ r = r := by
    rcases mul_self_eq_one_iff.mp hr with rfl | rfl <;> simp
  have key : ∀ x : E, r * x * r = x := fun x => by linear_combination x * hr
  refine LinearEquiv.ext fun X => Subtype.ext ?_
  rw [coe_hermOddRho, ← hrg]
  change _ = (X : Matrix (Fin 2) (Fin 2) E)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, hσ, key]

theorem ker_hermOddRho : (hermOddRho D).ker = Subgroup.center SL(2, E) := by
  ext g
  exact ⟨mem_center_of_hermOddRho_eq_one D g, hermOddRho_eq_one_of_mem_center D g⟩

theorem neg_not_mem_range_hermOddRho (h2 : (2 : K) ≠ 0) :
    LinearEquiv.neg K ∉ (hermOddRho D).range := by
  rintro ⟨g, hg⟩
  have h' : ∀ X : hermOddSpace D.σ, hermOddRho D g X = (-1 : K) • X := fun X => by
    rw [hg]
    exact (neg_one_smul K X).symm
  obtain ⟨hb, hc, had, h11, h22, h12, h21⟩ := hermOddRho_scalar_entries D g (-1) h'
  rw [map_neg, map_one] at h11 h22 h12 h21
  have ha0 : g.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one had
  have hdσ : D.σ (g.1 1 1) = - g.1 1 1 := by
    have : g.1 0 0 * (D.σ (g.1 1 1) + g.1 1 1) = 0 := by
      rw [mul_add, h12, had]
      ring
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left ha0)
  have hd2 : g.1 1 1 * g.1 1 1 = 1 := by
    have := h22
    rw [hdσ] at this
    linear_combination -this
  have hd : g.1 1 1 = 1 ∨ g.1 1 1 = -1 := mul_self_eq_one_iff.mp hd2
  have hfix : D.σ (g.1 1 1) = g.1 1 1 := by
    rcases hd with h | h <;> rw [h] <;> simp
  rw [hfix] at hdσ
  have h20 : (2 : E) * g.1 1 1 = 0 := by linear_combination hdσ
  have := (mul_eq_zero.mp h20).resolve_left (two_ne_zero_of_two_ne_zero h2)
  rw [this] at hd2
  simp at hd2

end Kernel

section Image

variable {K E : Type} [Field K] [Finite K] [Field E] [Algebra K E] (D : OddNormPlane K E)

@[expose] noncomputable def hermOddRangeEquiv :
    (hermOddRho D).range ≃* ProjectiveSpecialLinearGroup (Fin 2) E :=
  (QuotientGroup.quotientKerEquivRange (hermOddRho D)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_hermOddRho D))

theorem isSimpleGroup_hermOddRho_range (h4 : 4 ≤ Nat.card E) :
    IsSimpleGroup (hermOddRho D).range := by
  have : IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin 2) E) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (hermOddRangeEquiv D).isSimpleGroup

theorem isPerfect_hermOddRho_range (h4 : 4 ≤ Nat.card E) :
    Group.IsPerfect (hermOddRho D).range := by
  have := sl2_isPerfect_of_four_le h4
  exact Group.IsPerfect.range _

theorem det_hermOddRho (h4 : 4 ≤ Nat.card E) (g : SL(2, E)) :
    LinearEquiv.det (hermOddRho D g) = 1 := by
  have := sl2_isPerfect_of_four_le h4
  let φ : SL(2, E) →* Kˣ := LinearEquiv.det.comp (hermOddRho D)
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton φ.range := inferInstance
  have h1 : (⟨φ g, g, rfl⟩ : φ.range) = ⟨1, φ.range.one_mem⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val h1

theorem natCard_hermOddRho_range_mul_two [Finite E] (h2 : (2 : K) ≠ 0) :
    Nat.card (hermOddRho D).range * 2 = Nat.card E * (Nat.card E ^ 2 - 1) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (hermOddRho D).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (hermOddRho D)).toEquiv,
    ker_hermOddRho, natCard_center_sl2_eq_two (two_ne_zero_of_two_ne_zero h2),
    natCard_sl2_eq_of_finite] at h1
  exact h1.symm

end Image

end CFSG.GH74.Generic.S1.Exo
