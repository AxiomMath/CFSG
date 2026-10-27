module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6Gen
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Polynomial

variable {K : Type} [Field K]

theorem ff_aux_q_add_smul {V : Type} [AddCommGroup V] [Module K V] (q : QuadraticForm K V)
    {x y : V} (hxy : q.polarBilin x y = 0) (α β : K) :
    q (α • x + β • y) = α ^ 2 * q x + β ^ 2 * q y := by
  have hA : q (α • x) = α ^ 2 * q x := by rw [QuadraticMap.map_smul]; ring
  have hB : q (β • y) = β ^ 2 * q y := by rw [QuadraticMap.map_smul]; ring
  have hP : q.polarBilin (α • x) (β • y) = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, ← QuadraticMap.polarBilin_apply_apply, hxy]
    simp
  have h := QuadraticMap.map_add (⇑q) (α • x) (β • y)
  rw [h, hA, hB, ← QuadraticMap.polarBilin_apply_apply, hP]
  ring

theorem ff_aux_polar_add_smul {V : Type} [AddCommGroup V] [Module K V] (q : QuadraticForm K V)
    {x y : V} (hxy : q.polarBilin x y = 0) (α β γ δ : K) :
    q.polarBilin (α • x + β • y) (γ • x + δ • y) =
      (α * γ) * (2 * q x) + (β * δ) * (2 * q y) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [show α • x + β • y + (γ • x + δ • y) = (α + γ) • x + (β + δ) • y by module]
  rw [ff_aux_q_add_smul q hxy (α + γ) (β + δ), ff_aux_q_add_smul q hxy α β,
    ff_aux_q_add_smul q hxy γ δ]
  ring

theorem exists_smul_add_eq_one [Fintype K] (hodd : Fintype.card K % 2 = 1)
    {V : Type} [AddCommGroup V] [Module K V] (q : QuadraticForm K V) {x y : V}
    (hx : q x ≠ 0) (hy : q y ≠ 0) (hxy : q.polarBilin x y = 0) :
    ∃ α β : K, q (α • x + β • y) = 1 := by
  have hdegx : (C (q x) * X ^ 2 : K[X]).degree = 2 :=
    Polynomial.degree_C_mul_X_pow (a := q x) 2 hx
  have hdegy : (C (q y) * X ^ 2 - 1 : K[X]).degree = 2 := by
    have hdeg1 : (1 : K[X]).degree = 0 := Polynomial.degree_one
    have hlt : (1 : K[X]).degree < (C (q y) * X ^ 2 : K[X]).degree := by
      rw [hdeg1, Polynomial.degree_C_mul_X_pow (a := q y) 2 hy]
      norm_num
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt]
    exact Polynomial.degree_C_mul_X_pow (a := q y) 2 hy
  obtain ⟨α, β, hab⟩ := FiniteField.exists_root_sum_quadratic hdegx hdegy hodd
  refine ⟨α, β, ?_⟩
  rw [ff_aux_q_add_smul q hxy]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hab
  rw [show α ^ 2 * q x + β ^ 2 * q y = (q x * α ^ 2 + (q y * β ^ 2 - 1)) + 1 by ring]
  rw [hab, zero_add]

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_orthonormal_pair [Finite K] (q : QuadraticForm K V)
    (hq : q.polarBilin.Nondegenerate) (h3 : Module.finrank K V = 3) (h2 : (2 : K) ≠ 0)
    (hodd : Nat.card K % 2 = 1) :
    ∃ u₁ u₂ : V, q u₁ = 1 ∧ q u₂ = 1 ∧ q.polarBilin u₁ u₂ = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hodd' : Fintype.card K % 2 = 1 := by rw [← Nat.card_eq_fintype_card]; exact hodd
  haveI : Invertible (2 : K) := invertibleOfNonzero h2
  obtain ⟨b, hortho, haniso⟩ :=
    (QuadraticMap.nondegenerate_polar_iff.mp hq).exists_orthogonal_basis
  let b3 : Module.Basis (Fin 3) K V := b.reindex (finCongr h3)
  have hb3 : ∀ i : Fin 3, b3 i = b (finCongr h3.symm i) := by
    intro i
    change (b.reindex (finCongr h3)) i = b (finCongr h3.symm i)
    rw [Module.Basis.reindex_apply]
    rfl
  have hortho3 : ∀ i j : Fin 3, i ≠ j → q.polarBilin (b3 i) (b3 j) = 0 := by
    intro i j hij
    rw [hb3 i, hb3 j]
    exact (hortho _ _ (fun h => hij ((finCongr h3.symm).injective h))).polar_eq_zero
  have haniso3 : ∀ i : Fin 3, q (b3 i) ≠ 0 := by
    intro i; rw [hb3 i]; exact haniso _
  set d₁ : K := q (b3 0) with hd₁
  set d₂ : K := q (b3 1) with hd₂
  set d₃ : K := q (b3 2) with hd₃
  have hd₁' : d₁ ≠ 0 := haniso3 0
  have hd₂' : d₂ ≠ 0 := haniso3 1
  have hd₃' : d₃ ≠ 0 := haniso3 2
  have h01 : q.polarBilin (b3 0) (b3 1) = 0 := hortho3 0 1 (by decide)
  have h02 : q.polarBilin (b3 0) (b3 2) = 0 := hortho3 0 2 (by decide)
  have h12 : q.polarBilin (b3 1) (b3 2) = 0 := hortho3 1 2 (by decide)
  obtain ⟨a₁, a₂, ha⟩ := exists_smul_add_eq_one hodd' q hd₁' hd₂' h01
  set u₁ : V := a₁ • b3 0 + a₂ • b3 1 with hu₁def
  have hu₁ : q u₁ = 1 := ha
  have hqu₁ : a₁ ^ 2 * d₁ + a₂ ^ 2 * d₂ = 1 := by
    rw [hu₁def, ff_aux_q_add_smul q h01, ← hd₁, ← hd₂] at hu₁
    exact hu₁
  set w : V := (a₂ * d₂) • b3 0 + (-(a₁ * d₁)) • b3 1 with hwdef
  have hqw : q w = d₁ * d₂ := by
    rw [hwdef, ff_aux_q_add_smul q h01 (a₂ * d₂) (-(a₁ * d₁)), ← hd₁, ← hd₂]
    linear_combination (d₁ * d₂) * hqu₁
  have hpol1 : q.polarBilin u₁ w = 0 := by
    rw [hu₁def, hwdef,
      ff_aux_polar_add_smul q h01 a₁ a₂ (a₂ * d₂) (-(a₁ * d₁)), ← hd₁, ← hd₂]
    ring
  have hpol2 : q.polarBilin w (b3 2) = 0 := by
    rw [hwdef, QuadraticMap.polarBilin_apply_apply]
    simp only [QuadraticMap.polarBilin_apply_apply] at h02 h12
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      h02, h12]
    ring
  have hqw' : q w ≠ 0 := by rw [hqw]; exact mul_ne_zero hd₁' hd₂'
  obtain ⟨c₁, c₂, hc⟩ := exists_smul_add_eq_one hodd' q hqw' hd₃' hpol2
  refine ⟨u₁, c₁ • w + c₂ • b3 2, hu₁, hc, ?_⟩
  have hpol3 : q.polarBilin u₁ (b3 2) = 0 := by
    rw [hu₁def, QuadraticMap.polarBilin_apply_apply]
    simp only [QuadraticMap.polarBilin_apply_apply] at h02 h12
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
      h02, h12]
    ring
  simp only [QuadraticMap.polarBilin_apply_apply] at hpol1 hpol3 ⊢
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
    hpol1, hpol3]
  simp

end CFSG.OddStandard.SmallF3.Omega
