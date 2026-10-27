module

public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution

public section

namespace CFSG.QuasithinUnique

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {K : Type*} [Field K]

section Commutant

variable {x y : Matrix (Fin 2) (Fin 2) K}

theorem ne_scalar_of_anticomm (hK : ringChar K ≠ 2) (hx : x * x = -1) (hy : y * y = -1)
    (hxy : x * y = -(y * x)) (c : K) : x ≠ scalar (Fin 2) c := by
  intro hc
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hcomm : x * y = y * x := by
    rw [hc]
    exact (scalar_commute c (fun _ => Commute.all _ _) y)
  have hxy0 : x * y = 0 := by
    have h : (2 : K) • (x * y) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hxy]
      rw [hcomm, add_neg_cancel]
    exact (smul_eq_zero.1 h).resolve_left h2
  have hy0 : y = 0 := by
    calc y = -((x * x) * y) := by rw [hx, neg_one_mul, neg_neg]
      _ = 0 := by rw [Matrix.mul_assoc, hxy0, Matrix.mul_zero, neg_zero]
  have : (-1 : Matrix (Fin 2) (Fin 2) K) = 0 := by rw [← hy, hy0, Matrix.mul_zero]
  exact one_ne_zero (neg_eq_zero.1 this)

theorem eq_zero_of_smul_add_smul (hns : ∀ c : K, x ≠ scalar (Fin 2) c) {a b : K}
    (h : a • (1 : Matrix (Fin 2) (Fin 2) K) + b • x = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.1 h).resolve_right one_ne_zero, rfl⟩
  · refine absurd ?_ (hns (-(a / b)))
    have e : b • x = -(a • (1 : Matrix (Fin 2) (Fin 2) K)) := eq_neg_of_add_eq_zero_right h
    calc x = b⁻¹ • (b • x) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = scalar (Fin 2) (-(a / b)) := by
        rw [e, smul_neg, smul_smul, scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul,
          div_eq_inv_mul]

theorem linearIndependent_quaternion (hK : ringChar K ≠ 2) (hx : x * x = -1) (hy : y * y = -1)
    (hxy : x * y = -(y * x)) :
    LinearIndependent K ![(1 : Matrix (Fin 2) (Fin 2) K), x, y, x * y] := by
  have hns := ne_scalar_of_anticomm hK hx hy hxy
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at hg
  have hxxx : x * x * x = -x := by rw [hx, neg_one_mul]
  have hxyx : x * y * x = y := by
    rw [hxy, neg_mul, Matrix.mul_assoc, hx, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  have hxxyx : x * (x * y) * x = x * y := by
    rw [Matrix.mul_assoc, hxyx]
  set T := g 0 • (1 : Matrix (Fin 2) (Fin 2) K) + g 1 • x + g 2 • y + g 3 • (x * y) with hT
  have hconj : x * T * x = -(g 0 • (1 : Matrix (Fin 2) (Fin 2) K) + g 1 • x) +
      (g 2 • y + g 3 • (x * y)) := by
    have e1 : x * T * x = g 0 • (x * 1 * x) + g 1 • (x * x * x) + g 2 • (x * y * x) +
        g 3 • (x * (x * y) * x) := by
      rw [hT]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e1, hxxx, hxxyx, hxyx, Matrix.mul_one, hx]
    module
  have hT0 : T = 0 := hg
  rw [hT0, Matrix.mul_zero, Matrix.zero_mul] at hconj
  have hsum : T = (g 0 • (1 : Matrix (Fin 2) (Fin 2) K) + g 1 • x) +
      (g 2 • y + g 3 • (x * y)) := by
    rw [hT]
    abel
  rw [hT0] at hsum
  have hA : g 0 • (1 : Matrix (Fin 2) (Fin 2) K) + g 1 • x = 0 := by
    have : (2 : K) • (g 0 • (1 : Matrix (Fin 2) (Fin 2) K) + g 1 • x) = 0 := by
      rw [two_smul]
      linear_combination (norm := module) hconj - hsum
    exact (smul_eq_zero.1 this).resolve_left h2
  have hB : g 2 • y + g 3 • (x * y) = 0 := by
    have : (2 : K) • (g 2 • y + g 3 • (x * y)) = 0 := by
      rw [two_smul]
      linear_combination (norm := module) -hsum - hconj
    exact (smul_eq_zero.1 this).resolve_left h2
  have hB' : g 2 • (1 : Matrix (Fin 2) (Fin 2) K) + g 3 • x = 0 := by
    have h := congrArg (· * y) hB
    simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc, hy, Matrix.zero_mul,
      Matrix.mul_neg, Matrix.mul_one, smul_neg] at h
    rw [← neg_add, neg_eq_zero] at h
    exact h
  obtain ⟨h0, h1⟩ := eq_zero_of_smul_add_smul hns hA
  obtain ⟨h2', h3⟩ := eq_zero_of_smul_add_smul hns hB'
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2'
  · exact h3

theorem span_quaternion_eq_top (hK : ringChar K ≠ 2) (hx : x * x = -1) (hy : y * y = -1)
    (hxy : x * y = -(y * x)) :
    Submodule.span K (Set.range ![(1 : Matrix (Fin 2) (Fin 2) K), x, y, x * y]) = ⊤ := by
  refine (linearIndependent_quaternion hK hx hy hxy).span_eq_top_of_card_eq_finrank ?_
  rw [Module.finrank_matrix, Module.finrank_self, Fintype.card_fin, Fintype.card_fin]

theorem eq_scalar_of_commute_quaternion (hK : ringChar K ≠ 2) (hx : x * x = -1)
    (hy : y * y = -1) (hxy : x * y = -(y * x)) {B : Matrix (Fin 2) (Fin 2) K}
    (hBx : Commute B x) (hBy : Commute B y) : ∃ c : K, B = scalar (Fin 2) c := by
  have hall : ∀ M : Matrix (Fin 2) (Fin 2) K, Commute B M := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ![(1 : Matrix (Fin 2) (Fin 2) K), x, y, x * y]) := by
      rw [span_quaternion_eq_top hK hx hy hxy]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hM
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact Commute.one_right B
      · exact hBx
      · exact hBy
      · exact hBx.mul_right hBy
    · exact Commute.zero_right B
    · intro u v _ _ hu hv
      exact hu.add_right hv
    · intro a u _ hu
      exact hu.smul_right a
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := B) fun i j _ =>
    (hall _).symm
  exact ⟨c, hc.symm⟩

end Commutant

section Sylow

@[expose] def IsQuaternionPair (x y : Matrix.SpecialLinearGroup (Fin 2) K) : Prop :=
  x ^ 2 = -1 ∧ y ^ 2 = -1 ∧ x * y = -(y * x)

theorem IsQuaternionPair.matrix {x y : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : IsQuaternionPair x y) :
    (x : Matrix (Fin 2) (Fin 2) K) * x = -1 ∧ (y : Matrix (Fin 2) (Fin 2) K) * y = -1 ∧
      (x : Matrix (Fin 2) (Fin 2) K) * y = -((y : Matrix (Fin 2) (Fin 2) K) * x) := by
  obtain ⟨hx, hy, hxy⟩ := h
  have cx := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K)) hx
  have cy := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K)) hy
  have cxy := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K)) hxy
  simp only [Matrix.SpecialLinearGroup.coe_neg, sq] at cx cy cxy
  exact ⟨cx, cy, cxy⟩

theorem IsQuaternionPair.conj {x y : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : IsQuaternionPair x y) (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    IsQuaternionPair (g * x * g⁻¹) (g * y * g⁻¹) := by
  obtain ⟨hx, hy, hxy⟩ := h
  have hneg : ∀ u : Matrix.SpecialLinearGroup (Fin 2) K, g * (-u) * g⁻¹ = -(g * u * g⁻¹) :=
    fun u => by rw [mul_neg, neg_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [conj_pow, hx, hneg, mul_one, mul_inv_cancel]
  · rw [conj_pow, hy, hneg, mul_one, mul_inv_cancel]
  · rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hxy, hneg,
      show g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ by group]

theorem exists_quaternion_pair_mem_sylow [Finite K] (hK : ringChar K ≠ 2)
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) K)) :
    ∃ x ∈ P, ∃ y ∈ P, IsQuaternionPair x y := by
  obtain ⟨a, b, hab⟩ := finite_odd_field_two_squares hK (-1)
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ := sl2_exists_anticommuting_pair hab
  have hz := sl2_neg_one_ne_one hK (k := K)
  obtain ⟨H, hxH, hyH, ⟨e⟩⟩ := exists_quaternion_subgroup_of_anticommuting hz
    ((sl2_sq_eq_one_iff hK _).2 (Or.inr rfl)) hx hy hxy
  have hH : IsPGroup 2 H := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  obtain ⟨P', hHP'⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) K) P' P
  have hmem : ∀ u ∈ H, g * u * g⁻¹ ∈ P := by
    intro u hu
    rw [← hg]
    change g * u * g⁻¹ ∈ MulAut.conj g • (P' : Subgroup (SpecialLinearGroup (Fin 2) K))
    rw [Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨u, hHP' hu, by rw [MulAut.smul_def, MulAut.conj_apply]⟩
  exact ⟨g * x * g⁻¹, hmem x hxH, g * y * g⁻¹, hmem y hyH,
    IsQuaternionPair.conj ⟨hx, hy, by rw [hxy, neg_one_mul]⟩ g⟩

end Sylow

end CFSG.QuasithinUnique
