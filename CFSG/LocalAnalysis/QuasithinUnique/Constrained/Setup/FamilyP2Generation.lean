module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.SectionRank.OddCover

section ThreeInvolutions

@[expose] def slMk {R : Type*} [CommRing R] (a b c d : R) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem coe_slMk {R : Type*} [CommRing R] (a b c d : R) (h : a * d - b * c = 1) :
    (slMk a b c d h : Matrix (Fin 2) (Fin 2) R) = !![a, b; c, d] := rfl

@[expose] def slA {R : Type*} [CommRing R] : Matrix.SpecialLinearGroup (Fin 2) R :=
  slMk 0 (-1) 1 0 (by simp)

theorem coe_slA {R : Type*} [CommRing R] :
    (slA : Matrix.SpecialLinearGroup (Fin 2) R).1 = !![0, -1; 1, 0] := rfl

theorem det_slB {R : Type*} [CommRing R] {x y : R} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    x * -x - y * (y - x) = 1 := by
  linear_combination (-1 : R) * hq

theorem det_slC {R : Type*} [CommRing R] {x y : R} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    y * -y - (y - x) * -x = 1 := by
  linear_combination (-1 : R) * hq

@[expose] def slB {R : Type*} [CommRing R] {x y : R} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  slMk x y (y - x) (-x) (det_slB hq)

@[expose] def slC {R : Type*} [CommRing R] {x y : R} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    Matrix.SpecialLinearGroup (Fin 2) R :=
  slMk y (y - x) (-x) (-y) (det_slC hq)

theorem slB_mul_T {K : Type*} [Field K] {x y : K} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    slB hq * (slA * slU 1) = slC hq := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show (!![x, y; y - x, -x] : Matrix (Fin 2) (Fin 2) K) * (!![0, -1; 1, 0] * !![1, 1; 0, 1]) =
    !![y, y - x; -x, -y]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_transvection_upper {K : Type*} [CommRing K] (c : K) (h : (0 : Fin 2) ≠ 1) :
    ((Matrix.SpecialLinearGroup.transvection h c : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

theorem coe_transvection_lower {K : Type*} [CommRing K] (c : K) (h : (1 : Fin 2) ≠ 0) :
    ((Matrix.SpecialLinearGroup.transvection h c : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection, Matrix.transvection]

theorem upper_eq_slU {K : Type*} [Field K] (c : K) (h : (0 : Fin 2) ≠ 1) :
    Matrix.SpecialLinearGroup.transvection h c = slU c :=
  Subtype.ext (by rw [coe_transvection_upper]; rfl)

theorem lower_mul_A {K : Type*} [Field K] (c : K) (h : (1 : Fin 2) ≠ 0) :
    Matrix.SpecialLinearGroup.transvection h c * slA = slA * slU (-c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_transvection_lower]
  show (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K) * !![0, -1; 1, 0] =
    !![0, -1; 1, 0] * !![1, -c; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem proj_slU_natCast {K : Type*} [Field K] (n : ℕ) :
    proj 2 K (slU (n : K)) = (proj 2 K (slU 1)) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, slU_zero, map_one, pow_zero]
  | succ n ih => rw [Nat.cast_succ, slU_add, map_mul, ih, pow_succ]

theorem closure_proj_ABC_eq_top {K : Type*} [Field K] (hK : ∀ c : K, ∃ n : ℕ, (n : K) = c)
    {x y : K} (hq : x ^ 2 - x * y + y ^ 2 = -1) :
    Subgroup.closure {proj 2 K slA, proj 2 K (slB hq), proj 2 K (slC hq)} = ⊤ := by
  set H := Subgroup.closure {proj 2 K slA, proj 2 K (slB hq), proj 2 K (slC hq)} with hH
  have hA : proj 2 K slA ∈ H := Subgroup.subset_closure (by simp)
  have hB : proj 2 K (slB hq) ∈ H := Subgroup.subset_closure (by simp)
  have hC : proj 2 K (slC hq) ∈ H := Subgroup.subset_closure (by simp)
  have hT : proj 2 K (slA * slU 1) ∈ H := by
    have h2 : proj 2 K (slB hq) * proj 2 K (slA * slU 1) = proj 2 K (slC hq) := by
      rw [← map_mul, slB_mul_T]
    rw [eq_inv_mul_of_mul_eq h2]
    exact H.mul_mem (H.inv_mem hB) hC
  have hU : proj 2 K (slU 1) ∈ H := by
    have h1 : proj 2 K (slU 1) = (proj 2 K slA)⁻¹ * proj 2 K (slA * slU 1) := by
      rw [map_mul, inv_mul_cancel_left]
    rw [h1]
    exact H.mul_mem (H.inv_mem hA) hT
  have hUc : ∀ c : K, proj 2 K (slU c) ∈ H := fun c => by
    obtain ⟨n, rfl⟩ := hK c
    rw [proj_slU_natCast]
    exact H.pow_mem hU n
  have hL : ∀ (c : K) (h : (1 : Fin 2) ≠ 0),
      proj 2 K (Matrix.SpecialLinearGroup.transvection h c) ∈ H := fun c h => by
    have h1 : proj 2 K (Matrix.SpecialLinearGroup.transvection h c) =
        proj 2 K slA * proj 2 K (slU (-c)) * (proj 2 K slA)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul, lower_mul_A]
    rw [h1]
    exact H.mul_mem (H.mul_mem hA (hUc _)) (H.inv_mem hA)
  have hall : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤ H.comap (proj 2 K) := by
    rw [← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    have hi : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
    show proj 2 K (Matrix.SpecialLinearGroup.transvection hij c) ∈ H
    rcases hi i with rfl | rfl <;> rcases hi j with rfl | rfl
    · exact absurd rfl hij
    · rw [upper_eq_slU]
      exact hUc c
    · exact hL c hij
    · exact absurd rfl hij
  rw [eq_top_iff]
  intro s _
  obtain ⟨g, rfl⟩ := proj_surjective 2 K s
  exact hall (Subgroup.mem_top g)

theorem sl2_trace_zero_sq {R : Type*} [CommRing R] (a b c d : R) (htr : a + d = 0)
    (hdet : a * d - b * c = 1) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R) * !![a, b; c, d] =
      Matrix.scalar (Fin 2) (-1 : R) := by
  have hd : d = -a := eq_neg_of_add_eq_zero_right htr
  subst hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] <;>
    (first | ring1 | linear_combination (-1 : R) * hdet)

theorem proj_involution_of_trace_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (M : Matrix.SpecialLinearGroup (Fin 2) K)
    (htr : (M : Matrix (Fin 2) (Fin 2) K) 0 0 + (M : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    proj 2 K M ≠ 1 ∧ proj 2 K M * proj 2 K M = 1 := by
  have hdet := M.2
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨a, b, c, d, e⟩ : ∃ a b c d : K, (M : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet' : a * d - b * c = 1 := by
    have h := hdet
    simp only [e] at h
    simpa using h
  have htr' : a + d = 0 := by
    have h := htr
    simp only [e] at h
    simpa using h
  refine ⟨fun h => ?_, ?_⟩
  · rw [proj_eq_one_iff] at h
    obtain ⟨c', -, hc⟩ := h
    rw [e] at hc
    have h1 := congrFun (congrFun hc 0) 0
    have h2' := congrFun (congrFun hc 1) 1
    simp [Matrix.scalar_apply] at h1 h2'
    have h3 : (2 : K) * (c' : K) = 0 := by
      calc (2 : K) * (c' : K) = (c' : K) + (c' : K) := two_mul _
        _ = a + d := by rw [h1, h2']
        _ = 0 := htr'
    exact c'.ne_zero ((mul_eq_zero.1 h3).resolve_left h2)
  · rw [← map_mul, proj_eq_one_iff]
    refine ⟨-1, neg_one_sq, ?_⟩
    have hmul : ((M * M : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (M : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K) := rfl
    refine hmul.trans ?_
    rw [e]
    simpa using sl2_trace_zero_sq a b c d htr' hdet'

theorem coe_slA_trace {R : Type*} [CommRing R] :
    (slA : Matrix.SpecialLinearGroup (Fin 2) R).1 0 0 +
      (slA : Matrix.SpecialLinearGroup (Fin 2) R).1 1 1 = 0 := by
  simp [coe_slA]

theorem exists_norm_one_pair {K : Type*} [Field K] [Fintype K] (hodd : Fintype.card K % 2 = 1)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : ∃ x y : K, x ^ 2 - x * y + y ^ 2 = -1 := by
  have hf : (Polynomial.X ^ 2 + Polynomial.C (4 : K)).degree = 2 := by
    rw [Polynomial.degree_X_pow_add_C (by norm_num)]
    rfl
  have hg : (Polynomial.C (3 : K) * Polynomial.X ^ 2).degree = 2 := by
    rw [Polynomial.degree_C_mul_X_pow 2 h3]
    rfl
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_mul] at hab
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  refine ⟨(a + b) / 2, b, mul_left_cancel₀ h4 ?_⟩
  have hx : 2 * ((a + b) / 2) = a + b := by field_simp
  linear_combination (2 * ((a + b) / 2) + a - b) * hx + hab

theorem natCast_ne_zero_zmod {p : ℕ} [hpf : Fact p.Prime] {n : ℕ} (hn0 : 0 < n) (hn : n < p) :
    (n : ZMod p) ≠ 0 := fun h =>
  absurd (Nat.le_of_dvd hn0 ((CharP.cast_eq_zero_iff (ZMod p) p n).1 h)) (by omega)

theorem p2_three_involution_generation {p : ℕ} [hpf : Fact p.Prime] (hp5 : 5 ≤ p)
    {a : projectiveSL 2 (ZMod p)} (ha1 : a ≠ 1) (ha2 : a * a = 1) :
    ∃ a₁ a₂ a₃ : projectiveSL 2 (ZMod p), IsConj a a₁ ∧ IsConj a a₂ ∧ IsConj a a₃ ∧
      Subgroup.closure {a₁, a₂, a₃} = ⊤ := by
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_zmod (p := p) (n := 2) (by norm_num) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := by
    simpa using natCast_ne_zero_zmod (p := p) (n := 3) (by norm_num) (by omega)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    exact Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  obtain ⟨x, y, hq⟩ := exists_norm_one_pair hodd h2 h3
  obtain ⟨hconj, -⟩ := p2_involution_structure hp5
  have hA := proj_involution_of_trace_zero h2 (slA : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    coe_slA_trace
  have hB := proj_involution_of_trace_zero h2 (slB hq) (by simp [slB, slMk])
  have hC := proj_involution_of_trace_zero h2 (slC hq) (by simp [slC, slMk])
  refine ⟨proj 2 (ZMod p) slA, proj 2 (ZMod p) (slB hq), proj 2 (ZMod p) (slC hq), ?_, ?_, ?_,
    closure_proj_ABC_eq_top (fun c => ⟨c.val, ZMod.natCast_zmod_val c⟩) hq⟩
  · obtain ⟨g, hg⟩ := hconj a _ ha1 ha2 hA.1 hA.2
    exact isConj_iff.2 ⟨g, hg⟩
  · obtain ⟨g, hg⟩ := hconj a _ ha1 ha2 hB.1 hB.2
    exact isConj_iff.2 ⟨g, hg⟩
  · obtain ⟨g, hg⟩ := hconj a _ ha1 ha2 hC.1 hC.2
    exact isConj_iff.2 ⟨g, hg⟩

end ThreeInvolutions

end CFSG.QuasithinUnique.Setup.Family
