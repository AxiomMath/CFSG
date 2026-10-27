module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnCore
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnFix
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1UnGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def u3N (h : UnitaryFieldData p f K) (a b : K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  single (Sum.inl 0) (Sum.inr (Sum.inl 0)) (-h.bar a) +
    single (Sum.inl 0) (Sum.inr (Sum.inr 0)) b +
      single (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inr 0)) a

theorem rkOneQ_eq_one_add (h : UnitaryFieldData p f K) (a b : K) :
    rkOneQ h a b = 1 + u3N h a b := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
    simp [u3N, rkOneQ, heisenbergMatrix, hypIndexFin3]

theorem rkOneQElt_mem_unRad (h : UnitaryFieldData p f K) {a b : K}
    (hab : h.norm a + h.trace b = 0) :
    rkOneQElt h a b hab ∈ unRad h (le_refl 1) (le_refl 1) := by
  refine mem_unRad_of_nil h (le_refl 1) (le_refl 1) _ (u3N h a b) ?_ ?_
  · rw [coe_rkOneQElt]
    exact rkOneQ_eq_one_add h a b
  · intro i j hij
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
      simp_all [u3N, fullPos]

section Entries

variable (h : UnitaryFieldData p f K) (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (σ : K ≃+* K)
  (a b : K) (hcomm : A * (u3N h a b).map σ = u3N h a b * A)
include hcomm

theorem u3_ze : a * A (Sum.inr (Sum.inr 0)) (Sum.inl 0) = 0 := by
  have := congrFun (congrFun hcomm (Sum.inr (Sum.inl 0))) (Sum.inl 0)
  simpa [u3N, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply] using this.symm

theorem u3_ee : -h.bar a * A (Sum.inr (Sum.inl 0)) (Sum.inl 0) +
    b * A (Sum.inr (Sum.inr 0)) (Sum.inl 0) = 0 := by
  have := congrFun (congrFun hcomm (Sum.inl 0)) (Sum.inl 0)
  simpa [u3N, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply] using this.symm

theorem u3_ez : -(A (Sum.inl 0) (Sum.inl 0) * σ (h.bar a)) =
    -(h.bar a * A (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0))) +
      b * A (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl 0)) := by
  have := congrFun (congrFun hcomm (Sum.inl 0)) (Sum.inr (Sum.inl 0))
  simpa [u3N, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply] using this

theorem u3_zz : -(A (Sum.inr (Sum.inl 0)) (Sum.inl 0) * σ (h.bar a)) =
    a * A (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl 0)) := by
  have := congrFun (congrFun hcomm (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inl 0))
  simpa [u3N, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply] using this

theorem u3_zf : A (Sum.inr (Sum.inl 0)) (Sum.inl 0) * σ b +
    A (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)) * σ a =
      a * A (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) := by
  have := congrFun (congrFun hcomm (Sum.inr (Sum.inl 0))) (Sum.inr (Sum.inr 0))
  simpa [u3N, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply] using this

end Entries

theorem u3_cube_zero (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    (h1 : M (Sum.inr (Sum.inl 0)) (Sum.inl 0) = 0) (h2 : M (Sum.inr (Sum.inr 0)) (Sum.inl 0) = 0)
    (h3 : M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl 0)) = 0) (h4 : M (Sum.inl 0) (Sum.inl 0) = 0)
    (h5 : M (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)) = 0)
    (h6 : M (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) = 0) : M ^ 3 = 0 := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    obtain rfl := Fin.fin_one_eq_zero i <;> obtain rfl := Fin.fin_one_eq_zero j <;>
    simp [pow_succ, Matrix.mul_apply, Fintype.sum_sum_type, h1, h2, h3, h4, h5, h6]

theorem u3_hc : ∀ c : K, c ^ (2 * 1 + 1) = 1 → ((2 * 1 + 1 : ℕ) : K) * (1 - c) = 0 → c = 1 := by
  intro c hc3 hmul
  have hc3' : c ^ 3 = 1 := by simpa using hc3
  have hmul' : (3 : K) * (1 - c) = 0 := by simpa using hmul
  by_cases h3 : (3 : K) = 0
  · have h0 : (c - 1) ^ 3 = 0 := by linear_combination hc3' - (c * (c - 1)) * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  · rcases mul_eq_zero.mp hmul' with h | h
    · exact absurd h h3
    · exact (sub_eq_zero.mp h).symm

theorem radFixPow_u3 [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (h : UnitaryFieldData p f K) :
    RadFixPow (r := 1) (ε := 1) (d := 1) h le_rfl le_rfl := by
  classical
  intro b hb
  obtain ⟨x, rfl⟩ := semilinearAutHom_surjective h (le_refl 1) (le_refl 1) hp2 (by norm_num) b
  set A : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
    ((x : SemiGL (HypIndex 1 1) K).left : Matrix (HypIndex 1 1) (HypIndex 1 1) K) with hA
  set σ := (x : SemiGL (HypIndex 1 1) K).right with hσ
  have hcomm : ∀ (a b0 : K) (_ : h.norm a + h.trace b0 = 0),
      A * (u3N h a b0).map σ = u3N h a b0 * A := by
    intro a b0 hab
    have hg := rkOneQElt_mem_unRad h hab
    have := comm_of_fix h (le_refl 1) (le_refl 1) (le_refl 1) u3_hc x hg (hb _ hg)
    rwa [coe_rkOneQElt, rkOneQ_eq_one_add, add_sub_cancel_left] at this
  obtain ⟨b1, hb1⟩ := exists_norm_add_trace_eq_zero h 1
  have hc1 := hcomm 1 b1 hb1
  have hbar1 : h.bar 1 = 1 := map_one _
  have hfe : A (Sum.inr (Sum.inr 0)) (Sum.inl 0) = 0 := by
    simpa using u3_ze h A σ 1 b1 hc1
  have hze : A (Sum.inr (Sum.inl 0)) (Sum.inl 0) = 0 := by
    have := u3_ee h A σ 1 b1 hc1
    rw [hbar1, hfe] at this
    simpa using this
  have hfz : A (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl 0)) = 0 := by
    have := u3_zz h A σ 1 b1 hc1
    rw [hbar1, hze] at this
    simpa using this.symm
  have hzf : A (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)) =
      A (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0)) := by
    have := u3_zf h A σ 1 b1 hc1
    rw [hze] at this
    simpa using this
  have hez : A (Sum.inl 0) (Sum.inl 0) = A (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inl 0)) := by
    have := u3_ez h A σ 1 b1 hc1
    rw [hbar1, hfz] at this
    simpa using this
  have hA'A : (((x : SemiGL (HypIndex 1 1) K).left⁻¹ : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K) * A = 1 := Units.inv_mul _
  have ha0 : A (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
    intro h0
    have := congrFun (congrFun hA'A (Sum.inl 0)) (Sum.inl 0)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hfe, hze, h0] at this
  have hσid : σ = RingEquiv.refl K := by
    ext c
    obtain ⟨b2, hb2⟩ := exists_norm_add_trace_eq_zero h (h.bar c)
    have := u3_ez h A σ (h.bar c) b2 (hcomm _ b2 hb2)
    rw [h.bar_bar, hfz, ← hez] at this
    have h2 : A (Sum.inl 0) (Sum.inl 0) * (σ c - c) = 0 := by
      linear_combination -this
    rcases mul_eq_zero.mp h2 with h0 | h0
    · exact absurd h0 ha0
    · exact sub_eq_zero.mp h0
  set a0 := A (Sum.inl 0) (Sum.inl 0) with ha0def
  have hp3 : 3 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hM3 : (A - a0 • (1 : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) ^ 3 = 0 := by
    apply u3_cube_zero
    · simp [hze]
    · simp [hfe]
    · simp [hfz]
    · simp [ha0def]
    · simp [← hez, ha0def]
    · simp [← hzf, ← hez, ha0def]
  have hcom : Commute (a0 • (1 : Matrix (HypIndex 1 1) (HypIndex 1 1) K))
      (A - a0 • 1) := Commute.smul_left (Commute.one_left _) a0
  have hpow : A ^ p = (a0 ^ p) • (1 : Matrix (HypIndex 1 1) (HypIndex 1 1) K) := by
    calc A ^ p = (a0 • 1 + (A - a0 • 1)) ^ p := by rw [add_sub_cancel]
      _ = (a0 • 1) ^ p + (A - a0 • 1) ^ p := add_pow_char_of_commute p hcom
      _ = a0 ^ p • 1 := by rw [smul_pow, one_pow, pow_eq_zero_of_le hp3 hM3, add_zero]
  refine semilinearAutHom_pow_eq_one h (le_refl 1) (le_refl 1) (by norm_num) x p hσid (a0 ^ p)
    (pow_ne_zero p ha0) ?_
  rw [Units.val_pow_eq_pow_val]
  exact hpow

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
