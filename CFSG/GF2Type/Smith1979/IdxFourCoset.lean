module

public import CFSG.LargeExtraspecial.S3Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial

variable {G : Type} [Group G] [Finite G] (T : Setting G)

theorem zmod2_cases'' (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ b = a := by
  revert a b; decide

theorem sq_mul_eq_one_iff {r v : G} (hrQ : r ∈ T.QG) (hvQ : v ∈ T.QG) (hv : v ^ 2 = 1) :
    (r * v) ^ 2 = 1 ↔ polar T.q (T.cl r) (T.cl v) = T.q (T.cl r) := by
  rw [← T.q_cl_eq_zero_iff (T.QG.mul_mem hrQ hvQ), T.cl_mul hrQ hvQ,
    QuadraticMap.map_add (⇑T.q) (T.cl r) (T.cl v), (T.q_cl_eq_zero_iff hvQ).mpr hv, add_zero,
    zmod2_add_eq_zero_iff]

theorem clSub_le_orthogonal {V : Subgroup G} (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) :
    T.clSub V ≤ LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub V) := by
  intro v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  obtain ⟨x, hxV, hxQ, rfl⟩ := T.mem_clSub_iff.mp hv
  obtain ⟨y, hyV, hyQ, rfl⟩ := T.mem_clSub_iff.mp hw
  change T.q.polarBilin (T.cl y) (T.cl x) = 0
  rw [polarBilin_apply_apply]
  exact (T.polar_cl_eq_zero_iff hyQ hxQ).mpr (hab y hyV x hxV)

theorem orthogonal_clSub_eq {V : Subgroup G} (hVQ : V ≤ T.QG) (hzV : T.z ∈ V)
    (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hcard : Nat.card V = 2 ^ (T.width + 1)) :
    LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub V) = T.clSub V := by
  have hfin : finrank (ZMod 2) (T.clSub V) = T.width := by
    have h1 : Nat.card V = 2 * 2 ^ finrank (ZMod 2) (T.clSub V) := by
      rw [← T.card_submodule, ← T.card_clPre, T.clPre_clSub hVQ hzV]
    rw [hcard, pow_succ, mul_comm] at h1
    exact (Nat.pow_right_injective le_rfl (Nat.eq_of_mul_eq_mul_left (by norm_num) h1)).symm
  refine (Submodule.eq_of_le_of_finrank_eq (clSub_le_orthogonal T hab) ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate, T.finrank_Qt_eq_two_mul_width, hfin]
  omega

theorem card_sq_eq_one_coset {V : Subgroup G} (hVQ : V ≤ T.QG) (hzV : T.z ∈ V)
    (hab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hsq : ∀ x ∈ V, x ^ 2 = 1)
    (hcard : Nat.card V = 2 ^ (T.width + 1)) {r : G} (hrQ : r ∈ T.QG) (hrV : r ∉ V) :
    Nat.card {v : V // (r * v) ^ 2 = 1} = 2 ^ T.width := by
  classical
  set φ : V → ZMod 2 := fun v => polar T.q (T.cl r) (T.cl (v : G)) with hφ
  have hφmul : ∀ v w : V, φ (v * w) = φ v + φ w := fun v w => by
    simp only [hφ, Subgroup.coe_mul, T.cl_mul (hVQ v.2) (hVQ w.2), polar_add_right]
  obtain ⟨v₁, hv₁⟩ : ∃ v : V, φ v = 1 := by
    by_contra hno
    push Not at hno
    apply hrV
    have hrO : T.cl r ∈ LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub V) := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro w hw
      obtain ⟨x, hxV, hxQ, rfl⟩ := T.mem_clSub_iff.mp hw
      change T.q.polarBilin (T.cl x) (T.cl r) = 0
      rw [polarBilin_apply_apply, QuadraticMap.polar_comm]
      rcases zmod2_cases'' (polar T.q (T.cl r) (T.cl x)) with h | h
      · exact h
      · exact absurd h (hno ⟨x, hxV⟩)
    rw [orthogonal_clSub_eq T hVQ hzV hab hcard] at hrO
    have : r ∈ T.clPre (T.clSub V) := ⟨hrQ, hrO⟩
    rwa [T.clPre_clSub hVQ hzV] at this
  have hfib : ∀ c : ZMod 2, Nat.card {v : V // φ v = c} = Nat.card {v : V // φ v = c + 1} := by
    intro c
    refine Nat.card_congr
      { toFun := fun v => ⟨v.1 * v₁, by rw [hφmul, v.2, hv₁]⟩
        invFun := fun v => ⟨v.1 * v₁⁻¹, ?_⟩
        left_inv := fun v => by simp
        right_inv := fun v => by simp }
    have h1 : φ (v.1 * v₁⁻¹) + φ v₁ = φ v.1 := by
      rw [← hφmul, inv_mul_cancel_right]
    rw [v.2, hv₁] at h1
    rcases zmod2_cases'' (φ (v.1 * v₁⁻¹)) with h | h <;> rcases zmod2_cases'' c with hc | hc <;>
      simp_all <;> revert h1 <;> decide
  have htot : Nat.card {v : V // φ v = T.q (T.cl r)} +
      Nat.card {v : V // φ v = T.q (T.cl r) + 1} = Nat.card V := by
    have hc : ∀ v : V, φ v = T.q (T.cl r) + 1 ↔ ¬ φ v = T.q (T.cl r) := fun v => by
      rcases zmod2_cases'' (φ v) with h1 | h1 <;> rcases zmod2_cases'' (T.q (T.cl r)) with h2 | h2 <;>
        rw [h1, h2] <;> decide
    rw [Nat.card_congr (Equiv.subtypeEquivRight hc), ← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl (fun v : V => φ v = T.q (T.cl r)))
  have hequiv : Nat.card {v : V // (r * v) ^ 2 = 1} = Nat.card {v : V // φ v = T.q (T.cl r)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      sq_mul_eq_one_iff T hrQ (hVQ v.2) (hsq v v.2))
  rw [hequiv]
  rw [← hfib (T.q (T.cl r)), hcard, pow_succ] at htot
  omega

end CFSG.GF2Type.Smith1979.IdxFour
