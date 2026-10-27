module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical

public section

namespace CFSG.SeitzReduction

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace UnitaryShear

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ} (h : UnitaryFieldData p f K)
  (G : Matrix (Fin n) (Fin n) K)

theorem matrix_ext_mulVec {M M' : Matrix (Fin n) (Fin n) K} (hMM' : ∀ v, M *ᵥ v = M' *ᵥ v) :
    M = M' := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_mulVec_eq_zero fun v => by rw [sub_mulVec, hMM', sub_self]

@[expose] noncomputable def quasiRefl (u : Fin n → K) (c : K) : Matrix (Fin n) (Fin n) K :=
  1 + ((c - 1) / gramForm h G u u) • vecMulVec u (gramRow h G u)

theorem quasiRefl_mulVec (u : Fin n → K) (c : K) (v : Fin n → K) :
    quasiRefl h G u c *ᵥ v = v + ((c - 1) / gramForm h G u u * gramForm h G u v) • u := by
  simp only [quasiRefl, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    gramRow_dotProduct, op_smul_eq_smul, smul_smul]

variable {h G}

theorem quasiRefl_mulVec_of_orth {u v : Fin n → K} (c : K) (huv : gramForm h G u v = 0) :
    quasiRefl h G u c *ᵥ v = v := by
  rw [quasiRefl_mulVec, huv, mul_zero, zero_smul, add_zero]

theorem quasiRefl_mulVec_self {u : Fin n → K} (hu : gramForm h G u u ≠ 0) (c : K) :
    quasiRefl h G u c *ᵥ u = c • u := by
  rw [quasiRefl_mulVec, div_mul_cancel₀ _ hu, sub_smul, one_smul, add_sub_cancel]

theorem quasiRefl_one (u : Fin n → K) : quasiRefl h G u 1 = 1 := by
  rw [quasiRefl, sub_self, zero_div, zero_smul, add_zero]

theorem quasiRefl_mul_quasiRefl {u : Fin n → K} (hu : gramForm h G u u ≠ 0) (c c' : K) :
    quasiRefl h G u c * quasiRefl h G u c' = quasiRefl h G u (c * c') := by
  refine matrix_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, quasiRefl_mulVec, quasiRefl_mulVec, quasiRefl_mulVec, map_add, map_smul,
    smul_eq_mul]
  have key : (c - 1) / gramForm h G u u * (gramForm h G u v +
      (c' - 1) / gramForm h G u u * gramForm h G u v * gramForm h G u u) +
      (c' - 1) / gramForm h G u u * gramForm h G u v =
      (c * c' - 1) / gramForm h G u u * gramForm h G u v := by
    field_simp
    ring
  rw [← key, add_smul]
  abel

theorem quasiRefl_pow {u : Fin n → K} (hu : gramForm h G u u ≠ 0) (c : K) (k : ℕ) :
    quasiRefl h G u c ^ k = quasiRefl h G u (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, quasiRefl_one]
  | succ k ih => rw [pow_succ, ih, quasiRefl_mul_quasiRefl hu, pow_succ]

theorem quasiRefl_isometry (hH : (gramForm h G).IsSymm) {u : Fin n → K}
    (hu : gramForm h G u u ≠ 0) {c : K} (hc : h.norm c = 1) (x y : Fin n → K) :
    gramForm h G (quasiRefl h G u c *ᵥ x) (quasiRefl h G u c *ᵥ y) = gramForm h G x y := by
  set d := gramForm h G u u with hd
  have hdσ : h.bar d = d := hH.eq u u
  have hxu : gramForm h G x u = h.bar (gramForm h G u x) := (hH.eq u x).symm
  have ha : (c - 1) / d + h.bar ((c - 1) / d) + h.bar ((c - 1) / d) * ((c - 1) / d) * d = 0 := by
    rw [map_div₀, hdσ, map_sub, map_one]
    have hc' : c * h.bar c = 1 := hc
    field_simp
    linear_combination hc'
  rw [quasiRefl_mulVec, quasiRefl_mulVec]
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, hxu, map_mul, ← hd]
  linear_combination (gramForm h G u y * h.bar (gramForm h G u x)) * ha

theorem det_quasiRefl {u : Fin n → K} (hu : gramForm h G u u ≠ 0) (c : K) :
    (quasiRefl h G u c).det = c := by
  rw [quasiRefl, ← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, gramRow_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hu, add_sub_cancel]

theorem quasiRefl_mul_comm (hH : (gramForm h G).IsSymm) {u u' : Fin n → K}
    (huu' : gramForm h G u u' = 0) (c c' : K) :
    quasiRefl h G u c * quasiRefl h G u' c' = quasiRefl h G u' c' * quasiRefl h G u c := by
  have hu'u : gramForm h G u' u = 0 := by rw [← hH.eq u u', huu', map_zero]
  refine matrix_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, quasiRefl_mulVec, quasiRefl_mulVec, quasiRefl_mulVec,
    quasiRefl_mulVec]
  simp only [map_add, map_smul, huu', hu'u, smul_eq_mul, mul_zero, add_zero]
  abel

theorem mul_quasiRefl {g : Matrix (Fin n) (Fin n) K}
    (hg : ∀ x y, gramForm h G (g *ᵥ x) (g *ᵥ y) = gramForm h G x y) (u : Fin n → K) (c : K) :
    g * quasiRefl h G u c = quasiRefl h G (g *ᵥ u) c * g := by
  refine matrix_ext_mulVec fun v => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec, quasiRefl_mulVec, quasiRefl_mulVec, mulVec_add,
    mulVec_smul, hg, hg]

end UnitaryShear

end CFSG.SeitzReduction
