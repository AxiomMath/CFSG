module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LBID4

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

section Polar

variable (Q : QuadraticForm K V)

theorem q_add (x y : V) : Q (x + y) = Q x + Q y + polar Q x y := by
  rw [polar]; ring

theorem q_sub (x y : V) : Q (x - y) = Q x + Q y - polar Q x y := by
  rw [sub_eq_add_neg, q_add, QuadraticMap.map_neg, polar_neg_right]; ring

theorem q_smul (a : K) (x : V) : Q (a • x) = a ^ 2 * Q x := by
  rw [QuadraticMap.map_smul, smul_eq_mul, pow_two]

theorem polar_self_eq (x : V) : polar Q x x = 2 * Q x := by
  rw [QuadraticMap.polar_self, two_nsmul, two_mul]

@[expose] noncomputable def pol (b : V) : V →ₗ[K] K := (polarBilin Q).flip b

@[simp] theorem pol_apply (b v : V) : pol Q b v = polar Q v b := by
  simp [pol, polarBilin_apply_apply]

end Polar

structure EFrame (Q : QuadraticForm K V) where
  b : V
  b' : V
  c : K
  c_ne : c ≠ 0
  q_b : Q b = c
  q_b' : Q b' = c
  polar_bb' : polar Q b b' = -c

namespace EFrame

variable {Q : QuadraticForm K V} (F : EFrame Q)

theorem polar_bb : polar Q F.b F.b = 2 * F.c := by rw [polar_self_eq, F.q_b]

theorem polar_b'b' : polar Q F.b' F.b' = 2 * F.c := by rw [polar_self_eq, F.q_b']

theorem polar_b'b : polar Q F.b' F.b = -F.c := by rw [polar_comm, F.polar_bb']

theorem q_sub_sub (v : V) (l m : K) :
    Q (v - l • F.b - m • F.b') =
      Q v + F.c * (l ^ 2 - l * m + m ^ 2) - l * polar Q v F.b - m * polar Q v F.b' := by
  simp only [q_sub, q_smul, F.q_b, F.q_b', polar_sub_left, polar_smul_left, polar_smul_right,
    F.polar_bb', smul_eq_mul]
  ring

@[expose] def Orth (v : V) : Prop := polar Q v F.b = 0 ∧ polar Q v F.b' = 0

variable {F} in
theorem Orth.add {v w : V} (hv : F.Orth v) (hw : F.Orth w) : F.Orth (v + w) :=
  ⟨by rw [polar_add_left, hv.1, hw.1, add_zero], by rw [polar_add_left, hv.2, hw.2, add_zero]⟩

variable {F} in
theorem Orth.smul {v : V} (hv : F.Orth v) (a : K) : F.Orth (a • v) :=
  ⟨by rw [polar_smul_left, hv.1, smul_zero], by rw [polar_smul_left, hv.2, smul_zero]⟩

variable {F} in
theorem Orth.sub {v w : V} (hv : F.Orth v) (hw : F.Orth w) : F.Orth (v - w) :=
  ⟨by rw [polar_sub_left, hv.1, hw.1, sub_zero], by rw [polar_sub_left, hv.2, hw.2, sub_zero]⟩

@[expose] noncomputable def rotL : V →ₗ[K] V :=
  LinearMap.id - (F.c⁻¹ • (pol Q F.b + pol Q F.b')).smulRight F.b -
    (F.c⁻¹ • pol Q F.b').smulRight F.b'

theorem rotL_apply (v : V) : F.rotL v =
    v - (F.c⁻¹ * (polar Q v F.b + polar Q v F.b')) • F.b - (F.c⁻¹ * polar Q v F.b') • F.b' := by
  simp only [rotL, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.add_apply, pol_apply, smul_eq_mul]

theorem rotL_b : F.rotL F.b = F.b' := by
  have hc := F.c_ne
  rw [rotL_apply, F.polar_bb, F.polar_bb',
    show F.c⁻¹ * (2 * F.c + -F.c) = 1 by field_simp; ring,
    show F.c⁻¹ * -F.c = -1 by field_simp]
  module

theorem rotL_b' : F.rotL F.b' = -F.b - F.b' := by
  have hc := F.c_ne
  rw [rotL_apply, F.polar_b'b, F.polar_b'b',
    show F.c⁻¹ * (-F.c + 2 * F.c) = 1 by field_simp; ring,
    show F.c⁻¹ * (2 * F.c) = 2 by field_simp]
  module

theorem rotL_of_orth {v : V} (hv : F.Orth v) : F.rotL v = v := by
  rw [rotL_apply, hv.1, hv.2]
  simp

theorem rotL_eq_add (v : V) : ∃ α β : K, F.rotL v = v + α • F.b + β • F.b' :=
  ⟨-(F.c⁻¹ * (polar Q v F.b + polar Q v F.b')), -(F.c⁻¹ * polar Q v F.b'), by
    rw [rotL_apply]; simp only [neg_smul]; abel⟩

theorem rotL_cube (v : V) : F.rotL (F.rotL (F.rotL v)) = v := by
  obtain ⟨α, β, h⟩ := F.rotL_eq_add v
  have h2 : F.rotL (F.rotL v) = v + (α - β) • F.b + α • F.b' := by
    rw [h, map_add, map_add, map_smul, map_smul, h, F.rotL_b, F.rotL_b']
    module
  rw [h2, map_add, map_add, map_smul, map_smul, h, F.rotL_b, F.rotL_b']
  module

theorem q_rotL (v : V) : Q (F.rotL v) = Q v := by
  have hc := F.c_ne
  rw [rotL_apply, q_sub_sub]
  field_simp
  ring

theorem polar_rotL_of_orth {x : V} (hx : F.Orth x) (v : V) :
    polar Q (F.rotL v) x = polar Q v x := by
  have h1 : polar Q F.b x = 0 := by rw [polar_comm]; exact hx.1
  have h2 : polar Q F.b' x = 0 := by rw [polar_comm]; exact hx.2
  rw [rotL_apply, polar_sub_left, polar_sub_left, polar_smul_left, polar_smul_left, h1, h2]
  simp

@[expose] noncomputable def rot : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap F.rotL (F.rotL ∘ₗ F.rotL) (LinearMap.ext fun v => F.rotL_cube v)
    (LinearMap.ext fun v => F.rotL_cube v)

theorem rot_apply (v : V) : F.rot v = F.rotL v := rfl

theorem rot_mem : F.rot ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => F.q_rotL v

theorem rot_pow_three : F.rot ^ 3 = 1 := by
  ext v
  rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply, rot_apply, rot_apply, rot_apply,
    rotL_cube]
  rfl

@[expose] def Perp (G : EFrame Q) : Prop := F.Orth G.b ∧ F.Orth G.b'

theorem Perp.symm {G : EFrame Q} (h : F.Perp G) : G.Perp F :=
  ⟨⟨by rw [polar_comm]; exact h.1.1, by rw [polar_comm]; exact h.2.1⟩,
    ⟨by rw [polar_comm]; exact h.1.2, by rw [polar_comm]; exact h.2.2⟩⟩

theorem rotL_comm {G : EFrame Q} (h : F.Perp G) (v : V) :
    F.rotL (G.rotL v) = G.rotL (F.rotL v) := by
  have h' := h.symm
  rw [F.rotL_apply (G.rotL v), G.rotL_apply (F.rotL v), G.polar_rotL_of_orth h'.1,
    G.polar_rotL_of_orth h'.2, F.polar_rotL_of_orth h.1, F.polar_rotL_of_orth h.2,
    F.rotL_apply, G.rotL_apply]
  abel

theorem rot_comm {G : EFrame Q} (h : F.Perp G) : F.rot * G.rot = G.rot * F.rot := by
  ext v
  exact F.rotL_comm h v

theorem rot_pow_of_orth {v : V} (hv : F.Orth v) (n : ℕ) : (F.rot ^ n) v = v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, rot_apply, F.rotL_of_orth hv, ih]

theorem orth_rotL {G : EFrame Q} (h : F.Perp G) {v : V} (hv : G.Orth v) : G.Orth (F.rotL v) := by
  have h1 : G.Orth F.b := h.symm.1
  have h2 : G.Orth F.b' := h.symm.2
  rw [rotL_apply]
  exact ((hv.sub (h1.smul _)).sub (h2.smul _))

theorem orth_rot_pow {G : EFrame Q} (h : F.Perp G) {v : V} (hv : G.Orth v) (n : ℕ) :
    G.Orth ((F.rot ^ n) v) := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, rot_apply]; exact F.orth_rotL h ih

@[expose] noncomputable def proj : V →ₗ[K] V :=
  ((3 * F.c)⁻¹ • ((2 : K) • pol Q F.b + pol Q F.b')).smulRight F.b +
    ((3 * F.c)⁻¹ • (pol Q F.b + (2 : K) • pol Q F.b')).smulRight F.b'

theorem proj_apply (v : V) : F.proj v =
    ((3 * F.c)⁻¹ * (2 * polar Q v F.b + polar Q v F.b')) • F.b +
      ((3 * F.c)⁻¹ * (polar Q v F.b + 2 * polar Q v F.b')) • F.b' := by
  simp only [proj, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
    pol_apply, smul_eq_mul]

theorem proj_of_orth {v : V} (hv : F.Orth v) : F.proj v = 0 := by
  rw [proj_apply, hv.1, hv.2]
  simp

variable (h3 : (3 : K) ≠ 0)
include h3

theorem orth_sub_proj (v : V) : F.Orth (v - F.proj v) := by
  have hc := F.c_ne
  constructor
  · rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, F.polar_bb,
      F.polar_b'b, smul_eq_mul, smul_eq_mul]
    field_simp
    ring
  · rw [proj_apply, polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left, F.polar_bb',
      F.polar_b'b', smul_eq_mul, smul_eq_mul]
    field_simp
    ring

theorem proj_b : F.proj F.b = F.b := by
  have hc := F.c_ne
  rw [proj_apply, F.polar_bb, F.polar_bb',
    show (3 * F.c)⁻¹ * (2 * (2 * F.c) + -F.c) = 1 by field_simp; ring,
    show (3 * F.c)⁻¹ * (2 * F.c + 2 * -F.c) = 0 by ring]
  simp

theorem proj_b' : F.proj F.b' = F.b' := by
  have hc := F.c_ne
  rw [proj_apply, F.polar_b'b, F.polar_b'b',
    show (3 * F.c)⁻¹ * (2 * -F.c + 2 * F.c) = 0 by ring,
    show (3 * F.c)⁻¹ * (-F.c + 2 * (2 * F.c)) = 1 by field_simp; ring]
  simp

theorem linearMap_ext {f h : V →ₗ[K] V} (hb : f F.b = h F.b) (hb' : f F.b' = h F.b')
    (horth : ∀ v, F.Orth v → f v = h v) : f = h := by
  ext v
  have e : v = F.proj v + (v - F.proj v) := by abel
  rw [e, map_add, map_add, horth _ (F.orth_sub_proj h3 v), proj_apply, map_add, map_add, map_smul,
    map_smul, map_smul, map_smul, hb, hb']

theorem b_ne_b' : F.b ≠ F.b' := by
  intro h
  have e := F.polar_bb'
  rw [← h, F.polar_bb] at e
  exact F.c_ne (by
    have : (3 : K) * F.c = 0 := by linear_combination e
    exact (mul_eq_zero.mp this).resolve_left h3)

theorem neg_b_sub_b'_ne : -F.b - F.b' ≠ F.b := by
  intro h
  have hb' : F.b' = (-2 : K) • F.b := by
    calc F.b' = -F.b - (-F.b - F.b') := by abel
      _ = (-2 : K) • F.b := by rw [h]; module
  have e := F.polar_bb'
  rw [hb', polar_smul_right, F.polar_bb, smul_eq_mul] at e
  exact F.c_ne (by
    have : (3 : K) * F.c = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left h3)

omit h3 in
@[expose] noncomputable def sigL : V →ₗ[K] V :=
  LinearMap.id + ((3 * F.c)⁻¹ • (pol Q F.b' - pol Q F.b)).smulRight (F.b - F.b')

omit h3 in
theorem sigL_apply (v : V) : F.sigL v =
    v + ((3 * F.c)⁻¹ * (polar Q v F.b' - polar Q v F.b)) • (F.b - F.b') := by
  simp only [sigL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, pol_apply, smul_eq_mul]

theorem sigL_b : F.sigL F.b = F.b' := by
  have hc := F.c_ne
  rw [sigL_apply, F.polar_bb', F.polar_bb,
    show (3 * F.c)⁻¹ * (-F.c - 2 * F.c) = -1 by field_simp; ring]
  module

theorem sigL_b' : F.sigL F.b' = F.b := by
  have hc := F.c_ne
  rw [sigL_apply, F.polar_b'b', F.polar_b'b,
    show (3 * F.c)⁻¹ * (2 * F.c - -F.c) = 1 by field_simp; ring]
  module

omit h3 in
theorem sigL_of_orth {v : V} (hv : F.Orth v) : F.sigL v = v := by
  rw [sigL_apply, hv.1, hv.2]
  simp

theorem sigL_sq (v : V) : F.sigL (F.sigL v) = v := by
  have h := F.sigL_apply v
  set κ := (3 * F.c)⁻¹ * (polar Q v F.b' - polar Q v F.b)
  rw [h, map_add, map_smul, map_sub, F.sigL_b h3, F.sigL_b' h3, h]
  module

theorem q_sigL (v : V) : Q (F.sigL v) = Q v := by
  have hc := F.c_ne
  rw [sigL_apply, q_add, q_smul, q_sub, F.q_b, F.q_b', F.polar_bb', polar_smul_right,
    polar_sub_right, smul_eq_mul]
  field_simp
  ring

theorem sigL_rotL_sigL (v : V) : F.sigL (F.rotL (F.sigL v)) = F.rotL (F.rotL v) := by
  have key : F.sigL ∘ₗ F.rotL ∘ₗ F.sigL = F.rotL ∘ₗ F.rotL := by
    refine F.linearMap_ext h3 ?_ ?_ ?_
    · simp only [LinearMap.comp_apply]
      rw [F.sigL_b h3, F.rotL_b', map_sub, map_neg, F.sigL_b h3, F.sigL_b' h3, F.rotL_b,
        F.rotL_b']
      abel
    · simp only [LinearMap.comp_apply]
      rw [F.sigL_b' h3, F.rotL_b, F.sigL_b' h3, F.rotL_b', map_sub, map_neg, F.rotL_b,
        F.rotL_b']
      abel
    · intro v hv
      simp only [LinearMap.comp_apply]
      rw [F.sigL_of_orth hv, F.rotL_of_orth hv, F.sigL_of_orth hv, F.rotL_of_orth hv]
  exact congrArg (fun f : V →ₗ[K] V => f v) key

@[expose] noncomputable def sig : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap F.sigL F.sigL (LinearMap.ext fun v => F.sigL_sq h3 v)
    (LinearMap.ext fun v => F.sigL_sq h3 v)

theorem sig_mem : F.sig h3 ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => F.q_sigL h3 v

open scoped commutatorElement in
theorem rot_mem_commutator :
    F.rot ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hσσ : F.sig h3 * F.sig h3 = 1 := by
    ext v
    exact F.sigL_sq h3 v
  have hσinv : (F.sig h3)⁻¹ = F.sig h3 := inv_eq_of_mul_eq_one_right hσσ
  have hconj : F.sig h3 * F.rot * F.sig h3 = F.rot * F.rot := by
    ext v
    exact F.sigL_rotL_sigL h3 v
  have hc : ⁅F.sig h3, F.rot⁆ = F.rot := by
    calc ⁅F.sig h3, F.rot⁆ = F.sig h3 * F.rot * (F.sig h3)⁻¹ * F.rot⁻¹ :=
          commutatorElement_def _ _
      _ = F.sig h3 * F.rot * F.sig h3 * F.rot⁻¹ := by rw [hσinv]
      _ = F.rot * F.rot * F.rot⁻¹ := by rw [hconj]
      _ = F.rot := by group
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (F.sig_mem h3) F.rot_mem

end EFrame

end CFSG.HardMathSupport.Solomon.Coordinator.LBID4
