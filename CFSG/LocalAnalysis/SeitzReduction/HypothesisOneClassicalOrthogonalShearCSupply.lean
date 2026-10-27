module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearSiegel
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Tactic.Module
import Mathlib.Tactic.ReduceModChar
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalShearQuadratic

public section

namespace CFSG.SeitzReduction

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

namespace OrthogonalShearC

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local macro "char_two_module" : tactic =>
  `(tactic| (match_scalars <;> (try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;>
    (try ring_nf) <;> (try reduce_mod_char!) <;> (try ring_nf)))

local macro "char_two_ring" : tactic =>
  `(tactic| ((try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;>
    (try ring_nf) <;> (try reduce_mod_char!) <;> (try ring_nf)))

@[expose] def ofCube (f : V →ₗ[K] V) (h : ∀ x, f (f (f x)) = x) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap f (f ∘ₗ f) (LinearMap.ext h) (LinearMap.ext h)

theorem ofCube_apply (f : V →ₗ[K] V) (h : ∀ x, f (f (f x)) = x) (x : V) :
    ofCube f h x = f x :=
  rfl

theorem ofCube_pow_three (f : V →ₗ[K] V) (h : ∀ x, f (f (f x)) = x) : ofCube f h ^ 3 = 1 := by
  ext x
  rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact h x

theorem odd_orderOf_of_pow_three {G : Type*} [Monoid G] {g : G} (h : g ^ 3 = 1) :
    Odd (orderOf g) :=
  (by decide : Odd 3).of_dvd_nat (orderOf_dvd_of_pow_eq_one h)

theorem ofCube_mem_orthogonalGroup {Q : QuadraticForm K V} (f : V →ₗ[K] V)
    (h : ∀ x, f (f (f x)) = x) (hQ : ∀ x, Q (f x) = Q x) :
    ofCube f h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hQ

@[expose] def rotLin (Q : QuadraticForm K V) (p₁ p₂ : V) : V →ₗ[K] V :=
  LinearMap.id + ((polarBilin Q).flip p₂).smulRight (p₁ + p₂) +
    ((polarBilin Q).flip p₁).smulRight p₁

theorem rotLin_apply (Q : QuadraticForm K V) (p₁ p₂ x : V) :
    rotLin Q p₁ p₂ x = x + polar Q x p₂ • (p₁ + p₂) + polar Q x p₁ • p₁ :=
  rfl

@[expose] def IsRotPair (Q : QuadraticForm K V) (p₁ p₂ : V) : Prop :=
  Q p₁ = 1 ∧ Q p₂ = 1 ∧ polar Q p₁ p₂ = 1

variable [CharP K 2]

theorem polar_self_charTwo (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

section Rot

variable {Q : QuadraticForm K V} {p₁ p₂ : V}

theorem polar_rotLin_left₁ (h : IsRotPair Q p₁ p₂) (x : V) :
    polar Q (rotLin Q p₁ p₂ x) p₁ = polar Q x p₁ + polar Q x p₂ := by
  obtain ⟨-, -, h12⟩ := h
  rw [rotLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_add_left, polar_self_charTwo, polar_comm Q p₂ p₁, h12, smul_eq_mul, smul_eq_mul]
  ring

theorem polar_rotLin_left₂ (h : IsRotPair Q p₁ p₂) (x : V) :
    polar Q (rotLin Q p₁ p₂ x) p₂ = polar Q x p₁ := by
  obtain ⟨-, -, h12⟩ := h
  rw [rotLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_add_left, polar_self_charTwo, h12, smul_eq_mul, smul_eq_mul]
  char_two_ring

theorem rotLin_cube (h : IsRotPair Q p₁ p₂) (x : V) :
    rotLin Q p₁ p₂ (rotLin Q p₁ p₂ (rotLin Q p₁ p₂ x)) = x := by
  have h1 := polar_rotLin_left₁ h x
  have h2 := polar_rotLin_left₂ h x
  have h3 : polar Q (rotLin Q p₁ p₂ (rotLin Q p₁ p₂ x)) p₁ = polar Q x p₂ := by
    rw [polar_rotLin_left₁ h, h1, h2]
    char_two_ring
  have h4 : polar Q (rotLin Q p₁ p₂ (rotLin Q p₁ p₂ x)) p₂ = polar Q x p₁ + polar Q x p₂ := by
    rw [polar_rotLin_left₂ h, h1]
  rw [rotLin_apply _ _ _ (rotLin Q p₁ p₂ (rotLin Q p₁ p₂ x)), h3, h4,
    rotLin_apply _ _ _ (rotLin Q p₁ p₂ x), h1, h2, rotLin_apply]
  char_two_module

theorem map_rotLin (h : IsRotPair Q p₁ p₂) (x : V) : Q (rotLin Q p₁ p₂ x) = Q x := by
  obtain ⟨hp₁, hp₂, h12⟩ := h
  have e : rotLin Q p₁ p₂ x = x + ((polar Q x p₁ + polar Q x p₂) • p₁ + polar Q x p₂ • p₂) := by
    rw [rotLin_apply]
    module
  rw [e, QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul,
    QuadraticMap.map_smul, hp₁, hp₂, polar_add_right, polar_smul_right, polar_smul_right,
    polar_smul_left, polar_smul_right, h12, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  char_two_ring

theorem rotLin_apply_right (h : IsRotPair Q p₁ p₂) : rotLin Q p₁ p₂ p₂ = p₁ + p₂ := by
  obtain ⟨-, -, h12⟩ := h
  rw [rotLin_apply, polar_self_charTwo, polar_comm, h12, zero_smul, add_zero, one_smul,
    add_comm]

omit [CharP K 2] in
theorem rotLin_apply_of_polar_eq_zero {x : V} (h₁ : polar Q x p₁ = 0) (h₂ : polar Q x p₂ = 0) :
    rotLin Q p₁ p₂ x = x := by
  rw [rotLin_apply, h₁, h₂, zero_smul, zero_smul, add_zero, add_zero]

omit [CharP K 2] in
theorem rotLin_comm {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg₁ : g p₁ = p₁) (hg₂ : g p₂ = p₂) (x : V) : g (rotLin Q p₁ p₂ x) = rotLin Q p₁ p₂ (g x) := by
  rw [rotLin_apply, rotLin_apply, map_add, map_add, map_smul, map_smul, map_add, hg₁, hg₂,
    ← polar_map_of_mem hg x p₁, ← polar_map_of_mem hg x p₂, hg₁, hg₂]

@[expose] def rot (h : IsRotPair Q p₁ p₂) : V ≃ₗ[K] V :=
  ofCube (rotLin Q p₁ p₂) (rotLin_cube h)

theorem rot_apply (h : IsRotPair Q p₁ p₂) (x : V) : rot h x = rotLin Q p₁ p₂ x :=
  rfl

theorem rot_mem_orthogonalGroup (h : IsRotPair Q p₁ p₂) :
    rot h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  ofCube_mem_orthogonalGroup _ _ (map_rotLin h)

theorem rot_pow_three (h : IsRotPair Q p₁ p₂) : rot h ^ 3 = 1 :=
  ofCube_pow_three _ _

theorem rot_mul_comm {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h : IsRotPair Q p₁ p₂) (hg₁ : g p₁ = p₁) (hg₂ : g p₂ = p₂) : rot h * g = g * rot h :=
  LinearEquiv.ext fun x => (rotLin_comm hg hg₁ hg₂ x).symm

end Rot

@[expose] def wLeviLin (Q : QuadraticForm K V) (w₁ w₂ w₁' w₂' : V) : V →ₗ[K] V :=
  LinearMap.id + ((polarBilin Q).flip w₁').smulRight (w₁ + w₂) +
    ((polarBilin Q).flip w₂').smulRight w₁ + ((polarBilin Q).flip w₁).smulRight w₂' +
    ((polarBilin Q).flip w₂).smulRight (w₁' + w₂')

omit [CharP K 2] in
theorem wLeviLin_apply (Q : QuadraticForm K V) (w₁ w₂ w₁' w₂' x : V) :
    wLeviLin Q w₁ w₂ w₁' w₂' x = x + polar Q x w₁' • (w₁ + w₂) + polar Q x w₂' • w₁ +
      polar Q x w₁ • w₂' + polar Q x w₂ • (w₁' + w₂') :=
  rfl

@[expose] def IsHypFrame (Q : QuadraticForm K V) (w₁ w₂ w₁' w₂' : V) : Prop :=
  Q w₁ = 0 ∧ Q w₂ = 0 ∧ Q w₁' = 0 ∧ Q w₂' = 0 ∧ polar Q w₁ w₂ = 0 ∧ polar Q w₁' w₂' = 0 ∧
    polar Q w₁ w₁' = 1 ∧ polar Q w₂ w₂' = 1 ∧ polar Q w₁ w₂' = 0 ∧ polar Q w₂ w₁' = 0

section WLevi

variable {Q : QuadraticForm K V} {w₁ w₂ w₁' w₂' : V}

theorem polar_wLeviLin (h : IsHypFrame Q w₁ w₂ w₁' w₂') (x : V) :
    polar Q (wLeviLin Q w₁ w₂ w₁' w₂' x) w₁' = polar Q x w₂' ∧
      polar Q (wLeviLin Q w₁ w₂ w₁' w₂' x) w₂' = polar Q x w₁' + polar Q x w₂' ∧
      polar Q (wLeviLin Q w₁ w₂ w₁' w₂' x) w₁ = polar Q x w₁ + polar Q x w₂ ∧
      polar Q (wLeviLin Q w₁ w₂ w₁' w₂' x) w₂ = polar Q x w₁ := by
  obtain ⟨hq₁, hq₂, hq₁', hq₂', h12, h12', h11, h22, h12x, h21x⟩ := h
  have s₁ := polar_self_charTwo Q w₁
  have s₂ := polar_self_charTwo Q w₂
  have s₁' := polar_self_charTwo Q w₁'
  have s₂' := polar_self_charTwo Q w₂'
  simp only [wLeviLin_apply, polar_add_left, polar_smul_left, smul_eq_mul]
  rw [polar_comm Q w₂ w₁, polar_comm Q w₂' w₁', polar_comm Q w₁' w₁, polar_comm Q w₂' w₂,
    polar_comm Q w₂' w₁, polar_comm Q w₁' w₂]
  simp only [s₁, s₂, s₁', s₂', h12, h12', h11, h22, h12x, h21x]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> char_two_ring

theorem wLeviLin_cube (h : IsHypFrame Q w₁ w₂ w₁' w₂') (x : V) :
    wLeviLin Q w₁ w₂ w₁' w₂' (wLeviLin Q w₁ w₂ w₁' w₂' (wLeviLin Q w₁ w₂ w₁' w₂' x)) = x := by
  obtain ⟨a1, a2, a3, a4⟩ := polar_wLeviLin h x
  obtain ⟨b1, b2, b3, b4⟩ := polar_wLeviLin h (wLeviLin Q w₁ w₂ w₁' w₂' x)
  rw [wLeviLin_apply _ _ _ _ _ (wLeviLin Q w₁ w₂ w₁' w₂' (wLeviLin Q w₁ w₂ w₁' w₂' x)), b1, b2,
    b3, b4, a1, a2, a3, a4, wLeviLin_apply _ _ _ _ _ (wLeviLin Q w₁ w₂ w₁' w₂' x), a1, a2, a3, a4,
    wLeviLin_apply]
  char_two_module

omit [CharP K 2] in
theorem map_hypFrame (h : IsHypFrame Q w₁ w₂ w₁' w₂') (c₁ c₂ c₃ c₄ : K) :
    Q (c₁ • w₁ + c₂ • w₂ + c₃ • w₁' + c₄ • w₂') = c₁ * c₃ + c₂ * c₄ := by
  obtain ⟨hq₁, hq₂, hq₁', hq₂', h12, h12', h11, h22, h12x, h21x⟩ := h
  simp only [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_add_left, polar_smul_left,
    polar_smul_right, smul_eq_mul, hq₁, hq₂, hq₁', hq₂', h12, h12', h11, h22, h12x, h21x]
  ring

theorem map_wLeviLin (h : IsHypFrame Q w₁ w₂ w₁' w₂') (x : V) :
    Q (wLeviLin Q w₁ w₂ w₁' w₂' x) = Q x := by
  have e : wLeviLin Q w₁ w₂ w₁' w₂' x =
      x + ((polar Q x w₁' + polar Q x w₂') • w₁ + polar Q x w₁' • w₂ + polar Q x w₂ • w₁' +
        (polar Q x w₁ + polar Q x w₂) • w₂') := by
    rw [wLeviLin_apply]
    module
  rw [e, QuadraticMap.map_add Q x, map_hypFrame h]
  simp only [polar_add_right, polar_smul_right, smul_eq_mul]
  char_two_ring

@[expose] def wLevi (h : IsHypFrame Q w₁ w₂ w₁' w₂') : V ≃ₗ[K] V :=
  ofCube (wLeviLin Q w₁ w₂ w₁' w₂') (wLeviLin_cube h)

theorem wLevi_apply (h : IsHypFrame Q w₁ w₂ w₁' w₂') (x : V) :
    wLevi h x = wLeviLin Q w₁ w₂ w₁' w₂' x :=
  rfl

theorem wLevi_mem_orthogonalGroup (h : IsHypFrame Q w₁ w₂ w₁' w₂') :
    wLevi h ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  ofCube_mem_orthogonalGroup _ _ (map_wLeviLin h)

theorem wLevi_pow_three (h : IsHypFrame Q w₁ w₂ w₁' w₂') : wLevi h ^ 3 = 1 :=
  ofCube_pow_three _ _

theorem wLeviLin_apply_w₁ (h : IsHypFrame Q w₁ w₂ w₁' w₂') :
    wLeviLin Q w₁ w₂ w₁' w₂' w₁ = w₂ := by
  obtain ⟨-, -, -, -, h12, -, h11, -, h12x, -⟩ := h
  rw [wLeviLin_apply, h11, h12x, polar_self_charTwo, h12]
  char_two_module

theorem wLeviLin_apply_w₂ (h : IsHypFrame Q w₁ w₂ w₁' w₂') :
    wLeviLin Q w₁ w₂ w₁' w₂' w₂ = w₁ + w₂ := by
  obtain ⟨-, -, -, -, h12, -, -, h22, -, h21x⟩ := h
  rw [wLeviLin_apply, h21x, h22, polar_self_charTwo, polar_comm, h12]
  char_two_module

omit [CharP K 2] in
theorem wLeviLin_comm_N {N : V →ₗ[K] V} (hNadj : ∀ x y, polar Q (N x) y = polar Q x (N y))
    (hN₁ : N w₁ = 0) (hN₂ : N w₂ = 0) (hN₁' : N w₁' = w₂) (hN₂' : N w₂' = w₁) (x : V) :
    N (wLeviLin Q w₁ w₂ w₁' w₂' x) = wLeviLin Q w₁ w₂ w₁' w₂' (N x) := by
  rw [wLeviLin_apply, wLeviLin_apply, hNadj, hNadj, hNadj, hNadj, hN₁, hN₂, hN₁', hN₂']
  simp only [map_add, map_smul, hN₁, hN₂, hN₁', hN₂', polar_zero_right, zero_smul, add_zero,
    smul_zero]
  module

end WLevi

omit [CharP K 2] in
theorem eichler_commutator {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w u : V} (hwu : polar Q w u = 0)
    (hgw : g w = w) :
    eichler Q w u * g * (eichler Q w u)⁻¹ * g⁻¹ = eichler Q w (u - g u) := by
  have hc := eichler_conj hg w u
  rw [hgw] at hc
  have hwgu : polar Q w (g u) = 0 := by
    rw [← hgw, polar_map_of_mem hg, hwu]
  have h1 : eichler Q w u * g * (eichler Q w u)⁻¹ * g⁻¹ =
      eichler Q w u * (g * eichler Q w u * g⁻¹)⁻¹ := by group
  rw [h1, hc, eichler_inv hwgu, eichler_mul hwu (by rw [polar_neg_right, hwgu, neg_zero]),
    sub_eq_add_neg]

omit [CharP K 2] in
theorem eichler_mul_comm {Q : QuadraticForm K V} {s : V ≃ₗ[K] V}
    (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {w u : V} (hsw : s w = w)
    (hsu : s u = u) : eichler Q w u * s = s * eichler Q w u := by
  have hc := eichler_conj hs w u
  rw [hsw, hsu, mul_inv_eq_iff_eq_mul] at hc
  exact hc.symm

end OrthogonalShearC

end CFSG.SeitzReduction
