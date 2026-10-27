module

public import CFSG.ClassicalInvolution.Q3.TL4D4NCOne

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

namespace Trip

variable (T : Trip Q)

theorem eichler_sub {v a' : V} (hv : Q v = 0) (hva : polar Q v a' = 0) (x : V) :
    eichler Q v a' x - eichler Q v (-a') x =
      (2 : K) • (polar Q x v • a' - polar Q x a' • v) := by
  have hva' : polar Q v (-a') = 0 := by rw [polar_neg_right, hva, neg_zero]
  rw [eichler_apply hv hva, eichler_apply hv hva', polar_neg_right, QuadraticMap.map_neg]
  module

theorem Q_sub_smul {v a' : V} (hv : Q v = 0) (hva : polar Q v a' = 0) (x y : K) :
    Q (x • a' - y • v) = x ^ 2 * Q a' := by
  rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, hv,
    polar_smul_left_eq, polar_smul_right_eq, polar_comm, hva]
  ring

theorem eichler_mem_eich {v a' : V} (hv : v ∈ T.span) (ha' : a' ∈ T.span) (hQv : Q v = 0)
    (hva : polar Q v a' = 0) : eichler Q v a' ∈ T.eich ∧ eichler Q v (-a') ∈ T.eich :=
  ⟨⟨v, a', hv, ha', hQv, hva, rfl⟩,
    ⟨v, -a', hv, neg_mem ha', hQv, by rw [polar_neg_right, hva, neg_zero], rfl⟩⟩

theorem eq_zero_of_invariant (h2 : (2 : K) ≠ 0) {U : Submodule K V}
    (hts : ∀ x ∈ U, Q x = 0) (hinv : ∀ E ∈ T.eich, ∀ x ∈ U, E x ∈ U) {w : V} (hwU : w ∈ U)
    (hwW : w ∈ T.span) : w = 0 := by
  by_contra hw0
  obtain ⟨v, hv, a', ha', hQv, hva, hQa, hwv⟩ := T.exists_sing_aniso h2 hwW hw0
  obtain ⟨h₁, h₂⟩ := T.eichler_mem_eich hv ha' hQv hva
  have hd := U.sub_mem (hinv _ h₁ w hwU) (hinv _ h₂ w hwU)
  rw [eichler_sub hQv hva] at hd
  have h := hts _ hd
  rw [map_smul_eq_sq, Q_sub_smul hQv hva] at h
  exact mul_ne_zero (pow_ne_zero 2 h2) (mul_ne_zero (pow_ne_zero 2 hwv) hQa) h

theorem eq_zero_of_fixed (h2 : (2 : K) ≠ 0) {w : V} (hwW : w ∈ T.span)
    (hfix : ∀ E ∈ T.eich, E w = w) : w = 0 := by
  by_contra hw0
  obtain ⟨v, hv, a', ha', hQv, hva, hQa, hwv⟩ := T.exists_sing_aniso h2 hwW hw0
  obtain ⟨h₁, h₂⟩ := T.eichler_mem_eich hv ha' hQv hva
  have hd := eichler_sub hQv hva w
  rw [hfix _ h₁, hfix _ h₂, sub_self] at hd
  have h := congrArg Q hd
  rw [QuadraticMap.map_zero, map_smul_eq_sq, Q_sub_smul hQv hva] at h
  exact mul_ne_zero (pow_ne_zero 2 h2) (mul_ne_zero (pow_ne_zero 2 hwv) hQa) h.symm

theorem eich_fix {E : V ≃ₗ[K] V} (hE : E ∈ T.eich) {x : V} (hp : polar Q x T.p = 0)
    (hq : polar Q x T.q = 0) (ha : polar Q x T.a = 0) : E x = x := by
  obtain ⟨v, w, hv, hw, hQv, hvw, rfl⟩ := hE
  rw [eichler_apply hQv hvw, T.polar_eq_zero_of_perp hp hq ha hv,
    T.polar_eq_zero_of_perp hp hq ha hw]
  simp

theorem eich_mem {E : V ≃ₗ[K] V} (hE : E ∈ T.eich) {x : V} (hx : x ∈ T.span) :
    E x ∈ T.span := by
  obtain ⟨v, w, hv, hw, hQv, hvw, rfl⟩ := hE
  rw [eichler_apply hQv hvw]
  exact sub_mem (add_mem hx (Submodule.smul_mem _ _ hw)) (Submodule.smul_mem _ _ hv)

@[expose] noncomputable def proj (x : V) : V :=
  polar Q x T.q • T.p + polar Q x T.p • T.q + (polar Q x T.a / (2 * Q T.a)) • T.a

theorem proj_mem (x : V) : T.proj x ∈ T.span :=
  T.mem_span_iff.mpr ⟨_, _, _, rfl⟩

theorem sub_proj_perp (h2 : (2 : K) ≠ 0) (x : V) :
    polar Q (x - T.proj x) T.p = 0 ∧ polar Q (x - T.proj x) T.q = 0 ∧
      polar Q (x - T.proj x) T.a = 0 := by
  have h2a : (2 : K) * Q T.a ≠ 0 := mul_ne_zero h2 T.Qa
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [proj, polar_sub_left, polar_add_left, polar_smul_left_eq, T.pp, T.qq, T.pq,
      T.qp, T.pa, T.ap, T.qa, T.aq, T.aa]
  · ring
  · ring
  · rw [div_mul_cancel₀ _ h2a]
    ring

theorem two_mul_finrank_le [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {U : Submodule K V} (hts : ∀ x ∈ U, Q x = 0) :
    2 * Module.finrank K U ≤ Module.finrank K V := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) U := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change polarBilin Q y x = 0
    rw [polarBilin_apply_apply, polar, hts _ (U.add_mem hy hx), hts y hy, hts x hx]
    ring
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := Submodule.finrank_le U
  omega

end Trip

end CFSG.ClassicalInvolution.Q3.TL4
