module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Core
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3 QuadraticMap Module

noncomputable section
open Classical

section Decomp

variable {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Group Γ] [Fintype Γ] {ρ : Γ →* Module.End K V}

theorem right_mul_av {D : Subgroup Γ} {g : Γ} (hg : g ∈ D) : av ρ D * ρ g = av ρ D := by
  unfold av
  rw [smul_mul_assoc, sum_right_mul ρ hg]

theorem commute_av_of (D : Subgroup Γ) (Y : Module.End K V)
    (hY : ∀ g ∈ D, Y * ρ g = ρ g * Y) : Y * av ρ D = av ρ D * Y := by
  unfold av
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun g hg => ?_
  exact hY g ((mem_subEl D g).1 hg)

theorem commute_Qf (hcomm : ∀ g h : Γ, g * h = h * g) (o : Option (Subgroup Γ)) (γ : Γ) :
    ρ γ * Qf ρ o = Qf ρ o * ρ γ := by
  have key : ∀ D : Subgroup Γ, ρ γ * av ρ D = av ρ D * ρ γ := fun D =>
    commute_av_of D (ρ γ) (fun g _ => by rw [← map_mul, ← map_mul, hcomm])
  cases o with
  | none => exact key ⊤
  | some F =>
    by_cases hF : F ∈ idx3 Γ
    · rw [Qf_some_of_mem hF, mul_sub, sub_mul, key F, key ⊤]
    · rw [Qf_some_of_not_mem hF]
      simp

theorem av_top_apply_of_fixed (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) {y : V}
    (hy : ∀ γ : Γ, ρ γ y = y) : av ρ ⊤ y = y := by
  unfold av
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun g _ => hy g), Finset.sum_const, subEl_top, Finset.card_univ,
    ← Nat.card_eq_fintype_card, Subgroup.card_top, hΓ]
  have h27 : ((27 : ℕ) : K) ≠ 0 := by
    have e : ((27 : ℕ) : K) = 3 * 3 * 3 := by push_cast; norm_num
    rw [e]
    exact mul_ne_zero (mul_ne_zero h3 h3) h3
  rw [← Nat.cast_smul_eq_nsmul K 27 y, smul_smul, inv_mul_cancel₀ h27, one_smul]

theorem sq_add_self_add_one (h3 : (3 : K) ≠ 0) (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) {F : Subgroup Γ} (hF : F ∈ idx3 Γ) {g : Γ} (hg : g ∉ F)
    {x : V} (hx : x ∈ LinearMap.range (Qf ρ (some F))) :
    ρ g (ρ g x) + ρ g x + x = 0 := by
  have hFm : F.index = 3 := (mem_idx3 F).1 hF
  have hnc := natCard_ne_zero' (K := K) (Γ := Γ) h3 hΓ
  obtain ⟨y0, rfl⟩ := hx
  have hxF : av ρ F (Qf ρ (some F) y0) = Qf ρ (some F) y0 := by
    have : av ρ F * Qf ρ (some F) = Qf ρ (some F) := by
      rw [Qf_some_of_mem hF, mul_sub, av_mul_self ρ (hnc F), av_mul_avTop ρ F (hnc F)]
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End K V => f y0) this
  have hxT : av ρ ⊤ (Qf ρ (some F) y0) = 0 := by
    have : av ρ ⊤ * Qf ρ (some F) = 0 := by
      rw [Qf_some_of_mem hF, mul_sub, top_mul_av ρ F (hnc F), av_top_mul_top h3 hΓ, sub_self]
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End K V => f y0) this
  generalize Qf ρ (some F) y0 = x at hxF hxT ⊢
  have hg3 : g * g * g = 1 := by
    have := hexp g
    rwa [pow_three'] at this
  have hρ3 : ∀ z : V, ρ g (ρ g (ρ g z)) = z := by
    intro z
    have := congrArg (fun f : Module.End K V => f z) (show ρ g * ρ g * ρ g = 1 by
      rw [← map_mul, ← map_mul, hg3, map_one])
    simpa [Module.End.mul_apply] using this
  have hFx : ∀ d ∈ F, ρ d x = x := by
    intro d hd
    have := congrArg (fun f : Module.End K V => f x) (left_mul_av (ρ := ρ) hd)
    simp only [Module.End.mul_apply] at this
    rw [hxF] at this
    exact this
  have hcommρ : ∀ (a b : Γ) (z : V), ρ a (ρ b z) = ρ b (ρ a z) := by
    intro a b z
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hcomm]
  set y := ρ g (ρ g x) + ρ g x + x with hy
  have hgy : ρ g y = y := by
    rw [hy, map_add, map_add, hρ3]
    abel
  have hdy : ∀ d ∈ F, ρ d y = y := by
    intro d hd
    rw [hy, map_add, map_add, hcommρ d g, hcommρ d g, hFx d hd]
  have htop : Subgroup.zpowers g ⊔ F = ⊤ := by
    have hle : F ≤ Subgroup.zpowers g ⊔ F := le_sup_right
    have hdvd : (Subgroup.zpowers g ⊔ F).index ∣ F.index := Subgroup.index_dvd_of_le hle
    rw [hFm] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
    · exact Subgroup.index_eq_one.1 h1
    · exfalso
      apply hg
      have hc1 : Nat.card F = 9 := card_of_index_eq_three hΓ hFm
      have hc2 : Nat.card (Subgroup.zpowers g ⊔ F : Subgroup Γ) = 9 :=
        card_of_index_eq_three hΓ h3'
      have heq : F = Subgroup.zpowers g ⊔ F :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  let S : Subgroup Γ :=
    { carrier := {γ | ρ γ y = y}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ρ a y = y := ha
        have hb' : ρ b y = y := hb
        show ρ (a * b) y = y
        rw [map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := by
        show ρ 1 y = y
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha => by
        have ha' : ρ a y = y := ha
        show ρ a⁻¹ y = y
        have : ρ a⁻¹ (ρ a y) = y := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rwa [ha'] at this }
  have hSle : (⊤ : Subgroup Γ) ≤ S := by
    rw [← htop]
    exact sup_le (Subgroup.zpowers_le.2 hgy) (fun d hd => hdy d hd)
  have hfix : ∀ γ : Γ, ρ γ y = y := fun γ => hSle (Subgroup.mem_top γ)
  have h1 : av ρ ⊤ y = y := av_top_apply_of_fixed h3 hΓ hfix
  have hrt : ∀ z : V, av ρ ⊤ (ρ g z) = av ρ ⊤ z := by
    intro z
    have := congrArg (fun f : Module.End K V => f z) (right_mul_av (ρ := ρ) (Subgroup.mem_top g))
    simpa [Module.End.mul_apply] using this
  have h2 : av ρ ⊤ y = 0 := by
    rw [hy, map_add, map_add, hrt, hrt, hxT]
    simp
  rw [← h1, h2]

end Decomp

section Even

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem polar_map_of_isometry {Q : QuadraticForm K V} {T : V →ₗ[K] V}
    (hTQ : ∀ x, Q (T x) = Q x) (a b : V) : polar Q (T a) (T b) = polar Q a b := by
  simp only [polar, ← map_add, hTQ]

theorem polar_self_map {Q : QuadraticForm K V} {T : V →ₗ[K] V} (hTQ : ∀ x, Q (T x) = Q x)
    {x : V} (hx : T (T x) + T x + x = 0) : polar Q x (T x) = - Q x := by
  have h1 : T (T x) = -(x + T x) := by
    apply eq_neg_of_add_eq_zero_left
    have : T (T x) + (x + T x) = T (T x) + T x + x := by abel
    rw [this]
    exact hx
  have h2 : Q (T (T x)) = Q x := by rw [hTQ, hTQ]
  have h3 : Q (x + T x) = Q x + Q (T x) + polar Q x (T x) := QuadraticMap.map_add Q x (T x)
  rw [h1, QuadraticMap.map_neg, h3, hTQ] at h2
  linear_combination h2

theorem even_finrank_of_cube {Q : QuadraticForm K V} {W : Submodule K V} [FiniteDimensional K W]
    (h3 : (3 : K) ≠ 0) {T : V →ₗ[K] V} (hTW : ∀ x ∈ W, T x ∈ W)
    (hT : ∀ x ∈ W, T (T x) + T x + x = 0) (hTQ : ∀ x, Q (T x) = Q x)
    (hnd : ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0) : Even (finrank K W) := by
  set A : V →ₗ[K] V := (2 : K) • T + LinearMap.id with hA
  have hAapp : ∀ x, A x = (2 : K) • T x + x := fun x => rfl
  have hAW : ∀ x ∈ W, A x ∈ W := fun x hx => by
    rw [hAapp]
    exact W.add_mem (W.smul_mem 2 (hTW x hx)) hx
  let β : LinearMap.BilinForm K W := (polarBilin Q).compl₁₂ (A ∘ₗ W.subtype) W.subtype
  have hβ : ∀ u v : W, β u v = polar Q (A u) v := fun u v => by simp [β]
  have hT2 : ∀ x ∈ W, T (T x) = -x - T x := by
    intro x hx
    have h := hT x hx
    calc T (T x) = (T (T x) + T x + x) - T x - x := by abel
      _ = -x - T x := by rw [h]; abel
  have hT3 : ∀ x ∈ W, T (T (T x)) = x := by
    intro x hx
    have h := hT x hx
    have h' := congrArg T h
    rw [map_add, map_add, map_zero] at h'
    calc T (T (T x)) = (T (T (T x)) + T (T x) + T x) - (T (T x) + T x + x) + x := by abel
      _ = x := by rw [h', h]; abel
  have hAA : ∀ x ∈ W, A (A x) = (-3 : K) • x := by
    intro x hx
    simp only [hAapp, map_add, map_smul]
    rw [hT2 x hx]
    module
  have hskew : ∀ u ∈ W, ∀ v ∈ W, polar Q (A u) v = - polar Q u (A v) := by
    intro u hu v hv
    have e1 : polar Q (T u) v = polar Q (T (T u)) (T v) :=
      (polar_map_of_isometry hTQ (T u) v).symm
    have e2 : polar Q (T (T u)) (T v) = polar Q (T (T (T u))) (T (T v)) :=
      (polar_map_of_isometry hTQ (T (T u)) (T v)).symm
    have e3 : polar Q (T u) v = polar Q u (T (T v)) := by rw [e1, e2, hT3 u hu]
    rw [hAapp, hAapp, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, e3, hT2 v hv,
      QuadraticMap.polar_sub_right, QuadraticMap.polar_neg_right]
    simp only [smul_eq_mul]
    ring
  have hself : ∀ x ∈ W, polar Q (A x) x = 0 := by
    intro x hx
    rw [hAapp, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, polar_comm,
      polar_self_map hTQ (hT x hx), QuadraticMap.polar_self]
    simp only [smul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  have hβalt : β.IsAlt := fun x => by rw [hβ]; exact hself x x.2
  have hβnd : β.Nondegenerate := by
    constructor
    · intro u hu
      have h1 : A u ∈ W := hAW u u.2
      have h2 : A u = 0 := hnd (A u) h1 (fun y hy => by
        have := hu ⟨y, hy⟩
        rwa [hβ] at this)
      have h4 : A (A u) = 0 := by rw [h2, map_zero]
      rw [hAA u u.2] at h4
      have h5 : (u : V) = 0 := by
        rcases smul_eq_zero.1 h4 with h | h
        · exact absurd (neg_eq_zero.1 h) h3
        · exact h
      exact Subtype.ext h5
    · intro v hv
      have h1 : A v ∈ W := hAW v v.2
      have h2 : A v = 0 := hnd (A v) h1 (fun y hy => by
        have := hv ⟨y, hy⟩
        rw [hβ, hskew y hy v v.2] at this
        rw [polar_comm]
        exact neg_eq_zero.1 this)
      have h4 : A (A v) = 0 := by rw [h2, map_zero]
      rw [hAA v v.2] at h4
      have h5 : (v : V) = 0 := by
        rcases smul_eq_zero.1 h4 with h | h
        · exact absurd (neg_eq_zero.1 h) h3
        · exact h
      exact Subtype.ext h5
  exact LinearMap.BilinForm.IsAlt.even_finrank hβalt hβnd

end Even

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
