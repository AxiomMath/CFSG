module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3Count
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

open Subgroup

noncomputable section
open Classical

section Avg

variable {K V Γ : Type} [Field K] [AddCommGroup V] [Module K V] [Group Γ] [Fintype Γ]

@[expose] def av (ρ : Γ →* Module.End K V) (D : Subgroup Γ) : Module.End K V :=
  ((Nat.card D : K))⁻¹ • ∑ g ∈ subEl D, ρ g

variable (ρ : Γ →* Module.End K V)

theorem subEl_top : subEl (⊤ : Subgroup Γ) = Finset.univ := by
  ext g
  simp [mem_subEl]

theorem sum_left_mul {D : Subgroup Γ} {g : Γ} (hg : g ∈ D) :
    ρ g * ∑ x ∈ subEl D, ρ x = ∑ x ∈ subEl D, ρ x := by
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun x => g * x) (fun x => g⁻¹ * x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_subEl] at hx ⊢
    exact D.mul_mem hg hx
  · intro x hx
    rw [mem_subEl] at hx ⊢
    exact D.mul_mem (D.inv_mem hg) hx
  · intro x _
    simp
  · intro x _
    simp
  · intro x _
    exact (map_mul ρ g x).symm

theorem sum_right_mul {D : Subgroup Γ} {g : Γ} (hg : g ∈ D) :
    (∑ x ∈ subEl D, ρ x) * ρ g = ∑ x ∈ subEl D, ρ x := by
  rw [Finset.sum_mul]
  refine Finset.sum_nbij' (fun x => x * g) (fun x => x * g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_subEl] at hx ⊢
    exact D.mul_mem hx hg
  · intro x hx
    rw [mem_subEl] at hx ⊢
    exact D.mul_mem hx (D.inv_mem hg)
  · intro x _
    simp
  · intro x _
    simp
  · intro x _
    exact (map_mul ρ x g).symm

theorem av_mul_self {D : Subgroup Γ} (hD : (Nat.card D : K) ≠ 0) :
    av ρ D * av ρ D = av ρ D := by
  have hsum : (∑ x ∈ subEl D, ρ x) * (∑ x ∈ subEl D, ρ x) =
      (Nat.card D : K) • ∑ x ∈ subEl D, ρ x := by
    rw [Finset.sum_mul]
    have h : ∀ x ∈ subEl D, ρ x * (∑ y ∈ subEl D, ρ y) = ∑ y ∈ subEl D, ρ y :=
      fun x hx => sum_left_mul ρ ((mem_subEl D x).1 hx)
    rw [Finset.sum_congr rfl h, Finset.sum_const, subEl_card, Nat.cast_smul_eq_nsmul]
  unfold av
  rw [smul_mul_smul_comm, hsum, smul_smul]
  congr 1
  field_simp

theorem av_mul_avTop (D : Subgroup Γ) (hD : (Nat.card D : K) ≠ 0) :
    av ρ D * av ρ ⊤ = av ρ ⊤ := by
  have hsum : (∑ x ∈ subEl D, ρ x) * (∑ x ∈ subEl (⊤ : Subgroup Γ), ρ x) =
      (Nat.card D : K) • ∑ x ∈ subEl (⊤ : Subgroup Γ), ρ x := by
    rw [Finset.sum_mul]
    have h : ∀ x ∈ subEl D, ρ x * (∑ y ∈ subEl (⊤ : Subgroup Γ), ρ y) =
        ∑ y ∈ subEl (⊤ : Subgroup Γ), ρ y :=
      fun x hx => sum_left_mul ρ (Subgroup.mem_top x)
    rw [Finset.sum_congr rfl h, Finset.sum_const, subEl_card, Nat.cast_smul_eq_nsmul]
  unfold av
  rw [smul_mul_smul_comm, hsum, smul_smul]
  congr 1
  field_simp

theorem top_mul_av (D : Subgroup Γ) (hD : (Nat.card D : K) ≠ 0) :
    av ρ ⊤ * av ρ D = av ρ ⊤ := by
  have hsum : (∑ x ∈ subEl (⊤ : Subgroup Γ), ρ x) * (∑ x ∈ subEl D, ρ x) =
      (Nat.card D : K) • ∑ x ∈ subEl (⊤ : Subgroup Γ), ρ x := by
    rw [Finset.mul_sum]
    have h : ∀ x ∈ subEl D, (∑ y ∈ subEl (⊤ : Subgroup Γ), ρ y) * ρ x =
        ∑ y ∈ subEl (⊤ : Subgroup Γ), ρ y := by
      intro x hx
      rw [Finset.sum_mul]
      refine Finset.sum_nbij' (fun y => y * x) (fun y => y * x⁻¹) ?_ ?_ ?_ ?_ ?_
      · intro y _
        exact (mem_subEl _ _).2 (Subgroup.mem_top _)
      · intro y _
        exact (mem_subEl _ _).2 (Subgroup.mem_top _)
      · intro y _
        simp
      · intro y _
        simp
      · intro y _
        exact (map_mul ρ y x).symm
    rw [Finset.sum_congr rfl h, Finset.sum_const, subEl_card, Nat.cast_smul_eq_nsmul]
  unfold av
  rw [smul_mul_smul_comm, hsum, smul_smul]
  congr 1
  field_simp

theorem fib_card_eq {D E : Subgroup Γ} {g x₀ y₀ : Γ} (hx₀ : x₀ ∈ D) (hy₀ : y₀ ∈ E)
    (hg : x₀ * y₀ = g) :
    ((subEl D ×ˢ subEl E).filter (fun p : Γ × Γ => p.1 * p.2 = g)).card =
      (subEl (D ⊓ E)).card := by
  refine Finset.card_bij' (fun p _ => x₀⁻¹ * p.1) (fun t _ => (x₀ * t, t⁻¹ * y₀)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, mem_subEl] at hp
    obtain ⟨⟨ha, hb⟩, hab⟩ := hp
    rw [mem_subEl, Subgroup.mem_inf]
    have hab' : a = x₀ * y₀ * b⁻¹ := eq_mul_inv_of_mul_eq (hab.trans hg.symm)
    have heq : x₀⁻¹ * a = y₀ * b⁻¹ := by rw [hab']; group
    constructor
    · exact D.mul_mem (D.inv_mem hx₀) ha
    · show x₀⁻¹ * a ∈ E
      rw [heq]
      exact E.mul_mem hy₀ (E.inv_mem hb)
  · intro t ht
    rw [mem_subEl, Subgroup.mem_inf] at ht
    simp only [Finset.mem_filter, Finset.mem_product, mem_subEl]
    refine ⟨⟨D.mul_mem hx₀ ht.1, E.mul_mem (E.inv_mem ht.2) hy₀⟩, ?_⟩
    show x₀ * t * (t⁻¹ * y₀) = g
    rw [← hg]
    group
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, mem_subEl] at hp
    obtain ⟨_, hab⟩ := hp
    have hx : x₀ * y₀ = a * b := hg.trans hab.symm
    refine Prod.ext ?_ ?_
    · show x₀ * (x₀⁻¹ * a) = a
      group
    · show (x₀⁻¹ * a)⁻¹ * y₀ = b
      calc (x₀⁻¹ * a)⁻¹ * y₀ = a⁻¹ * (x₀ * y₀) := by group
        _ = b := by rw [hx]; group
  · intro t _
    show x₀⁻¹ * (x₀ * t) = t
    group

theorem fib_card_le_three {D E : Subgroup Γ} (hΓ : Nat.card Γ = 27) {g : Γ}
    (hD : D.index = 3) (hE : E.index = 3) (hne : D ≠ E) :
    ((subEl D ×ˢ subEl E).filter (fun p : Γ × Γ => p.1 * p.2 = g)).card ≤ 3 := by
  rcases ((subEl D ×ˢ subEl E).filter (fun p : Γ × Γ => p.1 * p.2 = g)).eq_empty_or_nonempty
    with h | ⟨p, hp⟩
  · rw [h]
    simp
  · simp only [Finset.mem_filter, Finset.mem_product, mem_subEl] at hp
    rw [fib_card_eq hp.1.1 hp.1.2 hp.2, subEl_card, card_inf_eq_three hΓ hD hE hne]

theorem fib_card_eq_three {D E : Subgroup Γ} (hΓ : Nat.card Γ = 27) (hD : D.index = 3)
    (hE : E.index = 3) (hne : D ≠ E) (g : Γ) :
    ((subEl D ×ˢ subEl E).filter (fun p : Γ × Γ => p.1 * p.2 = g)).card = 3 := by
  have hfib := Finset.card_eq_sum_card_fiberwise (f := fun p : Γ × Γ => p.1 * p.2)
    (s := subEl D ×ˢ subEl E) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have h81 : (subEl D ×ˢ subEl E).card = 81 := by
    rw [Finset.card_product, subEl_card, subEl_card, card_of_index_eq_three hΓ hD,
      card_of_index_eq_three hΓ hE]
  have hsum81 : ∑ b : Γ, ((subEl D ×ˢ subEl E).filter (fun p : Γ × Γ => p.1 * p.2 = b)).card
      = ∑ b : Γ, 3 := by
    rw [← hfib, h81, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hΓ]
    norm_num
  have heq := (Finset.sum_eq_sum_iff_of_le (fun b _ => fib_card_le_three hΓ hD hE hne)).1 hsum81
  exact heq g (Finset.mem_univ g)

theorem av_mul_av_of_ne (hΓ : Nat.card Γ = 27) (h3 : (3 : K) ≠ 0) {D E : Subgroup Γ}
    (hD : D.index = 3) (hE : E.index = 3) (hne : D ≠ E) :
    av ρ D * av ρ E = av ρ ⊤ := by
  have hDc : Nat.card D = 9 := card_of_index_eq_three hΓ hD
  have hEc : Nat.card E = 9 := card_of_index_eq_three hΓ hE
  have hdouble : (∑ x ∈ subEl D, ρ x) * (∑ y ∈ subEl E, ρ y) = (3 : K) • ∑ g : Γ, ρ g := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    simp_rw [← map_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.univ)
      (g := fun p : Γ × Γ => p.1 * p.2) (fun _ _ => Finset.mem_univ _)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_congr rfl (fun p hp => congrArg ρ (Finset.mem_filter.1 hp).2),
      Finset.sum_const, fib_card_eq_three hΓ hD hE hne j]
    exact (Nat.cast_smul_eq_nsmul K 3 (ρ j)).symm
  unfold av
  rw [smul_mul_smul_comm, hdouble, smul_smul, subEl_top, Subgroup.card_top, hΓ, hDc, hEc]
  have h9 : (9 : K) ≠ 0 := by
    have e : (9 : K) = 3 * 3 := by norm_num
    rw [e]
    exact mul_ne_zero h3 h3
  have h27 : (27 : K) ≠ 0 := by
    have e : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [e]
    exact mul_ne_zero (mul_ne_zero h3 h3) h3
  congr 1
  push_cast
  field_simp
  norm_num

theorem sum_av_idx3 (hΓ : Nat.card Γ = 27) (hexp : ∀ g : Γ, g ^ 3 = 1)
    (hcomm : ∀ g h : Γ, g * h = h * g) (h3 : (3 : K) ≠ 0) :
    ∑ F ∈ idx3 Γ, av ρ F = 1 + (12 : K) • av ρ ⊤ := by
  have h9 : (9 : K) ≠ 0 := by
    have e : (9 : K) = 3 * 3 := by norm_num
    rw [e]
    exact mul_ne_zero h3 h3
  have h1 : ∀ F ∈ idx3 Γ, av ρ F = (9 : K)⁻¹ • ∑ g ∈ subEl F, ρ g := by
    intro F hF
    unfold av
    rw [card_of_index_eq_three hΓ ((mem_idx3 F).1 hF)]
    norm_num
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, sum_idx3_sub hΓ hexp hcomm (fun g => ρ g)]
  unfold av
  rw [subEl_top, Subgroup.card_top, hΓ, map_one]
  rw [← Nat.cast_smul_eq_nsmul K 9, ← Nat.cast_smul_eq_nsmul K 4]
  have a1 : (9 : K)⁻¹ * 9 = 1 := inv_mul_cancel₀ h9
  have a2 : (9 : K)⁻¹ * 4 = 12 * ((27 : K))⁻¹ := by
    have h27 : (27 : K) ≠ 0 := by
      have e : (27 : K) = 3 * 3 * 3 := by norm_num
      rw [e]
      exact mul_ne_zero (mul_ne_zero h3 h3) h3
    field_simp
    norm_num
  rw [smul_add, smul_smul, smul_smul, smul_smul]
  push_cast
  rw [a1, a2, one_smul]

theorem bilin_av (B : LinearMap.BilinForm K V)
    (hB : ∀ (g : Γ) (u w : V), B (ρ g u) (ρ g w) = B u w) (D : Subgroup Γ) (u v : V) :
    B (av ρ D u) v = B u (av ρ D v) := by
  have key : ∀ x : Γ, B (ρ x u) v = B u (ρ x⁻¹ v) := by
    intro x
    have h := hB x u (ρ x⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h
  have hinv : ∑ x ∈ subEl D, B u (ρ x⁻¹ v) = ∑ x ∈ subEl D, B u (ρ x v) := by
    refine Finset.sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_subEl] at hx ⊢
      exact D.inv_mem hx
    · intro x hx
      rw [mem_subEl] at hx ⊢
      exact D.inv_mem hx
    · intro x _
      simp
    · intro x _
      simp
    · intro x _
      rfl
  unfold av
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  exact hinv

end Avg

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KC3

end
