module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Orbit

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem eq_V_of_f_invariant [Finite G] {V U : Subgroup G} {f : G} (k : ℕ) (hf : f ^ 3 ^ k = 1)
    (hfV : ∀ v ∈ V, f * v * f⁻¹ ∈ V) (hV : Nat.card V = 4)
    (hnc : ∃ v ∈ V, f * v * f⁻¹ ≠ v) (hUV : U ≤ V) (hfU : ∀ u ∈ U, f * u * f⁻¹ ∈ U)
    (hU : 1 < Nat.card U) : U = V := by
  have hdvd : Nat.card U ∣ 4 := hV ▸ Subgroup.card_dvd_of_le hUV
  have hle : Nat.card U ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hfree := fix_free_four V f k hf hfV hV hnc
  have h234 : Nat.card U = 2 ∨ Nat.card U = 3 ∨ Nat.card U = 4 := by omega
  rcases h234 with h2 | h3 | h4
  · exfalso
    have hnt : Nontrivial ↥U := Finite.one_lt_card_iff_nontrivial.1 hU
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥U)
    have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
    have hfz : f * (z : G) * f⁻¹ ∈ U := hfU z z.2
    by_cases hfix : f * (z : G) * f⁻¹ = z
    · exact hz1 (hfree z (hUV z.2) hfix)
    · have hne1 : f * (z : G) * f⁻¹ ≠ 1 := by
        intro h
        apply hz1
        have : (z : G) = f⁻¹ * (f * (z : G) * f⁻¹) * f := by group
        rw [this, h]; group
      have := three_le_card U.one_mem z.2 hfz (Ne.symm hz1) (Ne.symm hne1) (Ne.symm hfix)
      omega
  · exfalso
    rw [h3] at hdvd
    omega
  · exact Subgroup.eq_of_le_of_card_ge hUV (by rw [h4, hV])

namespace Ctx3

variable {x : G} {T V H : Subgroup G} {f : G} (c : Ctx3 G x T V H f)
include c

theorem f_norm_H0 : f ∈ normalizer ((Hzero H f : Subgroup G) : Set G) :=
  normalizer_Hzero c.hc.a_norm

theorem f_conj_H0 {a : G} (ha : a ∈ Hzero H f) : f * a * f⁻¹ ∈ Hzero H f :=
  (mem_normalizer_iff.1 c.f_norm_H0 a).1 ha

theorem f_conj_inv_H0 {a : G} (ha : a ∈ Hzero H f) : f⁻¹ * a * f ∈ Hzero H f := by
  have h := (mem_normalizer_iff.1 c.f_norm_H0 (f⁻¹ * a * f)).2
  have e : f * (f⁻¹ * a * f) * f⁻¹ = a := by group
  rw [e] at h
  exact h ha

theorem x_conj_inv_H0 {a : G} (ha : a ∈ Hzero H f) : x⁻¹ * a * x ∈ Hzero H f := by
  have h := c.H0_norm_H x⁻¹ (H.inv_mem c.x_mem_H) a ha
  rw [inv_inv] at h
  exact h

theorem f_conj_V {v : G} (hv : v ∈ V) : f * v * f⁻¹ ∈ V := (mem_normalizer_iff.1 c.hc.f_mem v).1 hv

theorem f_moves_V [Finite G] : ∃ v ∈ V, f * v * f⁻¹ ≠ v := exists_moved_of c.hc.f_not

theorem V_le_of_invariant [Finite G] {Y : Subgroup G} (hYP : Y ≤ Hzero H f) (hY : 1 < Nat.card Y)
    (hxY : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y) (hfY : ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) : V ≤ Y := by
  have hYp : IsPGroup 2 ↥Y := c.H_two.to_le (hYP.trans c.H0_le)
  obtain ⟨z, hzY, hz1, hxz⟩ := exists_fixed_ne_one c.x_sq hYp hY hxY
  have hzV : z ∈ V := by
    rw [← c.C_H0_x]
    refine ⟨hYP hzY, ?_⟩
    show z ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxz]
  obtain ⟨k, hk⟩ := c.hc.f3
  have hU : Y ⊓ V = V := by
    apply eq_V_of_f_invariant (U := Y ⊓ V) k hk (fun v hv => c.f_conj_V hv) c.out.V_four.2
      c.f_moves_V inf_le_right
    · intro u hu
      exact ⟨hfY u hu.1, c.f_conj_V hu.2⟩
    · exact one_lt_card_of_ne_one ⟨hzY, hzV⟩ hz1
  intro v hv
  have : v ∈ Y ⊓ V := by rw [hU]; exact hv
  exact this.1

theorem V_central [Finite G] : ∀ v ∈ V, ∀ a ∈ Hzero H f, v * a = a * v := by
  have hP : IsPGroup 2 ↥(Hzero H f) := c.H_two.to_le c.H0_le
  have hcard : 1 < Nat.card (Hzero H f) := by
    have h1 := Subgroup.card_le_of_le c.V_le_H0
    rw [c.out.V_four.2] at h1
    omega
  have : Nontrivial ↥(Hzero H f) := Finite.one_lt_card_iff_nontrivial.1 hcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcn : Nontrivial ↥(Subgroup.center ↥(Hzero H f)) := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥(Hzero H f)))
  have hz1 : ((z : ↥(Hzero H f)) : G) ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  set Y : Subgroup G := Hzero H f ⊓ centralizer ((Hzero H f : Subgroup G) : Set G) with hY
  have hzY : ((z : ↥(Hzero H f)) : G) ∈ Y := by
    refine ⟨(z : ↥(Hzero H f)).2, ?_⟩
    show ((z : ↥(Hzero H f)) : G) ∈ centralizer ((Hzero H f : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have := Subgroup.mem_center_iff.1 z.2 ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hconj : ∀ m : G, (∀ a ∈ Hzero H f, m⁻¹ * a * m ∈ Hzero H f) →
      (∀ a ∈ Hzero H f, m * a * m⁻¹ ∈ Hzero H f) → ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := by
    intro m hm hm' y hy
    refine ⟨hm' y hy.1, ?_⟩
    show m * y * m⁻¹ ∈ centralizer ((Hzero H f : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro a ha
    have h1 := mem_centralizer_iff.1 hy.2 (m⁻¹ * a * m) (hm a ha)
    calc a * (m * y * m⁻¹) = m * ((m⁻¹ * a * m) * y) * m⁻¹ := by group
      _ = m * (y * (m⁻¹ * a * m)) * m⁻¹ := by rw [h1]
      _ = (m * y * m⁻¹) * a := by group
  have hVY : V ≤ Y := by
    apply c.V_le_of_invariant inf_le_left (one_lt_card_of_ne_one hzY hz1)
    · intro y hy
      exact hconj x (fun a ha => c.x_conj_inv_H0 ha) (c.H0_norm_H x c.x_mem_H) y hy
    · intro y hy
      exact hconj f (fun a ha => c.f_conj_inv_H0 ha) (fun a ha => c.f_conj_H0 ha) y hy
  intro v hv a ha
  have := mem_centralizer_iff.1 (hVY hv).2 a ha
  exact this.symm

end Ctx3

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
