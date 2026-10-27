module

public import CFSG.ClassicalInvolution.Asc77.AscT3VHexX

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.v_normal_Y (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hgS : g ∈ (S : Subgroup G)) (hgK : conjSub g K = K) (hgt : g * t * g⁻¹ = t) :
    g ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G) := by
  have hgz : g * z * g⁻¹ = z := d.late_S_act_z hgS
  have hgJ : conjSub g J = J := by
    have hX2 : IsPGroup 2 ↥(Subgroup.zpowers g) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hgS)
    have hXS : Subgroup.zpowers g ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hgS
    have hcomm : Commute g t := by
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [hgt]
    have hXt : ∀ x ∈ Subgroup.zpowers g, x * t = t * x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hcomm.zpow_left k).eq
    have hK : ∀ x ∈ Subgroup.zpowers g, conjSub x K = K := by
      intro x hx
      have : x ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hgK)) hx
      exact mem_normalizer_iff_conjSub_eq.mp this
    exact (d.late_98_iff d.late_JW d.late_hW hX2 hXS hXt).mp hK g (Subgroup.mem_zpowers g)
  set Z : Subgroup G := Subgroup.closure {z, t} with hZ
  set NZ : Subgroup G := Subgroup.normalizer (Z : Set G) with hNZ
  have hgZ : g ∈ NZ := by
    refine T3V.mem_normalizer_of_conj_eq (T3V.conj_eq_of_mem_closure ?_)
    intro a ha
    rcases ha with rfl | ha
    · exact hgz
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hgt
  have hconj_inf : ∀ (A : Subgroup G), conjSub g (A ⊓ NZ) = conjSub g A ⊓ NZ := by
    intro A
    rw [late_conjSub_inf, conjSub_eq_self_of_mem hgZ]
  refine mem_normalizer_of_conjSub_le ?_
  calc conjSub g (pairNormalizers K J z t)
      = conjSub g (K ⊓ NZ) ⊔ conjSub g (J ⊓ NZ) := by
        rw [pairNormalizers, late_conjSub_sup]
    _ = (K ⊓ NZ) ⊔ (J ⊓ NZ) := by rw [hconj_inf K, hconj_inf J, hgK, hgJ]
    _ ≤ pairNormalizers K J z t := le_rfl

theorem Std20.v_same_aut (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hgS : g ∈ (S : Subgroup G)) (hgK : conjSub g K = K) (hgt : g * t * g⁻¹ = t) :
    ∃ x : G, x ∈ pairNormalizers K J z t ∧ x ∈ Subgroup.normalizer (W : Set G) ∧
      Odd (orderOf x) ∧ x * z * x⁻¹ = t ∧
      ∀ w ∈ W, g * (x * w * x⁻¹) * g⁻¹ = x * (g * w * g⁻¹) * x⁻¹ := by
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hgz : g * z * g⁻¹ = z := d.late_S_act_z hgS
  obtain ⟨g₀, hg₀Y, hg₀W, hg₀z, hg₀t⟩ := d.v_hexg
  obtain ⟨k, e, hk, hge⟩ := T3V.exists_pow_three_part g₀ (isOfFinOrder_of_finite g₀)
  obtain ⟨hx₀z, hx₀t⟩ := T3V.pow_act_of_mod hz2 hzt hg₀z hg₀t hk
  set x₀ := g₀ ^ k with hx₀
  have hx₀Y : x₀ ∈ pairNormalizers K J z t := Subgroup.pow_mem _ hg₀Y k
  have hx₀W : x₀ ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hg₀W k
  have hx₀odd : Odd (orderOf x₀) := by
    have : orderOf x₀ ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hge
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat this
  set x : G := x₀ * x₀ with hx
  have hxY : x ∈ pairNormalizers K J z t := Subgroup.mul_mem _ hx₀Y hx₀Y
  have hxW : x ∈ Subgroup.normalizer (W : Set G) := Subgroup.mul_mem _ hx₀W hx₀W
  have hxodd : Odd (orderOf x) := by
    have h1 : x = x₀ ^ 2 := by rw [hx, pow_two]
    have h2 : orderOf x ∣ orderOf x₀ := by rw [h1]; exact orderOf_pow_dvd 2
    exact hx₀odd.of_dvd_nat h2
  have hxz : x * z * x⁻¹ = t := by
    calc x * z * x⁻¹ = x₀ * (x₀ * z * x₀⁻¹) * x₀⁻¹ := by rw [hx]; group
      _ = x₀ * (z * t) * x₀⁻¹ := by rw [hx₀z]
      _ = (x₀ * z * x₀⁻¹) * (x₀ * t * x₀⁻¹) := by group
      _ = (z * t) * z := by rw [hx₀z, hx₀t]
      _ = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  have hgY := d.v_normal_Y hgS hgK hgt
  have hgW : g ∈ Subgroup.normalizer (W : Set G) := d.hWN hgS
  have hy := d.v_Y_odd hgY hgW hgz hgt hxY hxW hxodd
  refine ⟨x, hxY, hxW, hxodd, hxz, fun w hw => ?_⟩
  set y : G := x⁻¹ * (g * x * g⁻¹) with hy'
  have hyC : ∀ a ∈ W, a * y = y * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 a ha
  have hgx : g * x * g⁻¹ = x * y := by rw [hy']; group
  have hgwW : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgW w).mp hw
  calc g * (x * w * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * w * g⁻¹) * (g * x * g⁻¹)⁻¹ := by group
    _ = (x * y) * (g * w * g⁻¹) * (x * y)⁻¹ := by rw [hgx]
    _ = x * (y * (g * w * g⁻¹) * y⁻¹) * x⁻¹ := by group
    _ = x * (g * w * g⁻¹) * x⁻¹ := by
      have h1 : y * (g * w * g⁻¹) = (g * w * g⁻¹) * y := (hyC _ hgwW).symm
      rw [h1]
      group

theorem Std20.v_same_aut_exp (d : Std20 p f K K' J S R R' W V z t) {g : G}
    (hgS : g ∈ (S : Subgroup G)) (hgK : conjSub g K = K) (hgt : g * t * g⁻¹ = t) :
    ∃ x : G, x ∈ pairNormalizers K J z t ∧ x ∈ Subgroup.normalizer (W : Set G) ∧
      Odd (orderOf x) ∧ x * z * x⁻¹ = t ∧
      ∀ w ∈ W, ∀ k : ℤ, g * w * g⁻¹ = w ^ k → g * (x * w * x⁻¹) * g⁻¹ = (x * w * x⁻¹) ^ k := by
  obtain ⟨x, hxY, hxW, hxodd, hxz, hx⟩ := d.v_same_aut hgS hgK hgt
  refine ⟨x, hxY, hxW, hxodd, hxz, fun w hw k hk => ?_⟩
  rw [hx w hw, hk]
  have := conj_zpow (a := x) (b := w) (i := k)
  exact this.symm

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
