module

public import CFSG.GH74.Uniqueness.SU.KI1r4LyPerf
public import CFSG.GH74.Uniqueness.SU.KI1r4LyBase
public import CFSG.GH74.Uniqueness.SU.KI1r4LyBad

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.GH74.Generic.S45.LAlt
open scoped commutatorElement

theorem order4El_even : order4El ∈ alternatingGroup (Fin 11) :=
  Perm.mem_alternatingGroup.2 (by decide +kernel)

theorem orderOf_order4El : orderOf order4El = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ¬ order4El ^ 2 ^ 1 = 1 := by decide +kernel
  have h2 : order4El ^ 2 ^ (1 + 1) = 1 := by decide +kernel
  simpa using orderOf_eq_prime_pow h1 h2

theorem center_J_eq_bot :
    Subgroup.center J = ⊥ := by
  have hs : IsSimpleGroup J := isSimpleGroup_J
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    apply conj_lyz_ne_one
    have hz : lyz ∈ Subgroup.center J := by rw [h]; exact Subgroup.mem_top _
    refine MulEquiv.ext fun g => ?_
    rw [MulAut.conj_apply, MulAut.one_apply]
    have := Subgroup.mem_center_iff.1 hz g
    calc lyz * g * lyz⁻¹ = g * lyz * lyz⁻¹ := by rw [this]
      _ = g := by group

theorem lyC_perfect_order4 :
    ⁅lyC, lyC⁆ = lyC ∧ ∃ c ∈ lyC, 4 ∣ orderOf c := by
  refine ⟨Subgroup.isPerfect_iff.1 inferInstance, ?_⟩
  obtain ⟨c, hc⟩ := projAlt_surjective lyCenterEquiv ⟨order4El, order4El_even⟩
  refine ⟨(c : J), c.2, ?_⟩
  have h1 := orderOf_map_dvd (projAlt lyCenterEquiv) c
  rw [hc, Subgroup.orderOf_mk, orderOf_order4El] at h1
  rw [Subgroup.orderOf_coe]
  exact h1

theorem orderOf_conj_J (x c : J) : orderOf (x * c * x⁻¹) = orderOf c := by
  have := (MulAut.conj x).orderOf_eq c
  simpa [MulAut.conj_apply] using this

theorem perfect_map_conj (x : J) {P : Subgroup J} (hP : ⁅P, P⁆ = P)
    (hc : ∃ c ∈ P, 4 ∣ orderOf c) :
    ⁅P.map (MulAut.conj x).toMonoidHom, P.map (MulAut.conj x).toMonoidHom⁆ =
        P.map (MulAut.conj x).toMonoidHom ∧
      ∃ c ∈ P.map (MulAut.conj x).toMonoidHom, 4 ∣ orderOf c := by
  refine ⟨by rw [← Subgroup.map_commutator, hP], ?_⟩
  obtain ⟨c, hcP, h4⟩ := hc
  exact ⟨x * c * x⁻¹, ⟨c, hcP, rfl⟩, by rw [orderOf_conj_J]; exact h4⟩

theorem fixed_of_perfect' {K A : Type*} [Group K] [Group A] (π : K →* A) (y : MulAut K)
    (hker : π.ker ≤ Subgroup.center K) {D : Subgroup K} (hD : ⁅D, D⁆ = D)
    (hy : ∀ k ∈ D, π (y k) = π k) : ∀ k ∈ D, y k = k :=
  fixed_of_perfect y π hker hD hy

theorem exists_perfect_fixed_of_fixes_z
    (β : MulAut J) (hβ : β * β = 1) (hz : β lyz = lyz) (hβ1 : β ≠ 1) :
    ∃ P : Subgroup J, ⁅P, P⁆ = P ∧ (∀ p ∈ P, β p = p) ∧ ∃ c ∈ P, 4 ∣ orderOf c := by
  classical
  have hβ0 : (restrictC ⟨β, mem_autZ.2 hz⟩ : MulAut lyC) * restrictC ⟨β, mem_autZ.2 hz⟩ = 1 := by
    rw [← map_mul]
    have : (⟨β, mem_autZ.2 hz⟩ : autZ) * ⟨β, mem_autZ.2 hz⟩ = 1 := Subtype.ext hβ
    rw [this, map_one]
  obtain ⟨σ, hσ, hy⟩ := exists_sigma_of_aut lyCenterEquiv (restrictC ⟨β, mem_autZ.2 hz⟩) hβ0
  set β₀ : MulAut lyC := restrictC ⟨β, mem_autZ.2 hz⟩ with hβ₀def
  have hβ₀apply : ∀ k : lyC, ((β₀ k : lyC) : J) = β (k : J) := fun k => restrictC_apply _ k
  set π := projAlt lyCenterEquiv with hπdef
  have hπ : Function.Surjective π := projAlt_surjective lyCenterEquiv
  have hkerz : π.ker = zGroup := (ker_projAlt lyCenterEquiv).trans center_lyC
  have hker : π.ker ≤ Subgroup.center lyC := by rw [hkerz, center_lyC]
  have hK2 : IsPGroup 2 π.ker := by
    rw [hkerz]
    exact IsPGroup.of_card (n := 1) (by rw [zGroup, Nat.card_zpowers, orderOf_zC]; norm_num)
  have hne : π.ker ≠ ⊥ := by
    intro h
    have : zC ∈ π.ker := by rw [hkerz]; exact mem_zGroup.2 (Or.inr rfl)
    rw [h, Subgroup.mem_bot] at this
    have h2 := orderOf_zC
    rw [this, orderOf_one] at h2
    omega
  have hperfTop : ⁅(⊤ : Subgroup lyC), (⊤ : Subgroup lyC)⁆ = (⊤ : Subgroup lyC) := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  clear_value β₀ π
  by_cases hσ1 : σ = 1
  ·
    subst hσ1
    have hπβ : ∀ k ∈ (⊤ : Subgroup lyC), π (β₀ k) = π k := fun k _ => by
      apply Subtype.ext
      rw [hy k]
      simp
    have hfix : ∀ k ∈ (⊤ : Subgroup lyC), β₀ k = k :=
      fixed_of_perfect' π β₀ hker hperfTop hπβ
    obtain ⟨hperf, c, hc, h4⟩ := lyC_perfect_order4
    refine ⟨lyC, hperf, fun p hp => ?_, ⟨c, hc, h4⟩⟩
    have := congrArg Subtype.val (hfix ⟨p, hp⟩ trivial)
    rwa [hβ₀apply] at this
  · by_cases hσA : σ ∈ alternatingGroup (Fin 11)
    ·
      obtain ⟨c, hc⟩ := hπ ⟨σ, hσA⟩
      have hcσ : ((π c : alternatingGroup (Fin 11)) : Perm (Fin 11)) = σ := by rw [hc]
      have hβ0c : ∀ k : lyC, β₀ k = c * k * c⁻¹ := by
        have hγ : ∀ k ∈ (⊤ : Subgroup lyC), π ((MulAut.conj c⁻¹ * β₀) k) = π k := by
          intro k _
          have h1 : (MulAut.conj c⁻¹ * β₀) k = c⁻¹ * β₀ k * c := by
            rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
          apply Subtype.ext
          rw [h1, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcσ,
            hy k]
          group
        intro k
        have h := fixed_of_perfect (MulAut.conj c⁻¹ * β₀) π hker (D := ⊤) hperfTop hγ k trivial
        rw [MulAut.mul_apply, MulAut.conj_apply] at h
        calc β₀ k = c * (c⁻¹ * β₀ k * c⁻¹⁻¹) * c⁻¹ := by group
          _ = c * k * c⁻¹ := by rw [h]
      have hβc : ∀ x ∈ lyC, β x = (c : J) * x * (c : J)⁻¹ := by
        intro x hx
        have h1 := congrArg Subtype.val (hβ0c ⟨x, hx⟩)
        rw [hβ₀apply] at h1
        simpa using h1
      have hγ' : ∀ x ∈ lyC, (MulAut.conj (c : J)⁻¹ * β) x = x := by
        intro x hx
        rw [MulAut.mul_apply, MulAut.conj_apply, hβc x hx]
        group
      obtain ⟨t, hβt⟩ : ∃ t : J, β = MulAut.conj t := by
        have hrw : β = MulAut.conj (c : J) * (MulAut.conj (c : J)⁻¹ * β) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
        rcases fixes_C_cases hγ' with h | h
        · exact ⟨(c : J), by rw [hrw, h, mul_one]⟩
        · exact ⟨(c : J) * lyz, by rw [hrw, h, map_mul]⟩
      have htt : t * t = 1 := by
        have h1 : MulAut.conj (t * t) = 1 := by rw [map_mul, ← hβt]; exact hβ
        have hcenter : t * t ∈ Subgroup.center J := by
          rw [Subgroup.mem_center_iff]
          intro g
          have := congrArg (fun γ : MulAut J => γ g) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at this
          calc g * (t * t) = ((t * t) * g * (t * t)⁻¹) * (t * t) := by rw [this]
            _ = (t * t) * g := by group
        rw [center_J_eq_bot] at hcenter
        exact Subgroup.mem_bot.1 hcenter
      have ht1 : t ≠ 1 := fun h => hβ1 (by rw [hβt, h, map_one])
      have ht2 : orderOf t = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [sq]; exact htt) ht1
      obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 t ht2
      obtain ⟨hperf, c₀, hc₀, h4⟩ := lyC_perfect_order4
      obtain ⟨hperf', c', hc', h4'⟩ := perfect_map_conj x hperf ⟨c₀, hc₀, h4⟩
      refine ⟨lyC.map (MulAut.conj x).toMonoidHom, hperf', ?_, c', hc', h4'⟩
      rintro _ ⟨p, hp, rfl⟩
      have hpc : p * lyz = lyz * p := by
        have h : p ∈ lyC := hp
        rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at h
        exact h
      have hpc' : lyz * p * lyz⁻¹ = p := by
        calc lyz * p * lyz⁻¹ = p * lyz * lyz⁻¹ := by rw [hpc]
          _ = p := by group
      show β (x * p * x⁻¹) = x * p * x⁻¹
      rw [hβt, MulAut.conj_apply, ← hx]
      calc x * lyz * x⁻¹ * (x * p * x⁻¹) * (x * lyz * x⁻¹)⁻¹ = x * (lyz * p * lyz⁻¹) * x⁻¹ := by group
        _ = x * p * x⁻¹ := by rw [hpc']
    ·
      obtain ⟨D, hDperf, hDfix, k, hkD, hk4⟩ :=
        exists_fixed_perfect_order_four_lift π hπ hker hK2 hne β₀ σ hy (badCent_of_odd hσ hσA)
      refine ⟨D.map lyC.subtype, ?_, ?_, (k : J), ⟨k, hkD, rfl⟩, ?_⟩
      · rw [← Subgroup.map_commutator, hDperf]
      · rintro _ ⟨d, hd, rfl⟩
        have := congrArg Subtype.val (hDfix d hd)
        rwa [hβ₀apply] at this
      · rw [Subgroup.orderOf_coe]
        exact hk4

theorem exists_perfect_fixed_J
    (β : MulAut J) (hβ : β * β = 1) (hβ1 : β ≠ 1) :
    ∃ P : Subgroup J, ⁅P, P⁆ = P ∧ (∀ p ∈ P, β p = p) ∧ ∃ c ∈ P, 4 ∣ orderOf c := by
  have hβ' : ∀ x : J, (β : J →* J) ((β : J →* J) x) = x := fun x => by
    have h := congrArg (fun γ : MulAut J => γ x) hβ
    simpa using h
  obtain ⟨t, ht2, hβt⟩ := exists_fixed_involution_of_odd (β : J →* J) hβ'
    (by rw [card_involutions_J]; exact ⟨648413437, by norm_num⟩)
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 t ht2
  set β' : MulAut J := MulAut.conj x⁻¹ * β * MulAut.conj x with hβ'def
  have hconj : ∀ v : J, β' v = x⁻¹ * β (x * v * x⁻¹) * x := fun v => by
    rw [hβ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
    simp
  have hβ'z : β' lyz = lyz := by
    rw [hconj, hx]
    have : β t = t := hβt
    rw [this, ← hx]
    group
  have hβ'2 : β' * β' = 1 := by
    ext v
    rw [MulAut.mul_apply, MulAut.one_apply, hconj, hconj]
    have h1 : x * (x⁻¹ * β (x * v * x⁻¹) * x) * x⁻¹ = β (x * v * x⁻¹) := by group
    rw [h1]
    have h2 : β (β (x * v * x⁻¹)) = x * v * x⁻¹ := hβ' _
    rw [h2]
    group
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply]
    have e : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
    have h1 : β' (x⁻¹ * w * x) = x⁻¹ * w * x := by rw [h, MulAut.one_apply]
    rw [hconj, e] at h1
    calc β w = x * (x⁻¹ * β w * x) * x⁻¹ := by group
      _ = x * (x⁻¹ * w * x) * x⁻¹ := by rw [h1]
      _ = w := e
  obtain ⟨P, hPperf, hPfix, c, hcP, h4⟩ := exists_perfect_fixed_of_fixes_z β' hβ'2 hβ'z hβ'1
  obtain ⟨hperf', c', hc', h4'⟩ := perfect_map_conj x hPperf ⟨c, hcP, h4⟩
  refine ⟨P.map (MulAut.conj x).toMonoidHom, hperf', ?_, c', hc', h4'⟩
  rintro _ ⟨p, hp, rfl⟩
  show β (x * p * x⁻¹) = x * p * x⁻¹
  calc β (x * p * x⁻¹) = x * (x⁻¹ * β (x * p * x⁻¹) * x) * x⁻¹ := by group
    _ = x * (β' p) * x⁻¹ := by rw [hconj p]
    _ = x * p * x⁻¹ := by rw [hPfix p hp]

theorem exists_perfect_fixed_of_equiv
    {S : Type} [Group S] (e : S ≃* CFSG.Blueprint.NativeSporadic.Ly)
    (α : MulAut S) (hα : α * α = 1) (hα1 : α ≠ 1) :
    ∃ P : Subgroup S, ⁅P, P⁆ = P ∧ (∀ p ∈ P, α p = p) ∧ ∃ c ∈ P, 4 ∣ orderOf c := by
  let θ : S ≃* J := e.trans lyEquivJ
  have hαα : ∀ x : S, α (α x) = x := fun x => by
    have h := congrArg (fun γ : MulAut S => γ x) hα
    simpa [pow_two] using h
  let β : MulAut J := θ.symm.trans (α.trans θ)
  have hβ : ∀ x : J, β x = θ (α (θ.symm x)) := fun x => rfl
  have hβ2 : β * β = 1 := by
    ext x
    rw [MulAut.mul_apply, MulAut.one_apply, hβ, hβ, MulEquiv.symm_apply_apply, hαα,
      MulEquiv.apply_symm_apply]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    refine MulEquiv.ext fun x => ?_
    rw [MulAut.one_apply]
    have h1 : β (θ x) = θ x := by rw [h, MulAut.one_apply]
    rw [hβ, MulEquiv.symm_apply_apply] at h1
    exact θ.injective h1
  obtain ⟨P, hPperf, hPfix, c, hcP, h4⟩ := exists_perfect_fixed_J β hβ2 hβ1
  let f : J →* S := (θ.symm : J →* S)
  have hfinj : Function.Injective f := θ.symm.injective
  refine ⟨P.map f, ?_, ?_, f c, ⟨c, hcP, rfl⟩, ?_⟩
  · rw [← Subgroup.map_commutator, hPperf]
  · rintro _ ⟨q, hq, rfl⟩
    have h1 := hPfix q hq
    rw [hβ] at h1
    have h2 := congrArg θ.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  · rw [orderOf_injective f hfinj c]
    exact h4

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
