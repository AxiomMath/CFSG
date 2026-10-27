module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open
open scoped Pointwise

variable {X : Type*} [Group X]

theorem centralizes_of_normal_sup {U O : Subgroup X} {t w g : X} (hO : O.Normal)
    (hOodd : Odd (Nat.card O)) (hU : IsElemAbelian 2 U) (hN : (U ⊔ O).Normal)
    (htU : ∀ u ∈ U, t * u = u * t) (hwt : w * t = t * w) (hwU : ∀ u ∈ U, w * u * w⁻¹ ∈ U)
    (hg : g * t * g⁻¹ = t * w) : ∀ u ∈ U, w * u * w⁻¹ = u := by
  intro u hu
  have hUO : ∀ a ∈ U, a ∈ O → a = 1 := by
    intro a haU haO
    have h2 : a ^ 2 = 1 := hU.2 a haU
    have hord2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have hordO : orderOf a ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨a, haO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h | h
    · exact orderOf_eq_one_iff.1 h
    · exfalso
      rw [h] at hordO
      exact (Nat.not_even_iff_odd.2 hOodd) (even_iff_two_dvd.2 hordO)
  have h1 : g⁻¹ * u * g ∈ U ⊔ O := by
    have := hN.conj_mem u (mem_sup_left hu) g⁻¹
    simpa using this
  obtain ⟨u₁, hu₁, o₁, ho₁, hdec⟩ : ∃ u₁ ∈ U, ∃ o₁ ∈ O, u₁ * o₁ = g⁻¹ * u * g := by
    have hset := Subgroup.mul_normal U O
    have : g⁻¹ * u * g ∈ (U : Set X) * (O : Set X) := by
      rw [← hset]
      exact h1
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 this
    exact ⟨a, ha, b, hb, hab⟩
  have ho₂ : t * o₁ * t⁻¹ ∈ O := hO.conj_mem o₁ ho₁ t
  have hguu : g * u₁ * g⁻¹ = u * (g * o₁ * g⁻¹)⁻¹ := by
    have : u = g * (u₁ * o₁) * g⁻¹ := by rw [hdec]; group
    calc g * u₁ * g⁻¹ = g * (u₁ * o₁) * g⁻¹ * (g * o₁ * g⁻¹)⁻¹ := by group
      _ = u * (g * o₁ * g⁻¹)⁻¹ := by rw [← this]
  have hr : (t * w) * u * (t * w)⁻¹ = (g * u₁ * g⁻¹) * (g * (t * o₁ * t⁻¹) * g⁻¹) := by
    rw [← hg]
    have e : g * t * g⁻¹ * u * (g * t * g⁻¹)⁻¹ = g * (t * (g⁻¹ * u * g) * t⁻¹) * g⁻¹ := by group
    rw [e, ← hdec]
    have e2 : t * (u₁ * o₁) * t⁻¹ = (t * u₁ * t⁻¹) * (t * o₁ * t⁻¹) := by group
    have e3 : t * u₁ * t⁻¹ = u₁ := by
      have := htU u₁ hu₁
      rw [this]; group
    rw [e2, e3]
    group
  have hl : (t * w) * u * (t * w)⁻¹ = w * u * w⁻¹ := by
    have h1' : t * w * u * (t * w)⁻¹ = t * (w * u * w⁻¹) * t⁻¹ := by group
    rw [h1']
    have := htU _ (hwU u hu)
    rw [this]
    group
  have hmain : w * u * w⁻¹ = u * ((g * o₁ * g⁻¹)⁻¹ * (g * (t * o₁ * t⁻¹) * g⁻¹)) := by
    rw [← hl, hr, hguu]
    group
  have hoO : (g * o₁ * g⁻¹)⁻¹ * (g * (t * o₁ * t⁻¹) * g⁻¹) ∈ O :=
    mul_mem (Subgroup.inv_mem _ (hO.conj_mem o₁ ho₁ g)) (hO.conj_mem _ ho₂ g)
  have hoU : (g * o₁ * g⁻¹)⁻¹ * (g * (t * o₁ * t⁻¹) * g⁻¹) ∈ U := by
    have e : (g * o₁ * g⁻¹)⁻¹ * (g * (t * o₁ * t⁻¹) * g⁻¹) = u⁻¹ * (w * u * w⁻¹) := by
      rw [hmain]; group
    rw [e]
    exact mul_mem (Subgroup.inv_mem _ hu) (hwU u hu)
  have h1o := hUO _ hoU hoO
  rw [h1o, mul_one] at hmain
  exact hmain

theorem eq_one_of_inverter_centralizes {U : Subgroup X} {x w : X} (hx5 : x ^ 5 = 1)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1)
    (hwx : w * x * w⁻¹ = x⁻¹) (hwc : ∀ u ∈ U, w * u * w⁻¹ = u) : ∀ u ∈ U, u = 1 := by
  intro u hu
  apply hfpf u hu
  have hu' : x * u * x⁻¹ ∈ U := hxU u hu
  have h1 : x⁻¹ * u * x = x * u * x⁻¹ := by
    have := hwc _ hu'
    calc x⁻¹ * u * x = (w * x * w⁻¹) * (w * u * w⁻¹) * (w * x⁻¹ * w⁻¹) := by
          rw [hwx, hwc u hu]
          have : w * x⁻¹ * w⁻¹ = x := by
            rw [show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group, hwx]; simp
          rw [this]
      _ = w * (x * u * x⁻¹) * w⁻¹ := by group
      _ = x * u * x⁻¹ := this
  have h2 : x ^ 2 * u = u * x ^ 2 := by
    rw [pow_two]
    calc x * x * u = x * (x * u * x⁻¹) * x := by group
      _ = x * (x⁻¹ * u * x) * x := by rw [h1]
      _ = u * (x * x) := by group
  have h3 : (x ^ 2) ^ 3 * u = u * (x ^ 2) ^ 3 := (Commute.pow_left (show Commute (x ^ 2) u from h2) 3).eq
  have h4 : (x ^ 2) ^ 3 = x := by
    rw [← pow_mul]
    calc x ^ (2 * 3) = x ^ 5 * x := by rw [← pow_succ]
      _ = x := by rw [hx5, one_mul]
  rw [h4] at h3
  calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [h3]
    _ = u := by group

theorem contra_of_normal {U O : Subgroup X} {x t w g : X} (hO : O.Normal) (hOodd : Odd (Nat.card O))
    (hU : IsElemAbelian 2 U) (hN : (U ⊔ O).Normal) (hUne : ∃ u ∈ U, u ≠ 1)
    (htU : ∀ u ∈ U, t * u = u * t) (hwt : w * t = t * w) (hwU : ∀ u ∈ U, w * u * w⁻¹ ∈ U)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hx5 : x ^ 5 = 1)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) (hwx : w * x * w⁻¹ = x⁻¹)
    (hg : g * t * g⁻¹ = t * w) : False := by
  obtain ⟨u, hu, hu1⟩ := hUne
  exact hu1 (eq_one_of_inverter_centralizes hx5 hxU hfpf hwx
    (centralizes_of_normal_sup hO hOodd hU hN htU hwt hwU hg) u hu)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
