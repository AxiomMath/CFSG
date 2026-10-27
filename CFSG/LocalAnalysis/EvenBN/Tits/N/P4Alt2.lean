module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Y
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup
open scoped Pointwise

variable {Γ : Type*} [Group Γ]

@[expose] def EA (A : Subgroup Γ) : Prop := (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a * a = 1

theorem EA_zpowers {t : Γ} (ht : t * t = 1) : EA (zpowers t) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow_self t m n).eq
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_add, ← two_mul, zpow_mul]
    have : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
    rw [this, one_zpow]

theorem EA_sup {A B : Subgroup Γ} (hA : EA A) (hB : EA B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    EA (A ⊔ B) := by
  have hN : A ≤ normalizer (B : Set Γ) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro b hb
    exact (hAB a ha b hb).symm
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hN
  have key : ∀ g ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, g = a * b := by
    intro g hg
    have : g ∈ ((A : Set Γ) * (B : Set Γ)) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, rfl⟩ := this
    exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨fun g hg g' hg' => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := key g hg
    obtain ⟨a', ha', b', hb', rfl⟩ := key g' hg'
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [hA.1 a ha a' ha', hB.1 b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := key g hg
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hAB a ha b hb]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [hA.2 a ha, hB.2 b hb, one_mul]

theorem EA_map_conj {A : Subgroup Γ} (hA : EA A) (h : Γ) :
    EA (A.map (MulAut.conj h).toMonoidHom) := by
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ := by group
      _ = h * (y * x) * h⁻¹ := by rw [hA.1 x hx y hy]
      _ = h * y * h⁻¹ * (h * x * h⁻¹) := by group
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * x * h⁻¹ * (h * x * h⁻¹) = h * (x * x) * h⁻¹ := by group
      _ = 1 := by rw [hA.2 x hx]; group

theorem card_map_conj (A : Subgroup Γ) (h : Γ) :
    Nat.card (A.map (MulAut.conj h).toMonoidHom) = Nat.card A :=
  (Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj h).toMonoidHom
    (MulAut.conj h).injective).toEquiv).symm

theorem eq_one_or_eq_of_mem_zpowers {t a : Γ} (ht : t * t = 1) (ha : a ∈ zpowers t) :
    a = 1 ∨ a = t := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ht
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem decomp_J {U : Subgroup Γ} {t β : Γ} (htt : t * t = 1) (hββ : β * β = 1) (hβt : β * t = t * β)
    (htU : ∀ u ∈ U, t * u = u * t) (hβU : ∀ u ∈ U, β * u = u * β) {j : Γ}
    (hj : j ∈ (zpowers t ⊔ zpowers β) ⊔ U) :
    ∃ t' b' u : Γ, (t' = 1 ∨ t' = t) ∧ (b' = 1 ∨ b' = β) ∧ u ∈ U ∧ j = t' * b' * u := by
  have hZ0 : ∀ a ∈ zpowers t, ∀ b ∈ zpowers β, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute t β from hβt.symm) m n).eq
  have hN1 : zpowers t ≤ normalizer ((zpowers β : Subgroup Γ) : Set Γ) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro b hb
    exact (hZ0 a ha b hb).symm
  have hset1 := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) (zpowers β) hN1
  have hZ0U : ∀ c ∈ zpowers t ⊔ zpowers β, ∀ u ∈ U, c * u = u * c := by
    have hle : zpowers t ⊔ zpowers β ≤ centralizer (U : Set Γ) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · rw [mem_centralizer_iff]
        intro u hu
        exact (htU u hu).symm
      · rw [mem_centralizer_iff]
        intro u hu
        exact (hβU u hu).symm
    intro c hc u hu
    exact (mem_centralizer_iff.1 (hle hc) u hu).symm
  have hN2 : zpowers t ⊔ zpowers β ≤ normalizer (U : Set Γ) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro u hu
    exact (hZ0U c hc u hu).symm
  have hset2 := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t ⊔ zpowers β) U hN2
  have hj' : j ∈ (((zpowers t ⊔ zpowers β : Subgroup Γ) : Set Γ) * (U : Set Γ)) := by
    rw [← hset2]
    exact hj
  obtain ⟨c, hc, u, hu, rfl⟩ := hj'
  have hc' : c ∈ ((zpowers t : Set Γ) * (zpowers β : Set Γ)) := by
    rw [← hset1]
    exact hc
  obtain ⟨t', ht', b', hb', rfl⟩ := hc'
  refine ⟨t', b', u, eq_one_or_eq_of_mem_zpowers htt ht', eq_one_or_eq_of_mem_zpowers hββ hb', hu, rfl⟩

section Module

variable {L : Type*} [Group L]

theorem J1 (hcomm : ∀ a b : L, a * b = b * a) {Z1 E : Subgroup L} {U : Subgroup (MulAut L)}
    {t β : MulAut L} (htt : t * t = 1) (hββ : β * β = 1) (hβt : β * t = t * β)
    (htU : ∀ u ∈ U, t * u = u * t) (hβU : ∀ u ∈ U, β * u = u * β)
    (hβZ : ∀ l, β l * l⁻¹ ∈ Z1) (hZ1E : Z1 ≤ E)
    (htE : ∀ l, t l * l⁻¹ ∈ E) (htEfix : ∀ e ∈ E, t e = e) (htsurj : ∀ e ∈ E, ∃ l, t l * l⁻¹ = e)
    (hUE : ∀ u ∈ U, (∀ e ∈ E, u e = e) → u = 1) (hE : ∃ e ∈ E, e ∉ Z1) {j : MulAut L}
    (hj : j ∈ (zpowers t ⊔ zpowers β) ⊔ U) (hjZ : ∀ l, j l * l⁻¹ ∈ Z1) : j ∈ zpowers β := by
  obtain ⟨t', b', u, ht', hb', hu, rfl⟩ := decomp_J htt hββ hβt htU hβU hj
  have hb'Z : ∀ l, b'⁻¹ l * l⁻¹ ∈ Z1 := by
    intro l
    rcases hb' with h | h
    · rw [h]; simp
    · have : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
      rw [h, this]
      exact hβZ l
  have hb'u : b' * u = u * b' := by
    rcases hb' with h | h
    · rw [h]; simp
    · rw [h]; exact hβU u hu
  have hjg : t' * b' * u = (t' * u) * b' := by
    calc t' * b' * u = t' * (b' * u) := by group
      _ = t' * (u * b') := by rw [hb'u]
      _ = (t' * u) * b' := by group
  have hgZ : ∀ l, (t' * u) l * l⁻¹ ∈ Z1 := by
    intro l
    have h1 : (t' * u * b') (b'⁻¹ l) = (t' * u) l := by
      simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    have e : (t' * u) l * l⁻¹ =
        ((t' * u * b') (b'⁻¹ l) * (b'⁻¹ l)⁻¹) * (b'⁻¹ l * l⁻¹) := by
      rw [h1]; group
    rw [e]
    have := hjZ (b'⁻¹ l)
    rw [hjg] at this
    exact Z1.mul_mem this (hb'Z l)
  have hgt : t * (t' * u) = (t' * u) * t := by
    rcases ht' with h | h
    · rw [h]; simp [htU u hu]
    · rw [h]
      calc t * (t * u) = (t * t) * u := by group
        _ = u := by rw [htt, one_mul]
        _ = (t * u) * t := by rw [mul_assoc, ← htU u hu, ← mul_assoc, htt, one_mul]
  have hgE : ∀ e ∈ E, (t' * u) e = e := by
    intro e he
    obtain ⟨l, hl⟩ := htsurj e he
    obtain ⟨ζ, hζ, hζdef⟩ : ∃ ζ ∈ Z1, (t' * u) l = ζ * l := ⟨(t' * u) l * l⁻¹, hgZ l, by group⟩
    have htl : t l = e * l := by rw [← hl]; group
    have h1 : (t' * u) (t l) = t ((t' * u) l) := by
      have := congrArg (fun φ : MulAut L => φ l) hgt
      exact this.symm
    rw [htl, map_mul, hζdef, map_mul, htEfix ζ (hZ1E hζ), htl] at h1
    have h3 : (t' * u) e * ζ * l = ζ * (e * l) := by
      rw [← h1]
      group
    have h4 : (t' * u) e * ζ * l = (e * ζ) * l := by
      rw [h3, ← mul_assoc, hcomm ζ e]
    have h2 : (t' * u) e * ζ = e * ζ := mul_right_cancel h4
    exact mul_right_cancel h2
  have huE : ∀ e ∈ E, u e = e := by
    intro e he
    rcases ht' with h | h
    · rw [h] at hgE
      simpa using hgE e he
    · rw [h] at hgE
      have := hgE e he
      simp only [MulAut.mul_apply] at this
      have h2 : u e = t⁻¹ e := by
        calc u e = t⁻¹ (t (u e)) := by simp
          _ = t⁻¹ e := by rw [this]
      have ht'' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
      rw [h2, ht'']
      exact htEfix e he
  have hu1 : u = 1 := hUE u hu huE
  rw [hu1] at hgZ ⊢
  rcases ht' with h | h
  · rcases hb' with h' | h'
    · rw [h, h']; simp
    · rw [h, h']; simpa using mem_zpowers β
  · exfalso
    obtain ⟨e, he, heZ⟩ := hE
    obtain ⟨l, hl⟩ := htsurj e he
    apply heZ
    rw [← hl]
    have := hgZ l
    rw [h] at this
    simpa using this

theorem J2 {E E0 : Subgroup L} {U : Subgroup (MulAut L)} {t β : MulAut L}
    (htt : t * t = 1) (hββ : β * β = 1) (hβt : β * t = t * β)
    (htU : ∀ u ∈ U, t * u = u * t) (hβU : ∀ u ∈ U, β * u = u * β) (hEE0 : E ≤ E0)
    (htβ : ∀ e ∈ E0, (t * β) e = e) (he₀ : ∃ e₀ ∈ E0, t e₀ ≠ e₀ ∧ ∀ u ∈ U, u e₀ = e₀)
    (hUE : ∀ u ∈ U, (∀ e ∈ E, u e = e) → u = 1) {j : MulAut L}
    (hj : j ∈ (zpowers t ⊔ zpowers β) ⊔ U) (hjE : ∀ e ∈ E0, j e = e) : j ∈ zpowers (t * β) := by
  obtain ⟨t', b', u, ht', hb', hu, rfl⟩ := decomp_J htt hββ hβt htU hβU hj
  obtain ⟨e₀, he₀E, hte₀, hue₀⟩ := he₀
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hβe : ∀ e ∈ E0, β e = t e := by
    intro e he
    have h1 : t (β e) = e := htβ e he
    calc β e = t⁻¹ (t (β e)) := by simp
      _ = t e := by rw [h1, htinv]
  rcases ht' with h | h <;> rcases hb' with h' | h'
  · rw [h, h'] at hjE ⊢
    have hu1 : u = 1 := hUE u hu (fun e he => by simpa using hjE e (hEE0 he))
    rw [hu1]
    simpa using one_mem (zpowers (t * β))
  · exfalso
    rw [h, h'] at hjE
    have h1 := hjE e₀ he₀E
    simp only [MulAut.mul_apply, MulAut.one_apply, hue₀ u hu] at h1
    exact hte₀ (by rw [← hβe e₀ he₀E]; exact h1)
  · exfalso
    rw [h, h'] at hjE
    have h1 := hjE e₀ he₀E
    simp only [MulAut.mul_apply, MulAut.one_apply, hue₀ u hu] at h1
    exact hte₀ h1
  · rw [h, h'] at hjE ⊢
    have hu1 : u = 1 := by
      apply hUE u hu
      intro e he
      have h1 := hjE e (hEE0 he)
      have h2 : (t * β) (u e) = e := h1
      have h3 : (t * β) e = e := htβ e (hEE0 he)
      have h4 : (t * β) (u e) = (t * β) e := by rw [h2, h3]
      exact (t * β).injective h4
    rw [hu1]
    simpa using mem_zpowers (t * β)

theorem alt2_false [Finite L] (hcomm : ∀ a b : L, a * b = b * a)
    {Z1 E E0 : Subgroup L} {z : L} (hz : Z1 = zpowers z) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hZ1E : Z1 ≤ E) (hEE0 : E ≤ E0)
    {U : Subgroup (MulAut L)} {x v t β : MulAut L} (hF : IsF20 U x v) (Hs : Subgroup (MulAut L))
    (htt : t * t = 1) (htP : ∀ p ∈ IsF20.Pgrp U x v, t * p = p * t)
    (htinf : zpowers t ⊓ IsF20.Pgrp U x v = ⊥)
    (hββ : β * β = 1) (hβ1 : β ≠ 1) (hβt : β * t = t * β)
    (hβP : ∀ p ∈ IsF20.Pgrp U x v, β * p = p * β)
    (hβinf : zpowers β ⊓ (zpowers t ⊔ IsF20.Pgrp U x v) = ⊥)
    (hC : centralizer ({t} : Set (MulAut L)) ⊓ Hs = (zpowers t ⊔ IsF20.Pgrp U x v) ⊔ zpowers β)
    (hUZ : ∀ u ∈ U, ∀ ζ ∈ Z1, u ζ = ζ)
    (hM1 : ∀ l : L, (∀ g ∈ U ⊔ zpowers t, g l = l) → l ∈ Z1)
    (hM2 : ∀ l : L, (∀ g ∈ U ⊔ zpowers t, g l * l⁻¹ ∈ Z1) ↔ l ∈ E0)
    (hβZ : ∀ l, β l * l⁻¹ ∈ Z1)
    (htE : ∀ l, t l * l⁻¹ ∈ E) (htEfix : ∀ e ∈ E, t e = e) (htsurj : ∀ e ∈ E, ∃ l, t l * l⁻¹ = e)
    (hUE : ∀ u ∈ U, (∀ e ∈ E, u e = e) → u = 1) (hE : ∃ e ∈ E, e ∉ Z1)
    (htβ : ∀ e ∈ E0, (t * β) e = e) (he₀ : ∃ e₀ ∈ E0, t e₀ ≠ e₀ ∧ ∀ u ∈ U, u e₀ = e₀)
    (hfus : ∃ h ∈ Hs, ∃ u₀ ∈ U, u₀ ≠ 1 ∧ h * t * h⁻¹ = t * u₀) : False := by
  classical
  haveI : Finite (MulAut L) :=
    Finite.of_injective (fun e : MulAut L => e.toEquiv) MulEquiv.toEquiv_injective
  set P := IsF20.Pgrp U x v with hP
  have hUP : U ≤ P := IsF20.U_le_Pgrp U x v
  have htU : ∀ u ∈ U, t * u = u * t := fun u hu => htP u (hUP hu)
  have hβU : ∀ u ∈ U, β * u = u * β := fun u hu => hβP u (hUP hu)
  set Z0 : Subgroup (MulAut L) := zpowers t ⊔ zpowers β with hZ0
  have hEAt : EA (zpowers t) := EA_zpowers htt
  have hEAβ : EA (zpowers β) := EA_zpowers hββ
  have hZ0c : ∀ a ∈ zpowers t, ∀ b ∈ zpowers β, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute t β from hβt.symm) m n).eq
  have hEAZ0 : EA Z0 := EA_sup hEAt hEAβ hZ0c
  have hZ0P : ∀ a ∈ Z0, ∀ p ∈ P, a * p = p * a := by
    have hle : Z0 ≤ centralizer (P : Set (MulAut L)) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · rw [mem_centralizer_iff]
        intro p hp
        exact (htP p hp).symm
      · rw [mem_centralizer_iff]
        intro p hp
        exact (hβP p hp).symm
    intro a ha p hp
    exact (mem_centralizer_iff.1 (hle ha) p hp).symm
  have hZ0inf : Z0 ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    obtain ⟨hcZ, hcP⟩ := Subgroup.mem_inf.1 hc
    have hN1 : zpowers t ≤ normalizer ((zpowers β : Subgroup (MulAut L)) : Set (MulAut L)) := by
      intro a ha
      apply Subgroup.centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro b hb
      exact (hZ0c a ha b hb).symm
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers t) (zpowers β) hN1
    have hc' : c ∈ ((zpowers t : Set (MulAut L)) * (zpowers β : Set (MulAut L))) := by
      rw [← hset]
      exact hcZ
    obtain ⟨a, ha, b, hb, rfl⟩ := hc'
    have hcP' : a * b ∈ P := hcP
    show a * b ∈ (⊥ : Subgroup (MulAut L))
    have hb' : b ∈ zpowers β ⊓ (zpowers t ⊔ P) := by
      refine Subgroup.mem_inf.2 ⟨hb, ?_⟩
      have : b = a⁻¹ * (a * b) := by group
      rw [this]
      exact Subgroup.mul_mem _ (inv_mem (mem_sup_left ha)) (mem_sup_right hcP')
    rw [hβinf, Subgroup.mem_bot] at hb'
    rw [hb', mul_one] at hcP' ⊢
    have ha' : a ∈ zpowers t ⊓ P := Subgroup.mem_inf.2 ⟨ha, hcP'⟩
    rw [htinf] at ha'
    exact ha'
  have hEAU : EA U := ⟨hF.comm, hF.sq⟩
  set J : Subgroup (MulAut L) := Z0 ⊔ U with hJ
  have hEAJ : EA J := EA_sup hEAZ0 hEAU (fun a ha b hb => hZ0P a ha b (hUP hb))
  have hZ0U : Z0 ⊓ U = ⊥ := by
    rw [eq_bot_iff, ← hZ0inf]
    exact inf_le_inf_left Z0 hUP
  have hZ0N : Z0 ≤ normalizer (U : Set (MulAut L)) := by
    intro a ha
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro u hu
    exact (hZ0P a ha u (hUP hu)).symm
  have hJcard : Nat.card J = 16 * Nat.card Z0 := by
    have := card_sup_mul_card_inf' hZ0N
    rw [hZ0U, Subgroup.card_bot, mul_one, hF.card] at this
    rw [this]
    ring
  have hC' : centralizer ({t} : Set (MulAut L)) ⊓ Hs = Z0 ⊔ P := by
    rw [hC]
    exact sup_right_comm _ _ _
  have hJle : J ≤ centralizer ({t} : Set (MulAut L)) ⊓ Hs := by
    rw [hC']
    exact sup_le_sup_left hUP _
  have huniq : ∀ D : Subgroup (MulAut L), D ≤ centralizer ({t} : Set (MulAut L)) ⊓ Hs → EA D →
      Nat.card D = 16 * Nat.card Z0 → D = J := by
    intro D hD hDEA hDc
    rw [hC'] at hD
    exact (hF.card_elemAb_le_sup hZ0P hZ0inf hD hDEA.1 hDEA.2).2 hDc
  obtain ⟨h, hh, u₀, hu₀, hu₀1, hht⟩ := hfus
  have hsJ : t * u₀ ∈ J :=
    Subgroup.mul_mem _ (mem_sup_left (mem_sup_left (mem_zpowers t))) (mem_sup_right hu₀)
  have hJ' : J.map (MulAut.conj h⁻¹).toMonoidHom ≤ centralizer ({t} : Set (MulAut L)) ⊓ Hs := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hjs : j * (t * u₀) = (t * u₀) * j := hEAJ.1 j hj _ hsJ
      calc h⁻¹ * j * h * t = h⁻¹ * (j * (h * t * h⁻¹)) * h := by group
        _ = h⁻¹ * (j * (t * u₀)) * h := by rw [hht]
        _ = h⁻¹ * ((t * u₀) * j) * h := by rw [hjs]
        _ = t * (h⁻¹ * j * h) := by rw [← hht]; group
    · exact Hs.mul_mem (Hs.mul_mem (Hs.inv_mem hh) (hJle hj).2) hh
  have hJ'eq : J.map (MulAut.conj h⁻¹).toMonoidHom = J :=
    huniq _ hJ' (EA_map_conj hEAJ h⁻¹) (by rw [card_map_conj, hJcard])
  have hhN : h ∈ normalizer (J : Set (MulAut L)) := by
    have : h⁻¹ ∈ normalizer (J : Set (MulAut L)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 hJ'eq
    simpa using inv_mem this
  have hnJ : ∀ g ∈ J, h⁻¹ * g * h ∈ J := fun g hg => (mem_normalizer_iff''.1 hhN g).1 hg
  have hnJ' : ∀ g ∈ J, h * g * h⁻¹ ∈ J := fun g hg => (mem_normalizer_iff.1 hhN g).1 hg
  have hU0J : U ⊔ zpowers t ≤ J :=
    sup_le (fun u hu => mem_sup_right hu)
      (zpowers_le.2 (mem_sup_left (mem_sup_left (mem_zpowers t))))
  have htJ : t ∈ J := mem_sup_left (mem_sup_left (mem_zpowers t))
  have hβJ : β ∈ J := mem_sup_left (mem_sup_right (mem_zpowers β))
  have hzZ : z ∈ Z1 := by rw [hz]; exact mem_zpowers z
  have hzfix1 : ∀ w : L, w ∈ Z1 → ∀ g ∈ J, g w = w → True := fun _ _ _ _ _ => trivial
  have hβz : β z = z := by
    have h1 : β z * z⁻¹ ∈ zpowers z := hz ▸ hβZ z
    rcases eq_one_or_eq_of_mem_zpowers hzz h1 with h2 | h2
    · exact mul_inv_eq_one.1 h2
    · exfalso
      have h3 : β z = 1 := by
        calc β z = (β z * z⁻¹) * z := by group
          _ = z * z := by rw [h2]
          _ = 1 := hzz
      exact hz1 (β.injective (h3.trans (map_one β).symm))
  have hJz : ∀ g ∈ J, g z = z := by
    have hle : J ≤ MulAction.stabilizer (MulAut L) z := by
      refine sup_le (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)) (fun u hu => ?_)
      · exact (MulAction.mem_stabilizer_iff).2 (by simpa [MulAut.smul_def] using htEfix z (hZ1E hzZ))
      · exact (MulAction.mem_stabilizer_iff).2 (by simpa [MulAut.smul_def] using hβz)
      · exact (MulAction.mem_stabilizer_iff).2 (by simpa [MulAut.smul_def] using hUZ u hu z hzZ)
    intro g hg
    exact (MulAction.mem_stabilizer_iff.1 (hle hg))
  have hnz : h z = z := by
    have hfix : ∀ g ∈ J, g (h z) = h z := by
      intro g hg
      have := hJz _ (hnJ g hg)
      calc g (h z) = (h * (h⁻¹ * g * h)) z := by simp [mul_assoc]
        _ = h ((h⁻¹ * g * h) z) := rfl
        _ = h z := by rw [this]
    have hmem : h z ∈ Z1 := hM1 (h z) (fun g hg => hfix g (hU0J hg))
    rw [hz] at hmem
    rcases eq_one_or_eq_of_mem_zpowers hzz hmem with h1 | h1
    · exfalso
      exact hz1 (h.injective (h1.trans (map_one h).symm))
    · exact h1
  have hnZ : ∀ ζ ∈ Z1, h ζ = ζ := by
    intro ζ hζ
    rw [hz] at hζ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hζ
    rw [map_zpow, hnz]
  have hnZ' : ∀ ζ ∈ Z1, h⁻¹ ζ = ζ := by
    intro ζ hζ
    have := hnZ ζ hζ
    calc h⁻¹ ζ = h⁻¹ (h ζ) := by rw [this]
      _ = ζ := by simp
  have hβ' : h * β * h⁻¹ = β := by
    have hβ'J : h * β * h⁻¹ ∈ J := hnJ' β hβJ
    have hβ'Z : ∀ l, (h * β * h⁻¹) l * l⁻¹ ∈ Z1 := by
      intro l
      have := hβZ (h⁻¹ l)
      have h2 : (h * β * h⁻¹) l * l⁻¹ = h (β (h⁻¹ l) * (h⁻¹ l)⁻¹) := by
        simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
      rw [h2, hnZ _ this]
      exact this
    have hmem := J1 hcomm htt hββ hβt htU hβU hβZ hZ1E htE htEfix htsurj hUE hE hβ'J hβ'Z
    rcases eq_one_or_eq_of_mem_zpowers hββ hmem with h2 | h2
    · exfalso
      apply hβ1
      have : h⁻¹ * (h * β * h⁻¹) * h = β := by group
      rw [← this, h2]
      group
    · exact h2
  have hJT : J ≤ trivOn Z1 E0 (hZ1E.trans hEE0) := by
    have hZ1E0 : Z1 ≤ E0 := hZ1E.trans hEE0
    refine sup_le (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)) (fun u hu => ?_)
    · rw [mem_trivOn]
      intro c hc
      exact (hM2 c).2 hc t (mem_sup_right (mem_zpowers t))
    · rw [mem_trivOn]
      intro c _
      exact hβZ c
    · rw [mem_trivOn]
      intro c hc
      exact (hM2 c).2 hc u (mem_sup_left hu)
  have hnE0 : ∀ l ∈ E0, h l ∈ E0 := by
    intro l hl
    apply (hM2 (h l)).1
    intro g hg
    have hg' : h⁻¹ * g * h ∈ J := hnJ g (hU0J hg)
    have h1 := mem_trivOn.1 (hJT hg') l hl
    have h2 : g (h l) * (h l)⁻¹ = h ((h⁻¹ * g * h) l * l⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [h2, hnZ _ h1]
    exact h1
  have hnE0' : ∀ l ∈ E0, h⁻¹ l ∈ E0 := by
    intro l hl
    apply (hM2 (h⁻¹ l)).1
    intro g hg
    have hg' : h * g * h⁻¹ ∈ J := hnJ' g (hU0J hg)
    have h1 := mem_trivOn.1 (hJT hg') l hl
    have h2 : g (h⁻¹ l) * (h⁻¹ l)⁻¹ = h⁻¹ ((h * g * h⁻¹) l * l⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self, MulAut.inv_apply_self]
    rw [h2, hnZ' _ h1]
    exact h1
  have htβJ : t * β ∈ J := Subgroup.mul_mem _ htJ hβJ
  have htβ1 : t * β ≠ 1 := by
    intro h1
    have hβt' : β = t := by
      have : β = t⁻¹ := (eq_inv_of_mul_eq_one_right h1)
      rw [this]
      exact inv_eq_of_mul_eq_one_right htt
    apply hβ1
    have hb : β ∈ zpowers β ⊓ (zpowers t ⊔ P) :=
      Subgroup.mem_inf.2 ⟨mem_zpowers β, mem_sup_left (by rw [hβt']; exact mem_zpowers t)⟩
    rw [hβinf, Subgroup.mem_bot] at hb
    exact hb
  have htβ' : h * (t * β) * h⁻¹ = t * β := by
    have hJ'' : h * (t * β) * h⁻¹ ∈ J := hnJ' _ htβJ
    have hfixE : ∀ e ∈ E0, (h * (t * β) * h⁻¹) e = e := by
      intro e he
      have h1 : (t * β) (h⁻¹ e) = h⁻¹ e := htβ _ (hnE0' e he)
      simp only [MulAut.mul_apply]
      have h2 : t (β (h⁻¹ e)) = h⁻¹ e := h1
      rw [h2]
      simp
    have hmem := J2 htt hββ hβt htU hβU hEE0 htβ he₀ hUE hJ'' hfixE
    rcases eq_one_or_eq_of_mem_zpowers (show (t * β) * (t * β) = 1 by
        calc (t * β) * (t * β) = t * (β * t) * β := by group
          _ = t * (t * β) * β := by rw [hβt]
          _ = (t * t) * (β * β) := by group
          _ = 1 := by rw [htt, hββ, one_mul]) hmem with h2 | h2
    · exfalso
      apply htβ1
      have : h⁻¹ * (h * (t * β) * h⁻¹) * h = t * β := by group
      rw [← this, h2]
      group
    · exact h2
  have hht' : h * t * h⁻¹ = t := by
    calc h * t * h⁻¹ = (h * (t * β) * h⁻¹) * (h * β * h⁻¹)⁻¹ := by group
      _ = (t * β) * β⁻¹ := by rw [htβ', hβ']
      _ = t := by group
  rw [hht'] at hht
  exact hu₀1 (mul_left_cancel (a := t) (by simpa using hht)).symm

end Module

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
