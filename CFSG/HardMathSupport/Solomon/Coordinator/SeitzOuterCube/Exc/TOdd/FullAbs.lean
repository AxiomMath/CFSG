module

public import Mathlib.GroupTheory.OrderOfElement

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Group

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd

variable {G : Type*} [Group G]

abbrev layerOf (x : G) : Subgroup G :=
  ⁅Subgroup.centralizer ({x} : Set G), Subgroup.centralizer ({x} : Set G)⁆

abbrev torusOf (x : G) : Subgroup G :=
  Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (layerOf x : Set G)

theorem layerOf_le_centralizer (x : G) : layerOf x ≤ Subgroup.centralizer ({x} : Set G) :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    simp only [commutatorElement_def]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
      (Subgroup.inv_mem _ h₂)

theorem conj_mem_layerOf {x c d : G} (hc : c ∈ Subgroup.centralizer ({x} : Set G))
    (hd : d ∈ layerOf x) : c * d * c⁻¹ ∈ layerOf x := by
  have key : layerOf x ≤ (layerOf x).comap (MulAut.conj c).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    have hc₁ : c * g₁ * c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc h₁) (Subgroup.inv_mem _ hc)
    have hc₂ : c * g₂ * c⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc h₂) (Subgroup.inv_mem _ hc)
    have h := Subgroup.commutator_mem_commutator hc₁ hc₂
    have e : c * ⁅g₁, g₂⁆ * c⁻¹ = ⁅c * g₁ * c⁻¹, c * g₂ * c⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    simpa [Subgroup.mem_comap, e] using h
  simpa using key hd

theorem commute_of_mem_zpowers {x g w : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G))
    (hw : w ∈ Subgroup.zpowers x) : g * w = w * g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hxg : Commute x g := Subgroup.mem_centralizer_iff.1 hg x rfl
  exact (hxg.zpow_left k).symm.eq

theorem exists_mul_of_mem_sup {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {a : G}
    (ha : a ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, h * k = a := by
  let S : Subgroup G :=
    { carrier := {a | ∃ h ∈ H, ∃ k ∈ K, h * k = a}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
        have e := hc h₂ hh₂ k₁ hk₁
        calc h₁ * h₂ * (k₁ * k₂) = h₁ * (h₂ * k₁) * k₂ := by group
          _ = h₁ * (k₁ * h₂) * k₂ := by rw [e]
          _ = h₁ * k₁ * (h₂ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
        have e : Commute h k := hc h hh k hk
        rw [e.mul_inv] }
  have hHK : H ⊔ K ≤ S :=
    sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, mul_one h⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, one_mul k⟩)
  exact hHK ha

section Layer

variable [Finite G] {x : G}

theorem torus_central (hx3 : x ^ 3 = 1)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (layerOf x : Set G),
      (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x)
    {g t : G} (hg : g ∈ Subgroup.centralizer ({x} : Set G)) (ht : t ∈ torusOf x) :
    g * t = t * g := by
  have htC : t ∈ Subgroup.centralizer ({x} : Set G) := ht.1
  have htD : t ∈ Subgroup.centralizer (layerOf x : Set G) := ht.2
  set w : G := g * t * g⁻¹ * t⁻¹ with hw
  have hwD : w ∈ layerOf x := Subgroup.commutator_mem_commutator hg htC
  have hwcen : ∀ d ∈ layerOf x, w * d = d * w := by
    intro d hd
    have hd' : g⁻¹ * d * g⁻¹⁻¹ ∈ layerOf x :=
      conj_mem_layerOf (Subgroup.inv_mem _ hg) hd
    have h1 : (g⁻¹ * d * g⁻¹⁻¹) * t = t * (g⁻¹ * d * g⁻¹⁻¹) :=
      Subgroup.mem_centralizer_iff.1 htD _ hd'
    have h2 : d * t⁻¹ = t⁻¹ * d := by
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ htD) d hd
      exact this
    have h3 : d * (g * t * g⁻¹) = (g * t * g⁻¹) * d := by
      calc d * (g * t * g⁻¹) = g * ((g⁻¹ * d * g⁻¹⁻¹) * t) * g⁻¹ := by group
        _ = g * (t * (g⁻¹ * d * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
        _ = (g * t * g⁻¹) * d := by group
    calc w * d = (g * t * g⁻¹) * (t⁻¹ * d) := by rw [hw]; group
      _ = (g * t * g⁻¹) * (d * t⁻¹) := by rw [h2]
      _ = ((g * t * g⁻¹) * d) * t⁻¹ := by group
      _ = (d * (g * t * g⁻¹)) * t⁻¹ := by rw [h3]
      _ = d * w := by rw [hw]; group
  have hwx : w ∈ Subgroup.zpowers x := hZD w hwD hwcen
  have hwg : g * w = w * g := commute_of_mem_zpowers hg hwx
  have hwt : t * w = w * t := commute_of_mem_zpowers htC hwx
  have hw3 : w ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hwx
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  have hconj : ∀ n : ℕ, g * t ^ n * g⁻¹ = w ^ n * t ^ n := by
    intro n
    have hgt : g * t * g⁻¹ = w * t := by rw [hw]; group
    rw [← conj_pow, hgt]
    exact (Commute.mul_pow (hwt.symm : Commute w t) n)
  obtain ⟨k, m, hm3, hmk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos t).ne' 3 (by norm_num)
  have htm : t ^ m ∈ Subgroup.zpowers x := by
    refine hZ3 _ (Subgroup.pow_mem _ htD m) ⟨k, ?_⟩
    rw [← pow_mul, mul_comm, ← hmk]
    exact pow_orderOf_eq_one t
  have htmg : g * t ^ m * g⁻¹ = t ^ m := by
    rw [mul_inv_eq_iff_eq_mul]
    exact commute_of_mem_zpowers hg htm
  have hwm : w ^ m = 1 := by
    have h := hconj m
    rw [htmg] at h
    exact (mul_eq_right.1 h.symm)
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm3
  have hw1 : w = 1 := by
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hw3)
      (orderOf_dvd_of_pow_eq_one hwm)
  have : g * t * g⁻¹ * t⁻¹ = 1 := hw1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
  exact this

theorem centralizer_le_of_layer_core {a' : G} (hx3 : x ^ 3 = 1)
    (hxD : x ∈ layerOf x)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (layerOf x : Set G),
      (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x)
    (ha'C : a' * x = x * a') (ha'3 : a' ^ 3 = 1)
    (hM1 : a' ∉ layerOf x ⊔ torusOf x → ∀ g' ∈ Subgroup.centralizer ({x} : Set G),
      ∃ k : ℕ, g' * a' ^ k ∈ layerOf x ⊔ torusOf x)
    (hM2 : a' ∈ layerOf x → ∀ g ∈ Subgroup.centralizer ({x} : Set G),
      ∃ h ∈ layerOf x, h * a' * h⁻¹ = g * a' * g⁻¹)
    {Γ : Subgroup G} (hDΓ : layerOf x ≤ Γ)
    (hΓ : ∀ l ∈ Subgroup.centralizer ({x} : Set G), l * a' = a' * l → l ∈ Γ) :
    Subgroup.centralizer ({x} : Set G) ≤ Γ := by
  have ha'cen : a' ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 ha'C
  have hTΓ : torusOf x ≤ Γ := fun t ht =>
    hΓ t ht.1 (torus_central hx3 hZD hZ3 ha'cen ht).symm
  have ha'Γ : a' ∈ Γ := hΓ a' ha'cen rfl
  by_cases hmem : a' ∈ layerOf x ⊔ torusOf x
  ·
    have hcomm : ∀ r ∈ layerOf x, ∀ t ∈ torusOf x, r * t = t * r := fun r hr t ht =>
      Subgroup.mem_centralizer_iff.1 ht.2 r hr
    obtain ⟨r, hr, t, ht, hrt⟩ := exists_mul_of_mem_sup hcomm hmem
    have hrt' : Commute r t := hcomm r hr t ht
    have ht3 : t ^ 3 = (r ^ 3)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← hrt'.mul_pow, hrt, ha'3]
    have ht3D : t ^ 3 ∈ layerOf x := by
      rw [ht3]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hr 3)
    have ht3cen : t ^ 3 ∈ Subgroup.centralizer (layerOf x : Set G) :=
      Subgroup.pow_mem _ ht.2 3
    have ht3x : t ^ 3 ∈ Subgroup.zpowers x :=
      hZD _ ht3D fun d hd => (Subgroup.mem_centralizer_iff.1 ht3cen d hd).symm
    have ht9 : t ^ (3 ^ 2) = 1 := by
      have h3 : (t ^ 3) ^ 3 = 1 := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ht3x
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
      rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul]
      exact h3
    have htx : t ∈ Subgroup.zpowers x := hZ3 t ht.2 ⟨2, ht9⟩
    have htD : t ∈ layerOf x := (Subgroup.zpowers_le.2 hxD) htx
    have ha'D : a' ∈ layerOf x := by
      rw [← hrt]; exact Subgroup.mul_mem _ hr htD
    intro g hg
    obtain ⟨h, hh, hconj⟩ := hM2 ha'D g hg
    have hhC : h ∈ Subgroup.centralizer ({x} : Set G) := layerOf_le_centralizer x hh
    have hl : h⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hhC) hg
    have e : g * a' = h * a' * h⁻¹ * g := by rw [hconj]; group
    have key : h⁻¹ * g * a' = a' * (h⁻¹ * g) := by
      calc h⁻¹ * g * a' = h⁻¹ * (g * a') := by group
        _ = h⁻¹ * (h * a' * h⁻¹ * g) := by rw [e]
        _ = a' * (h⁻¹ * g) := by group
    have := Γ.mul_mem (hDΓ hh) (hΓ _ hl key)
    simpa using this
  · intro g' hg'
    obtain ⟨k, hk⟩ := hM1 hmem g' hg'
    have hk' : g' * a' ^ k ∈ Γ := sup_le hDΓ hTΓ hk
    have := Γ.mul_mem hk' (Γ.inv_mem (Γ.pow_mem ha'Γ k))
    simpa using this

theorem centralizer_le_of_layer {a' : G} (hx3 : x ^ 3 = 1)
    (hxD : x ∈ layerOf x)
    (hZD : ∀ w ∈ layerOf x, (∀ d ∈ layerOf x, w * d = d * w) → w ∈ Subgroup.zpowers x)
    (hZ3 : ∀ z ∈ Subgroup.centralizer (layerOf x : Set G),
      (∃ k : ℕ, z ^ (3 ^ k) = 1) → z ∈ Subgroup.zpowers x)
    (ha'C : a' * x = x * a') (ha'3 : a' ^ 3 = 1) (ha'x : a' ∉ Subgroup.zpowers x)
    (hM1 : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∉ layerOf x ⊔ torusOf x →
      ∀ g' ∈ Subgroup.centralizer ({x} : Set G), ∃ k : ℕ, g' * g ^ k ∈ layerOf x ⊔ torusOf x)
    (hM2 : ∀ s ∈ layerOf x, s ^ 3 = 1 → s ∉ Subgroup.zpowers x →
      ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∃ h ∈ layerOf x, h * s * h⁻¹ = g * s * g⁻¹)
    {Γ : Subgroup G} (hDΓ : layerOf x ≤ Γ)
    (hΓ : ∀ l ∈ Subgroup.centralizer ({x} : Set G), l * a' = a' * l → l ∈ Γ) :
    Subgroup.centralizer ({x} : Set G) ≤ Γ := by
  have ha'cen : a' ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 ha'C
  exact centralizer_le_of_layer_core hx3 hxD hZD hZ3 ha'C ha'3 (hM1 a' ha'cen)
    (fun ha'D => hM2 a' ha'D ha'3 ha'x) hDΓ hΓ

end Layer

end CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TOdd
