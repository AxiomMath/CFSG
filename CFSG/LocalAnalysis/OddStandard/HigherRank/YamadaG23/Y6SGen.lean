module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

theorem y6_card_eq_two_mul_cent [Finite G] {Y : Subgroup G} {t s : G} (hst : s ≠ t)
    (hY : ∀ y ∈ Y, y * t * y⁻¹ = t ∨ y * t * y⁻¹ = s) {y₀ : G} (hy₀ : y₀ ∈ Y)
    (hy₀t : y₀ * t * y₀⁻¹ = s) :
    Nat.card ↥Y = 2 * Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) := by
  set C : Subgroup G := Y ⊓ centralizer ({t} : Set G) with hC
  have hCY : C ≤ Y := by rw [hC]; exact inf_le_left
  have hmemC : ∀ b ∈ Y, (b ∈ C ↔ b * t * b⁻¹ = t) := by
    intro b hb
    simp only [hC, mem_inf, mem_centralizer_singleton_iff, hb, true_and]
    constructor
    · intro h
      rw [h]
      group
    · intro h
      calc b * t = b * t * b⁻¹ * b := by group
        _ = t * b := by rw [h]
  have hCpair : ∀ b ∈ Y, Xor (b * y₀ ∈ C) (b ∈ C) := by
    intro b hb
    have hby : b * y₀ ∈ Y := Y.mul_mem hb hy₀
    have hbs : b * s * b⁻¹ = t ∨ b * s * b⁻¹ = s := by
      have h := hY (b * y₀) hby
      rwa [show (b * y₀) * t * (b * y₀)⁻¹ = b * s * b⁻¹ by
        rw [← hy₀t]; group] at h
    have hbt : b * t * b⁻¹ = t ∨ b * t * b⁻¹ = s := hY b hb
    have hxor : Xor (b * s * b⁻¹ = t) (b * t * b⁻¹ = t) := by
      rcases hbt with hbt | hbt
      · have hbss : b * s * b⁻¹ = s := by
          rcases hbs with hbs | hbs
          · exfalso
            have hcomm : b * t = t * b := by
              calc b * t = b * t * b⁻¹ * b := by group
                _ = t * b := by rw [hbt]
            have hbt' : b⁻¹ * t * b = t := by
              calc b⁻¹ * t * b = b⁻¹ * (t * b) := by group
                _ = b⁻¹ * (b * t) := by rw [← hcomm]
                _ = t := by group
            have hst' : s = t := by
              calc s = b⁻¹ * (b * s * b⁻¹) * b := by group
                _ = b⁻¹ * t * b := by rw [hbs]
                _ = t := hbt'
            exact hst hst'
          · exact hbs
        exact Or.inr ⟨hbt, fun h => hst (hbss.symm.trans h)⟩
      · have hbst : b * s * b⁻¹ = t := by
          rcases hbs with hbs | hbs
          · exact hbs
          · exfalso
            have ht : t = b⁻¹ * s * b := by
              calc t = b⁻¹ * (b * t * b⁻¹) * b := by group
                _ = b⁻¹ * s * b := by rw [hbt]
            have hs : s = b⁻¹ * s * b := by
              calc s = b⁻¹ * (b * s * b⁻¹) * b := by group
                _ = b⁻¹ * s * b := by rw [hbs]
            exact hst (hs.trans ht.symm)
        exact Or.inl ⟨hbst, fun h => hst (hbt.symm.trans h)⟩
    have hmemby : (b * y₀ ∈ C) ↔ (b * s * b⁻¹ = t) := by
      rw [hmemC (b * y₀) hby]
      rw [show (b * y₀) * t * (b * y₀)⁻¹ = b * s * b⁻¹ by rw [← hy₀t]; group]
    rw [hmemby, hmemC b hb]
    exact hxor
  have hrel : C.relIndex Y = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    exact ⟨y₀, hy₀, fun b hb => hCpair b hb⟩
  have hmul := Subgroup.relIndex_mul_card (H := C) (K := Y)
  rw [hrel, inf_of_le_left hCY] at hmul
  exact hmul.symm

theorem y6_orbitMod_trans {T Z : Subgroup G} (hTZ : T ≤ normalizer (Z : Set G)) {O : Set G}
    (hO : IsOrbitMod T Z O) {u v : G} (hu : u ∈ O) (hv : v ∈ O) :
    ∃ k ∈ T, (k * u * k⁻¹)⁻¹ * v ∈ Z := by
  obtain ⟨u₀, -, rfl⟩ := hO
  rw [orbitMod] at hu hv
  obtain ⟨k₁, hk₁, hz₁⟩ := hu
  obtain ⟨k₂, hk₂, hz₂⟩ := hv
  refine ⟨k₂ * k₁⁻¹, T.mul_mem hk₂ (T.inv_mem hk₁), ?_⟩
  have hu_eq : u = (k₁ * u₀ * k₁⁻¹) * ((k₁ * u₀ * k₁⁻¹)⁻¹ * u) := by group
  have hv_eq : v = (k₂ * u₀ * k₂⁻¹) * ((k₂ * u₀ * k₂⁻¹)⁻¹ * v) := by group
  have hz₁' : (k₂ * k₁⁻¹) * ((k₁ * u₀ * k₁⁻¹)⁻¹ * u) * (k₂ * k₁⁻¹)⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp
      (hTZ (T.mul_mem hk₂ (T.inv_mem hk₁))) ((k₁ * u₀ * k₁⁻¹)⁻¹ * u)).mp hz₁
  have heq : ((k₂ * k₁⁻¹) * u * (k₂ * k₁⁻¹)⁻¹)⁻¹ * v =
      ((k₂ * k₁⁻¹) * ((k₁ * u₀ * k₁⁻¹)⁻¹ * u) * (k₂ * k₁⁻¹)⁻¹)⁻¹ *
        ((k₂ * u₀ * k₂⁻¹)⁻¹ * v) := by
    rw [hu_eq, hv_eq]
    group
  rw [heq]
  exact Z.mul_mem (Z.inv_mem hz₁') hz₂

theorem y6_order_six {X K Y C1 : Subgroup G} (ψ : ↥X →* Equiv.Perm (Fin 6))
    (hker : ψ.ker = K.subgroupOf X) (hKY : K ⊓ Y = C1) (hYX : Y ≤ X) {y : G} (hy : y ∈ Y)
    (h6 : y ^ 6 ∈ C1) (h2 : y ^ 2 ∉ C1) (h3 : y ^ 3 ∉ C1) :
    ∃ x : ↥X, (x : G) ∈ Y ∧ orderOf (ψ x) = 6 := by
  refine ⟨⟨y, hYX hy⟩, hy, ?_⟩
  set x : ↥X := ⟨y, hYX hy⟩ with hxdef
  have hxcoe : (x : G) = y := by rw [hxdef]
  have hmem : ∀ n : ℕ, (ψ x) ^ n = 1 ↔ y ^ n ∈ C1 := by
    intro n
    have hcoe : ((x ^ n : ↥X) : G) = y ^ n := by
      rw [SubmonoidClass.coe_pow, hxcoe]
    rw [← map_pow, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, hcoe]
    constructor
    · intro hk
      rw [← hKY]
      exact ⟨hk, Y.pow_mem hy n⟩
    · intro h
      rw [← hKY] at h
      exact h.1
  rw [orderOf_eq_iff (by norm_num : 0 < 6)]
  refine ⟨(hmem 6).mpr h6, ?_⟩
  intro m hm6 hm0
  simp only [ne_eq, hmem m]
  interval_cases m
  · intro hy1
    exact h2 (by simpa [pow_one, pow_two] using C1.mul_mem hy1 hy1)
  · exact h2
  · exact h3
  · intro hy4
    have heq : y ^ 2 = y ^ 6 * (y ^ 4)⁻¹ := by group
    exact h2 (by rw [heq]; exact C1.mul_mem h6 (C1.inv_mem hy4))
  · intro hy5
    have hy1 : y ∈ C1 := by
      have heq : y = y ^ 6 * (y ^ 5)⁻¹ := by group
      rw [heq]
      exact C1.mul_mem h6 (C1.inv_mem hy5)
    exact h2 (by simpa [pow_two] using C1.mul_mem hy1 hy1)

private lemma conj_mem_centralizerSection {K M : Subgroup G} {c x : G}
    (hcK : c ∈ normalizer (K : Set G)) (hcM : c ∈ normalizer (M : Set G))
    (hx : x ∈ CFSG.GH74.GLS.centralizerSection K M) :
    c * x * c⁻¹ ∈ CFSG.GH74.GLS.centralizerSection K M := by
  obtain ⟨hxK, hxM, hx⟩ := hx
  refine ⟨?_, ?_, fun k hk => ?_⟩
  · exact mul_mem (mul_mem hcK hxK) (inv_mem hcK)
  · exact mul_mem (mul_mem hcM hxM) (inv_mem hcM)
  · have hk' : c⁻¹ * k * c ∈ K := (Subgroup.mem_normalizer_iff''.mp hcK k).mp hk
    have hcomm : ⁅c⁻¹ * k * c, x⁆ ∈ M := hx (c⁻¹ * k * c) hk'
    have hconj : c * ⁅c⁻¹ * k * c, x⁆ * c⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp hcM (⁅c⁻¹ * k * c, x⁆)).mp hcomm
    rw [show ⁅k, c * x * c⁻¹⁆ = c * ⁅c⁻¹ * k * c, x⁆ * c⁻¹ by
      rw [conjugate_commutatorElement]
      congr 1
      group]
    exact hconj

theorem y6_centSec_normal {K M N : Subgroup G} (hNK : N ≤ normalizer (K : Set G))
    (hNM : N ≤ normalizer (M : Set G)) :
    ((CFSG.GH74.GLS.centralizerSection K M).subgroupOf N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using conj_mem_centralizerSection (hNK g.2) (hNM g.2) hn

end CFSG.OddStandard.HigherRank.YamadaG23
